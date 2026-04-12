// CodeIntegrityReflection
//
// Cross-function integrity reflection. For each checker function F we
// insert a CRC32 check over 1-N target functions G_i. If any G_i is
// patched, its CRC changes, F's check fails, process dies.
//
// Key design points vs. a plain checksum loop:
//
//  * CRC32 via the ARMv8 `crc32w` hardware instruction
//    (llvm.aarch64.crc32w). Much harder to forge than XOR — an
//    attacker can no longer flip two bytes to restore the hash; they
//    must solve a polynomial residue problem.
//
//  * Per-target expected-hash GV AND per-target function-size GV, both
//    emitted as zero placeholders into dedicated sections. A post-link
//    tool parses the binary, computes CRC32 over each target's .text
//    bytes, and patches both GVs.
//
//  * Per-function manifest entry — an opaque struct
//    {func_ptr, size_gv_ptr, hash_gv_ptr} emitted into .cir_manifest.
//    Lets the post-link tool walk a single array and fill everything
//    it needs without guessing from names.
//
//  * Criticality-weighted graph. Functions annotated with
//    `cir_critical` get prioritized as check targets; each checker
//    biases its picks toward them so critical code gets more
//    redundant coverage. Annotation `cir_checker` makes a function an
//    active checker regardless of the global flag.
//
// ARM64 only, requires +crc (standard on ARMv8.1+).

#include "llvm/Transforms/Obfuscation/CodeIntegrityReflection.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicsAArch64.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <algorithm>
#include <cstdio>
#include <vector>

using namespace llvm;

static cl::opt<uint32_t>
    CIRProbability("cir_prob", cl::init(100), cl::NotHidden,
                   cl::desc("CIR checker-enablement probability 0-100"));

static cl::opt<uint32_t>
    CIRFanout("cir_fanout", cl::init(3), cl::NotHidden,
              cl::desc("Base number of targets each checker verifies"));

static cl::opt<uint32_t>
    CIRCriticalBoost("cir_critical_boost", cl::init(3), cl::NotHidden,
                     cl::desc("Extra fanout added when checker is critical"));

static cl::opt<uint32_t>
    CIRCriticalBias("cir_critical_bias", cl::init(70), cl::NotHidden,
                    cl::desc("Percent chance each target-pick prefers a critical function"));

namespace {

enum Criticality { C_Low = 0, C_Medium = 1, C_High = 2 };

struct FuncInfo {
  Function *F;
  Criticality crit;
};

struct CodeIntegrityReflection : public ModulePass {
  static char ID;
  bool flag;

  CodeIntegrityReflection() : ModulePass(ID), flag(true) {}
  CodeIntegrityReflection(bool flag) : ModulePass(ID), flag(flag) {}

  bool runOnModule(Module &M) override;
  StringRef getPassName() const override {
    return "CodeIntegrityReflection";
  }

private:
  Criticality classify(Function &F);
  bool isEligibleChecker(Function &F);
  bool isEligibleTarget(Function &F);
  Function *pickTarget(const std::vector<FuncInfo> &pool, Function *self,
                       bool preferCritical);
  bool insertCheck(Function &Checker, Function &Target,
                   GlobalVariable *ManifestArr, std::vector<Constant *> &manifest);
  static std::string randomName(const char *prefix);

  // Cached intrinsic decl across all checks in one module run.
  Function *Crc32WFn = nullptr;
  Function *TrapFn = nullptr;
};

} // namespace

char CodeIntegrityReflection::ID = 0;

std::string CodeIntegrityReflection::randomName(const char *prefix) {
  char buf[64];
  std::snprintf(buf, sizeof(buf), "%s_%08x%08x", prefix,
                (unsigned)cryptoutils->get_uint32_t(),
                (unsigned)cryptoutils->get_uint32_t());
  return std::string(buf);
}

Criticality CodeIntegrityReflection::classify(Function &F) {
  if (readAnnotationMetadata(&F, "cir_critical"))
    return C_High;
  if (readAnnotationMetadata(&F, "cir_low"))
    return C_Low;
  // Heuristic: very small functions are poor targets (less material to
  // hash, easier to hand-verify). Bump them down one tier.
  unsigned insnCount = 0;
  for (BasicBlock &BB : F)
    insnCount += BB.size();
  if (insnCount < 16)
    return C_Low;
  return C_Medium;
}

bool CodeIntegrityReflection::isEligibleChecker(Function &F) {
  if (F.isDeclaration() || F.hasAvailableExternallyLinkage())
    return false;
  if (F.hasFnAttribute(Attribute::Naked) ||
      F.hasFnAttribute(Attribute::ReturnsTwice))
    return false;
  if (F.hasFnAttribute("no-cir"))
    return false;
  StringRef n = F.getName();
  if (n.starts_with("llvm.") || n.starts_with("__cxx_") ||
      n.starts_with("__cir_"))
    return false;
  return true;
}

bool CodeIntegrityReflection::isEligibleTarget(Function &F) {
  if (!isEligibleChecker(F))
    return false;
  // Targets must have some body to measure.
  unsigned insnCount = 0;
  for (BasicBlock &BB : F)
    insnCount += BB.size();
  return insnCount >= 4;
}

Function *CodeIntegrityReflection::pickTarget(
    const std::vector<FuncInfo> &pool, Function *self, bool preferCritical) {
  if (pool.empty())
    return nullptr;

  if (preferCritical) {
    // Build critical-only slice on the fly.
    std::vector<Function *> crit;
    for (const auto &fi : pool)
      if (fi.crit == C_High && fi.F != self)
        crit.push_back(fi.F);
    if (!crit.empty())
      return crit[cryptoutils->get_uint32_t() % crit.size()];
    // Fall through to unbiased pick if no critical functions exist.
  }

  for (int tries = 0; tries < 12; ++tries) {
    const FuncInfo &fi =
        pool[cryptoutils->get_uint32_t() % pool.size()];
    if (fi.F != self)
      return fi.F;
  }
  return nullptr;
}

bool CodeIntegrityReflection::insertCheck(Function &Checker, Function &Target,
                                          GlobalVariable * /*unused*/,
                                          std::vector<Constant *> &manifest) {
  LLVMContext &Ctx = Checker.getContext();
  Module *M = Checker.getParent();
  Type *I64Ty = Type::getInt64Ty(Ctx);
  Type *I32Ty = Type::getInt32Ty(Ctx);
  Type *PtrTy = PointerType::get(Ctx, 0);

  BasicBlock &EntryBB = Checker.getEntryBlock();
  Instruction *splitPt = &*EntryBB.getFirstInsertionPt();
  if (!splitPt || splitPt->isTerminator())
    return false;
  BasicBlock *contBB = EntryBB.splitBasicBlock(splitPt, "cir.cont");

  // Placeholder GVs — post-link tool fills them in.
  GlobalVariable *sizeGV = new GlobalVariable(
      *M, I32Ty, /*isConstant=*/false, GlobalValue::PrivateLinkage,
      ConstantInt::get(I32Ty, 0), randomName("__cir_size"));
  sizeGV->setSection(".cir_sizes");
  sizeGV->setAlignment(Align(4));
  appendToCompilerUsed(*M, {sizeGV});

  GlobalVariable *hashGV = new GlobalVariable(
      *M, I32Ty, /*isConstant=*/false, GlobalValue::PrivateLinkage,
      ConstantInt::get(I32Ty, 0), randomName("__cir_hash"));
  hashGV->setSection(".cir_hashes");
  hashGV->setAlignment(Align(4));
  appendToCompilerUsed(*M, {hashGV});

  // Manifest entry (3 pointers per check). With opaque pointers these
  // already have the canonical ptr type — no bitcast needed.
  (void)PtrTy;
  manifest.push_back(&Target);
  manifest.push_back(sizeGV);
  manifest.push_back(hashGV);

  // ────── Build the check ──────
  Constant *funcAddr = ConstantExpr::getPtrToInt(&Target, I64Ty);

  BasicBlock *preBB =
      BasicBlock::Create(Ctx, "cir.pre", &Checker, contBB);
  BasicBlock *loopHdr = BasicBlock::Create(Ctx, "cir.loop", &Checker, contBB);
  BasicBlock *loopBody = BasicBlock::Create(Ctx, "cir.body", &Checker, contBB);
  BasicBlock *checkBB = BasicBlock::Create(Ctx, "cir.check", &Checker, contBB);
  BasicBlock *dieBB = BasicBlock::Create(Ctx, "cir.die", &Checker, contBB);

  // Redirect EntryBB's terminator (splitBasicBlock inserted a br to
  // contBB) to our pre-setup block.
  EntryBB.getTerminator()->eraseFromParent();
  BranchInst::Create(preBB, &EntryBB);

  // cir.pre: load size, compute end. If size == 0, skip to contBB —
  // allows fail-open on unpatched debug builds at the operator's
  // discretion via an env-controlled post-link tool.
  IRBuilder<> pb(preBB);
  LoadInst *sizeLd =
      pb.CreateAlignedLoad(I32Ty, sizeGV, Align(4), /*isVolatile=*/true);
  Value *sizeZ = pb.CreateZExt(sizeLd, I64Ty);
  Value *endAddr = pb.CreateAdd(funcAddr, sizeZ);
  Value *zeroSize = pb.CreateICmpEQ(sizeLd, ConstantInt::get(I32Ty, 0));
  pb.CreateCondBr(zeroSize, contBB, loopHdr);

  // cir.loop: PHI (cur_addr, acc), test cur_addr < end.
  IRBuilder<> hb(loopHdr);
  PHINode *iPhi = hb.CreatePHI(I64Ty, 2, "cir.i");
  // Initial CRC32 seed: 0xFFFFFFFF (standard CRC32).
  PHINode *accPhi = hb.CreatePHI(I32Ty, 2, "cir.acc");
  iPhi->addIncoming(funcAddr, preBB);
  accPhi->addIncoming(ConstantInt::get(I32Ty, 0xFFFFFFFFu), preBB);
  Value *done = hb.CreateICmpUGE(iPhi, endAddr);
  hb.CreateCondBr(done, checkBB, loopBody);

  // cir.body: load 4 bytes, fold into CRC via llvm.aarch64.crc32w.
  IRBuilder<> bb(loopBody);
  Value *curPtr = bb.CreateIntToPtr(iPhi, PtrTy);
  LoadInst *word =
      bb.CreateAlignedLoad(I32Ty, curPtr, Align(4), /*isVolatile=*/true);
  Value *newAcc = bb.CreateCall(Crc32WFn, {accPhi, word});
  Value *nextI = bb.CreateAdd(iPhi, ConstantInt::get(I64Ty, 4));
  bb.CreateBr(loopHdr);
  iPhi->addIncoming(nextI, loopBody);
  accPhi->addIncoming(newAcc, loopBody);

  // cir.check: final CRC xor 0xFFFFFFFF (standard CRC32 finalization
  // — the crc32w instruction does NOT do this implicitly). Compare
  // with the expected value from hashGV.
  IRBuilder<> cb(checkBB);
  Value *finalHash =
      cb.CreateXor(accPhi, ConstantInt::get(I32Ty, 0xFFFFFFFFu));
  LoadInst *expected = cb.CreateAlignedLoad(I32Ty, hashGV, Align(4),
                                             /*isVolatile=*/true);
  Value *match = cb.CreateICmpEQ(finalHash, expected);
  cb.CreateCondBr(match, contBB, dieBB);

  // cir.die: kill(getpid(), SIGKILL) then trap.
  IRBuilder<> db(dieBB);
  FunctionType *AsmFTy = FunctionType::get(Type::getVoidTy(Ctx), false);
  InlineAsm *killAsm = InlineAsm::get(
      AsmFTy,
      "mov x8, #172\n\tsvc #0\n\tmov w1, #9\n\tmov x8, #129\n\tsvc #0\n\t",
      "~{x0},~{x1},~{x8},~{memory}",
      /*hasSideEffects=*/true);
  db.CreateCall(killAsm);
  db.CreateCall(TrapFn);
  db.CreateUnreachable();

  // Ensure the checker function is compiled with +crc so crc32w is
  // available. On ARMv8.1+ this is default but older cores need the
  // explicit feature.
  Checker.addFnAttr("target-features", "+crc");
  return true;
}

bool CodeIntegrityReflection::runOnModule(Module &M) {
  if (!flag)
    return false;

  Triple T(M.getTargetTriple());
  if (!T.isAArch64())
    return false;

  // Classify every function once up front.
  std::vector<FuncInfo> all;
  all.reserve(M.size());
  for (Function &F : M) {
    if (!isEligibleTarget(F))
      continue;
    all.push_back({&F, classify(F)});
  }
  if (all.size() < 2)
    return false;

  // Prepare intrinsic declarations once.
  Crc32WFn =
      Intrinsic::getDeclaration(&M, Intrinsic::aarch64_crc32w);
  TrapFn = Intrinsic::getDeclaration(&M, Intrinsic::trap);

  LLVMContext &Ctx = M.getContext();
  Type *PtrTy = PointerType::get(Ctx, 0);

  std::vector<Constant *> manifest;
  bool changed = false;

  for (Function &F : M) {
    if (!isEligibleChecker(F))
      continue;

    bool explicitChecker = readAnnotationMetadata(&F, "cir_checker");
    uint32_t prob = CIRProbability;
    toObfuscateUint32Option(&F, "cir_prob", &prob);
    if (prob > 100)
      prob = 100;

    if (!explicitChecker) {
      if (!toObfuscate(flag, &F, "cir"))
        continue;
      if ((cryptoutils->get_uint32_t() % 100) >= prob)
        continue;
    }

    uint32_t fanout = CIRFanout;
    toObfuscateUint32Option(&F, "cir_fanout", &fanout);
    if (classify(F) == C_High)
      fanout += CIRCriticalBoost;
    if (fanout == 0)
      fanout = 1;
    if (fanout > 16)
      fanout = 16;

    uint32_t bias = CIRCriticalBias;
    if (bias > 100)
      bias = 100;

    for (uint32_t n = 0; n < fanout; ++n) {
      bool preferCritical = (cryptoutils->get_uint32_t() % 100) < bias;
      Function *G = pickTarget(all, &F, preferCritical);
      if (!G)
        continue;
      changed |= insertCheck(F, *G, nullptr, manifest);
    }
  }

  // Emit the manifest: an array of ptrs, zero-terminated triple. The
  // post-link tool walks it three-at-a-time until a null `func_ptr`.
  if (!manifest.empty()) {
    manifest.push_back(Constant::getNullValue(PtrTy));
    manifest.push_back(Constant::getNullValue(PtrTy));
    manifest.push_back(Constant::getNullValue(PtrTy));
    // Per-TU manifest: PrivateLinkage + explicit .cir_manifest section.
    // The ELF linker concatenates contributions from each object file
    // into one monolithic `.cir_manifest` section in the final binary,
    // which the post-link tool walks three-pointers-at-a-time.
    ArrayType *AT = ArrayType::get(PtrTy, manifest.size());
    Constant *init = ConstantArray::get(AT, manifest);
    auto *GV = new GlobalVariable(M, AT, /*isConstant=*/false,
                                   GlobalValue::PrivateLinkage, init,
                                   randomName("__cir_manifest"));
    GV->setSection(".cir_manifest");
    GV->setAlignment(Align(8));
    appendToCompilerUsed(M, {GV});
  }

  return changed;
}

ModulePass *llvm::createCodeIntegrityReflectionPass(bool flag) {
  return new CodeIntegrityReflection(flag);
}

INITIALIZE_PASS(CodeIntegrityReflection, "cir",
                "CRC32-based cross-function integrity reflection", false,
                false)
