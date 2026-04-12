// InstructionLevelAntiPatching
//
// Inserts inline integrity-check blocks into ARM64 functions. Each check
// XOR-sums the 4-byte instruction words from the function start up to the
// check point, then compares the result against a value held in a
// per-check GlobalVariable. If the comparison fails, the process traps.
//
// The expected-value GV is emitted with an initializer of 0 and placed in
// a dedicated section (.iap_expected). A post-link tool is expected to
// disassemble the produced binary, compute the XOR sum for each marker,
// and patch the GV with the real expected value before shipping. Until
// such a tool runs, checks will always fail — which is intentional: a
// shipped binary with uninitialized expected values is a build error.
//
// The check code itself is placed AFTER the measured region so that it
// does not include itself in the XOR.

#include "llvm/Transforms/Obfuscation/InstructionLevelAntiPatching.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <cstdio>
#include <vector>

using namespace llvm;

static cl::opt<uint32_t>
    IAPProbability("iap_prob", cl::init(100), cl::NotHidden,
                   cl::desc("IAP probability per function (0-100)"));

static cl::opt<uint32_t>
    IAPInterval("iap_interval", cl::init(80), cl::NotHidden,
                cl::desc("Minimum instruction count between IAP checks"));

static cl::opt<uint32_t>
    IAPMaxChecks("iap_max_checks", cl::init(3), cl::NotHidden,
                 cl::desc("Upper bound on IAP checks per function"));

namespace {

struct InstructionLevelAntiPatching : public FunctionPass {
  static char ID;
  bool flag;

  InstructionLevelAntiPatching() : FunctionPass(ID), flag(true) {}
  InstructionLevelAntiPatching(bool flag) : FunctionPass(ID), flag(flag) {}

  bool runOnFunction(Function &F) override;

  StringRef getPassName() const override {
    return "InstructionLevelAntiPatching";
  }

private:
  bool insertCheck(Function &F, BasicBlock *splitBefore);
  GlobalVariable *makeExpectedGV(Module &M, Type *I32Ty);
  static std::string randomName(const char *prefix);
};

} // namespace

char InstructionLevelAntiPatching::ID = 0;

std::string InstructionLevelAntiPatching::randomName(const char *prefix) {
  char buf[48];
  std::snprintf(buf, sizeof(buf), "%s_%08x%08x", prefix,
                (unsigned)cryptoutils->get_uint32_t(),
                (unsigned)cryptoutils->get_uint32_t());
  return std::string(buf);
}

GlobalVariable *
InstructionLevelAntiPatching::makeExpectedGV(Module &M, Type *I32Ty) {
  GlobalVariable *GV = new GlobalVariable(
      M, I32Ty, /*isConstant=*/false, GlobalValue::PrivateLinkage,
      ConstantInt::get(I32Ty, 0), randomName("iap.expected"));
  GV->setSection(".iap_expected");
  GV->setAlignment(Align(4));
  appendToCompilerUsed(M, {GV});
  return GV;
}

bool InstructionLevelAntiPatching::runOnFunction(Function &F) {
  if (!toObfuscate(flag, &F, "iap"))
    return false;
  if (F.isDeclaration())
    return false;
  if (F.hasFnAttribute(Attribute::Naked) ||
      F.hasFnAttribute(Attribute::ReturnsTwice))
    return false;
  if (F.hasFnAttribute("no-iap"))
    return false;

  Module *M = F.getParent();
  Triple T(M->getTargetTriple());
  if (!T.isAArch64())
    return false;

  uint32_t prob = IAPProbability;
  toObfuscateUint32Option(&F, "iap_prob", &prob);
  if (prob > 100)
    prob = 100;
  if ((cryptoutils->get_uint32_t() % 100) >= prob)
    return false;

  uint32_t interval = IAPInterval;
  toObfuscateUint32Option(&F, "iap_interval", &interval);
  if (interval < 16)
    interval = 16;

  uint32_t maxChecks = IAPMaxChecks;
  toObfuscateUint32Option(&F, "iap_max_checks", &maxChecks);
  if (maxChecks == 0)
    return false;
  if (maxChecks > 8)
    maxChecks = 8;

  // Gather candidate split points. We skip PHIs, landingpads, and any
  // instruction with a token type — those can't be split across blocks.
  std::vector<Instruction *> points;
  uint32_t counter = 0;
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      if (I.isTerminator())
        continue;
      if (isa<PHINode>(I) || isa<LandingPadInst>(I))
        continue;
      if (I.getType()->isTokenTy())
        continue;
      if (counter++ % interval != 0)
        continue;
      // Don't split right at entry — we want at least one original
      // instruction in the prologue to measure.
      if (&BB == &F.getEntryBlock() && BB.getFirstNonPHI() == &I)
        continue;
      points.push_back(&I);
      if (points.size() >= maxChecks)
        break;
    }
    if (points.size() >= maxChecks)
      break;
  }

  if (points.empty())
    return false;

  bool changed = false;
  for (Instruction *I : points) {
    BasicBlock *parent = I->getParent();
    BasicBlock *contBB = parent->splitBasicBlock(I, "iap.cont");

    LLVMContext &Ctx = F.getContext();
    Type *I64Ty = Type::getInt64Ty(Ctx);
    Type *I32Ty = Type::getInt32Ty(Ctx);
    Type *PtrTy = PointerType::get(Ctx, 0);

    Constant *funcAddr = ConstantExpr::getPtrToInt(&F, I64Ty);
    Constant *pcAddr =
        ConstantExpr::getPtrToInt(BlockAddress::get(&F, contBB), I64Ty);

    GlobalVariable *expectedGV = makeExpectedGV(*M, I32Ty);

    BasicBlock *loopHdr = BasicBlock::Create(Ctx, "iap.loop", &F, contBB);
    BasicBlock *loopBody = BasicBlock::Create(Ctx, "iap.body", &F, contBB);
    BasicBlock *checkBB = BasicBlock::Create(Ctx, "iap.check", &F, contBB);
    BasicBlock *dieBB = BasicBlock::Create(Ctx, "iap.die", &F, contBB);

    // Redirect the unconditional branch splitBasicBlock inserted.
    Instruction *oldTerm = parent->getTerminator();
    oldTerm->eraseFromParent();
    BranchInst::Create(loopHdr, parent);

    // Loop header: PHI for current byte pointer and XOR accumulator.
    IRBuilder<> hb(loopHdr);
    PHINode *iPhi = hb.CreatePHI(I64Ty, 2, "iap.i");
    PHINode *accPhi = hb.CreatePHI(I32Ty, 2, "iap.acc");
    iPhi->addIncoming(funcAddr, parent);
    accPhi->addIncoming(ConstantInt::get(I32Ty, 0), parent);
    Value *done = hb.CreateICmpUGE(iPhi, pcAddr);
    hb.CreateCondBr(done, checkBB, loopBody);

    // Loop body: load one 4-byte word, xor it in, advance pointer.
    IRBuilder<> bb(loopBody);
    Value *curPtr = bb.CreateIntToPtr(iPhi, PtrTy);
    LoadInst *word =
        bb.CreateAlignedLoad(I32Ty, curPtr, Align(4), /*isVolatile=*/true);
    Value *newAcc = bb.CreateXor(accPhi, word);
    Value *nextI = bb.CreateAdd(iPhi, ConstantInt::get(I64Ty, 4));
    bb.CreateBr(loopHdr);
    iPhi->addIncoming(nextI, loopBody);
    accPhi->addIncoming(newAcc, loopBody);

    // Check block: compare accumulator against expected value.
    IRBuilder<> cb(checkBB);
    LoadInst *expected = cb.CreateAlignedLoad(
        I32Ty, expectedGV, Align(4), /*isVolatile=*/true);
    Value *match = cb.CreateICmpEQ(accPhi, expected);
    cb.CreateCondBr(match, contBB, dieBB);

    // Die block: getpid() -> x0, then kill(pid, SIGKILL). Falls through
    // to llvm.trap() if the syscall somehow returns.
    IRBuilder<> db(dieBB);
    FunctionType *AsmFTy = FunctionType::get(Type::getVoidTy(Ctx), false);
    InlineAsm *killAsm = InlineAsm::get(
        AsmFTy,
        "mov x8, #172\n\t"  // SYS_getpid (ARM64 Linux)
        "svc #0\n\t"
        "mov w1, #9\n\t"    // SIGKILL
        "mov x8, #129\n\t"  // SYS_kill
        "svc #0\n\t",
        "~{x0},~{x1},~{x8},~{memory}",
        /*hasSideEffects=*/true);
    db.CreateCall(killAsm);
    Function *TrapFn =
        Intrinsic::getDeclaration(M, Intrinsic::trap);
    db.CreateCall(TrapFn);
    db.CreateUnreachable();

    changed = true;
  }

  return changed;
}

FunctionPass *llvm::createInstructionLevelAntiPatchingPass(bool flag) {
  return new InstructionLevelAntiPatching(flag);
}

INITIALIZE_PASS(InstructionLevelAntiPatching, "iap",
                "Instruction-level anti-patching integrity checks", false,
                false)
