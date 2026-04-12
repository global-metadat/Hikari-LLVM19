// ReturnAddressEncryption.cpp — Encrypt saved return addresses on the stack
//
// ARM64-only pass that XORs the saved LR (X30) on the stack frame with a
// per-function random key. Any stack unwinder, debugger, crash reporter,
// or backtrace-based hook sees garbage return addresses while the function
// is executing.
//
// Mechanism:
//   1. Force frame pointer so saved LR is always at [FP+8] (AArch64 ABI).
//   2. At function entry: load saved LR from [FP+8], XOR with key, store back.
//   3. Before each ret: load encrypted LR, XOR with key, store decrypted back.
//   4. Epilogue restores the correct LR and function returns normally.
//
// The per-function key lives in a PrivateLinkage GlobalVariable that
// ConstantEncryption can further protect in a later pass.
//
// Works best with -fno-unwind-tables (already set in AC's CMake).
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Obfuscation/ReturnAddressEncryption.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static cl::opt<unsigned> RetEncProb(
    "retenc_prob", cl::init(100), cl::NotHidden,
    cl::desc("Probability (0-100) of encrypting return address per function"));

static cl::opt<bool> RetEncClobberLR(
    "retenc_clobber_lr", cl::init(true), cl::NotHidden,
    cl::desc("Also clobber X30 register via inline asm after encrypting "
             "saved LR (breaks register-level debugger reads)"));

namespace {

// Find the first non-alloca, non-PHI instruction in the entry block.
// This is the safe insertion point after the prologue has set up the frame.
static Instruction *getEntryInsertPoint(Function &F) {
  BasicBlock &Entry = F.getEntryBlock();
  for (auto &I : Entry) {
    if (isa<AllocaInst>(&I))
      continue;
    if (isa<PHINode>(&I))
      continue;
    return &I;
  }
  return Entry.getTerminator();
}

// Generate a random name for the key GV to avoid pattern matching.
// Uses hex chars from cryptoutils, not the function name.
static std::string randomKeyName() {
  char buf[24];
  snprintf(buf, sizeof(buf), "rk_%08x%08x",
           cryptoutils->get_uint32_t(), cryptoutils->get_uint32_t());
  return std::string(buf);
}

struct ReturnAddressEncryption : public FunctionPass {
  static char ID;
  bool flag;

  ReturnAddressEncryption() : FunctionPass(ID), flag(true) {
    initializeReturnAddressEncryptionPass(*PassRegistry::getPassRegistry());
  }

  ReturnAddressEncryption(bool flag) : FunctionPass(ID), flag(flag) {
    initializeReturnAddressEncryptionPass(*PassRegistry::getPassRegistry());
  }

  StringRef getPassName() const override { return "ReturnAddressEncryption"; }

  bool runOnFunction(Function &F) override {
    if (!flag)
      return false;
    if (F.isDeclaration())
      return false;
    if (!toObfuscate(flag, &F, "retenc"))
      return false;

    // Per-function probability check
    unsigned prob = RetEncProb;
    toObfuscateUint32Option(&F, "retenc_prob", &prob);
    if (prob < 100 && cryptoutils->get_range(100) >= prob)
      return false;

    // Skip functions with special attributes that conflict
    if (F.hasFnAttribute(Attribute::Naked))
      return false;
    if (F.hasFnAttribute(Attribute::ReturnsTwice)) // setjmp
      return false;
    if (F.hasFnAttribute("thunk"))
      return false;

    // ARM64 only — the saved LR location is ABI-specific
    Module &M = *F.getParent();
    std::string Triple = M.getTargetTriple();
    bool isAArch64 = Triple.find("aarch64") != std::string::npos ||
                     Triple.find("arm64") != std::string::npos;
    if (!isAArch64)
      return false;

    // Must have at least one ret instruction
    SmallVector<ReturnInst *, 4> Rets;
    for (auto &BB : F)
      if (auto *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
        Rets.push_back(RI);
    if (Rets.empty())
      return false;

    errs() << "Running ReturnAddressEncryption On " << F.getName() << "\n";

    LLVMContext &Ctx = F.getContext();
    Type *I64Ty = Type::getInt64Ty(Ctx);
    Type *I8Ty = Type::getInt8Ty(Ctx);

    // ── Generate per-function random key ──
    uint64_t KeyVal = cryptoutils->get_uint64_t();
    // Avoid zero key (identity XOR = no encryption)
    if (KeyVal == 0)
      KeyVal = 0xA3B1C6D9E2F40857ULL;

    // Store key in a private global variable.
    // ConstantEncryption pass will further protect this if enabled.
    GlobalVariable *KeyGV = new GlobalVariable(
        M, I64Ty, /*isConstant=*/false, GlobalValue::PrivateLinkage,
        ConstantInt::get(I64Ty, KeyVal), randomKeyName());
    KeyGV->setAlignment(Align(8));

    // ── Force frame pointer ──
    // With frame-pointer=all, the backend emits:
    //   STP X29, X30, [SP, #-N]!
    //   MOV X29, SP
    // So saved LR is always at [X29+8] = [FP+8].
    // This overrides -fomit-frame-pointer for this function only.
    F.addFnAttr("frame-pointer", "all");

    // ── Get llvm.frameaddress intrinsic ──
    auto *PtrTy = PointerType::get(Ctx, 0);
    Function *FADecl =
        Intrinsic::getDeclaration(&M, Intrinsic::frameaddress, {PtrTy});

    // ── Encrypt saved LR at function entry ──
    Instruction *EntryPt = getEntryInsertPoint(F);
    IRBuilder<> EntryB(EntryPt);

    // Get frame pointer → saved LR is at FP+8
    Value *FP = EntryB.CreateCall(FADecl, {EntryB.getInt32(0)}, "retenc.fp");
    Value *LRPtr =
        EntryB.CreateGEP(I8Ty, FP, EntryB.getInt64(8), "retenc.lr.ptr");

    // Load key (volatile so LLVM can't constant-fold it away)
    LoadInst *KeyLoad = EntryB.CreateLoad(I64Ty, KeyGV, /*isVolatile=*/true,
                                          "retenc.key");

    // Load saved LR, XOR with key, store encrypted LR back
    LoadInst *LRLoad = EntryB.CreateLoad(I64Ty, LRPtr, "retenc.lr");
    Value *EncLR = EntryB.CreateXor(LRLoad, KeyLoad, "retenc.enc");
    EntryB.CreateStore(EncLR, LRPtr);

    // ── Optionally clobber X30 register via inline asm ──
    // After saving encrypted LR, X30 still holds the real return address.
    // Clobber it so a debugger reading registers also sees garbage.
    bool doClobber = RetEncClobberLR;
    toObfuscateBoolOption(&F, "retenc_clobber_lr", &doClobber);

    if (doClobber) {
      // XOR x30 with a random immediate via inline asm.
      // We use x16 as scratch (IP0, caller-saved, safe to clobber).
      // The clobbered x30 value doesn't matter — the epilogue will
      // restore x30 from the stack (where we just stored the encrypted LR,
      // which we decrypt before ret).
      auto *VoidTy = Type::getVoidTy(Ctx);
      auto *FTy = FunctionType::get(VoidTy, {I64Ty}, false);
      auto *ClobberAsm = InlineAsm::get(
          FTy,
          "eor x30, x30, $0",
          "r,~{x30}", /*hasSideEffects=*/true);
      // Use same key value for clobber (any value works, just needs to not be 0)
      EntryB.CreateCall(ClobberAsm, {KeyLoad});
    }

    // ── Decrypt saved LR before each ret ──
    for (ReturnInst *RI : Rets) {
      IRBuilder<> RetB(RI);

      Value *FP2 =
          RetB.CreateCall(FADecl, {RetB.getInt32(0)}, "retenc.fp.ret");
      Value *LRPtr2 =
          RetB.CreateGEP(I8Ty, FP2, RetB.getInt64(8), "retenc.lr.ptr.ret");

      LoadInst *KeyLoad2 = RetB.CreateLoad(I64Ty, KeyGV, /*isVolatile=*/true,
                                           "retenc.key.ret");

      LoadInst *EncLRLoad =
          RetB.CreateLoad(I64Ty, LRPtr2, "retenc.enc.ret");
      Value *DecLR = RetB.CreateXor(EncLRLoad, KeyLoad2, "retenc.dec");
      RetB.CreateStore(DecLR, LRPtr2);
    }

    return true;
  }
};

char ReturnAddressEncryption::ID = 0;

} // anonymous namespace

INITIALIZE_PASS(ReturnAddressEncryption, "retenc",
                "Return Address Encryption", false, false)

FunctionPass *llvm::createReturnAddressEncryptionPass(bool flag) {
  return new ReturnAddressEncryption(flag);
}
