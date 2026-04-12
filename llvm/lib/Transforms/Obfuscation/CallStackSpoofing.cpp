// CallStackSpoofing
//
// For each call site in a marked function, temporarily overwrites the
// saved-LR slot at [FP+8] with the address of a decoy libc function
// (printf/malloc/memcpy/...). The original LR is saved in an SSA value
// before the call and restored right after, so control flow is
// unaffected. Any external observer sampling the backtrace DURING the
// call — crash handler, profiler, Frida Interceptor, unwind-based
// detector — sees the decoy as our "caller", masking the real control
// flow.
//
// ARM64 only. Applies per-function via annotation "callstack_spoof" or
// when the global flag is on.

#include "llvm/Transforms/Obfuscation/CallStackSpoofing.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <vector>

using namespace llvm;

static cl::opt<uint32_t>
    CSSProbability("css_prob", cl::init(100), cl::NotHidden,
                   cl::desc("CallStackSpoofing probability per call (0-100)"));

namespace {

struct CallStackSpoofing : public FunctionPass {
  static char ID;
  bool flag;

  CallStackSpoofing() : FunctionPass(ID), flag(true) {}
  CallStackSpoofing(bool flag) : FunctionPass(ID), flag(flag) {}

  bool runOnFunction(Function &F) override;

  StringRef getPassName() const override { return "CallStackSpoofing"; }

private:
  Function *getOrDeclareDecoy(Module &M, StringRef name);
  Constant *pickDecoy(Module &M);
  bool spoofCall(CallInst *CI, Function *FrameAddr, Constant *Decoy);
};

} // namespace

char CallStackSpoofing::ID = 0;

static const char *const kDecoyNames[] = {
    "printf", "malloc", "memcpy", "memset", "strlen",
    "strcmp", "read",   "write",  "free",   "fprintf",
};

Function *CallStackSpoofing::getOrDeclareDecoy(Module &M, StringRef name) {
  if (Function *F = M.getFunction(name))
    return F;
  LLVMContext &Ctx = M.getContext();
  FunctionType *FT = FunctionType::get(Type::getInt32Ty(Ctx), true);
  Function *F = Function::Create(FT, GlobalValue::ExternalLinkage, name, &M);
  F->setDoesNotThrow();
  return F;
}

Constant *CallStackSpoofing::pickDecoy(Module &M) {
  unsigned idx =
      cryptoutils->get_uint32_t() % (sizeof(kDecoyNames) / sizeof(kDecoyNames[0]));
  Function *D = getOrDeclareDecoy(M, kDecoyNames[idx]);
  return ConstantExpr::getPtrToInt(D, Type::getInt64Ty(M.getContext()));
}

bool CallStackSpoofing::spoofCall(CallInst *CI, Function *FrameAddr,
                                  Constant *Decoy) {
  // Skip intrinsics and inline asm — those don't go through a normal BL.
  if (CI->isInlineAsm())
    return false;
  if (Function *Callee = CI->getCalledFunction())
    if (Callee->isIntrinsic())
      return false;
  // Don't spoof tail calls — the saved LR isn't written back on entry
  // to the callee for musttail/tail sequences.
  if (CI->isMustTailCall() || CI->isTailCall())
    return false;

  LLVMContext &Ctx = CI->getContext();
  Type *I64Ty = Type::getInt64Ty(Ctx);
  Type *PtrTy = PointerType::get(Ctx, 0);

  IRBuilder<> B(CI);
  Value *FP = B.CreateCall(FrameAddr, {ConstantInt::get(Type::getInt32Ty(Ctx), 0)});
  Value *LrSlot = B.CreateGEP(Type::getInt8Ty(Ctx), FP,
                              ConstantInt::get(I64Ty, 8), "css.lr_slot");
  LoadInst *realLR =
      B.CreateAlignedLoad(I64Ty, LrSlot, Align(8), /*isVolatile=*/true);
  // Add small random displacement to the decoy so different callsites
  // don't all show the exact same fake LR.
  int32_t disp = ((int32_t)(cryptoutils->get_uint32_t() & 0x3F)) * 4;
  Value *FakeLR =
      B.CreateAdd(Decoy, ConstantInt::get(I64Ty, (int64_t)disp));
  B.CreateAlignedStore(FakeLR, LrSlot, Align(8), /*isVolatile=*/true);

  // Now re-anchor the builder AFTER the call to restore LR.
  B.SetInsertPoint(CI->getNextNode());
  B.CreateAlignedStore(realLR, LrSlot, Align(8), /*isVolatile=*/true);
  return true;
}

bool CallStackSpoofing::runOnFunction(Function &F) {
  if (!toObfuscate(flag, &F, "callstack_spoof"))
    return false;
  if (F.isDeclaration() || F.hasFnAttribute(Attribute::Naked))
    return false;

  Module *M = F.getParent();
  Triple T(M->getTargetTriple());
  if (!T.isAArch64())
    return false;

  uint32_t prob = CSSProbability;
  toObfuscateUint32Option(&F, "css_prob", &prob);
  if (prob > 100)
    prob = 100;
  if (prob == 0)
    return false;

  // Force frame-pointer so [FP+8] has well-defined meaning.
  F.addFnAttr("frame-pointer", "all");

  // Collect callsites (don't mutate while iterating).
  std::vector<CallInst *> worklist;
  for (BasicBlock &BB : F)
    for (Instruction &I : BB)
      if (CallInst *CI = dyn_cast<CallInst>(&I))
        worklist.push_back(CI);

  if (worklist.empty())
    return false;

  Function *FrameAddr =
      Intrinsic::getDeclaration(M, Intrinsic::frameaddress, {PointerType::get(F.getContext(), 0)});

  bool changed = false;
  for (CallInst *CI : worklist) {
    if ((cryptoutils->get_uint32_t() % 100) >= prob)
      continue;
    Constant *decoy = pickDecoy(*M);
    changed |= spoofCall(CI, FrameAddr, decoy);
  }
  return changed;
}

FunctionPass *llvm::createCallStackSpoofingPass(bool flag) {
  return new CallStackSpoofing(flag);
}

INITIALIZE_PASS(CallStackSpoofing, "callstack-spoof",
                "Spoof saved LR around call sites to mislead stack unwinders",
                false, false)
