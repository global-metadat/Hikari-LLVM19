// For open-source license, please refer to
// [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
// FunctionWrapper — wraps direct function calls through a trampoline function.
//
// Each eligible call site `call @foo(args...)` becomes `call @wrapper(args...)`
// where @wrapper is a new internal function that simply forwards to @foo.
// Combined with IndirectBranch, the wrapper is indirected, making call graph
// reconstruction harder.
//
// Rewritten for LLVM 17+ opaque pointers: uses CallBase* directly instead of
// the deprecated CallSite wrapper, and removes ConstantExpr::getBitCast for
// pointer-to-pointer casts which no longer exist with opaque pointers.
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Obfuscation/FunctionWrapper.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;

static cl::opt<uint32_t>
    ProbRate("fw_prob",
             cl::desc("Choose the probability [%] for each call site to be "
                      "obfuscated by FunctionWrapper"),
             cl::value_desc("Probability Rate"), cl::init(30), cl::Optional);
static uint32_t ProbRateTemp = 30;

static cl::opt<uint32_t> ObfTimes(
    "fw_times",
    cl::desc(
        "Choose how many times the FunctionWrapper pass loops on a call site"),
    cl::value_desc("Number of Times"), cl::init(2), cl::Optional);

namespace llvm {
struct FunctionWrapper : public ModulePass {
  static char ID;
  bool flag;
  FunctionWrapper() : ModulePass(ID) { this->flag = true; }
  FunctionWrapper(bool flag) : ModulePass(ID) { this->flag = flag; }
  StringRef getPassName() const override { return "FunctionWrapper"; }

  bool runOnModule(Module &M) override {
    // Collect eligible call sites first, then transform.
    // Transforming during iteration would invalidate iterators.
    SmallVector<CallBase *, 16> CallSites;
    for (Function &F : M) {
      if (!toObfuscate(flag, &F, "fw"))
        continue;
      errs() << "Running FunctionWrapper On " << F.getName() << "\n";
      if (!toObfuscateUint32Option(&F, "fw_prob", &ProbRateTemp))
        ProbRateTemp = ProbRate;
      if (ProbRateTemp > 100) {
        errs() << "FunctionWrapper: -fw_prob=x must be 0 < x <= 100\n";
        return false;
      }
      for (Instruction &Inst : instructions(F)) {
        auto *CB = dyn_cast<CallBase>(&Inst);
        if (!CB)
          continue;
        // Skip invoke/callbr — wrapping them requires landing pad handling
        if (!isa<CallInst>(CB))
          continue;
        // Skip inline asm
        if (CB->isInlineAsm())
          continue;
        if (cryptoutils->get_range(100) <= ProbRateTemp)
          CallSites.push_back(CB);
      }
    }
    for (CallBase *CB : CallSites) {
      for (uint32_t i = 0; i < ObfTimes && CB != nullptr; i++)
        CB = HandleCallSite(CB);
    }
    return true;
  } // End of runOnModule

  CallBase *HandleCallSite(CallBase *CB) {
    // Resolve the called function (direct or through pointer casts)
    Function *CalledF = CB->getCalledFunction();
    if (!CalledF) {
      Value *V = CB->getCalledOperand()->stripPointerCasts();
      CalledF = dyn_cast<Function>(V);
    }
    if (!CalledF)
      return nullptr;

    // Skip intrinsics and clang builtins
    if (CalledF->isIntrinsic())
      return nullptr;
#if LLVM_VERSION_MAJOR >= 18
    if (CalledF->getName().starts_with("clang."))
#else
    if (CalledF->getName().startswith("clang."))
#endif
      return nullptr;

    // Skip functions with problematic parameter attributes
    for (auto &Arg : CalledF->args()) {
      if (Arg.hasStructRetAttr() || Arg.hasSwiftSelfAttr())
        return nullptr;
    }

    // Build wrapper function type from the actual argument types at the call site
    SmallVector<Type *, 8> ArgTypes;
    for (unsigned i = 0; i < CB->arg_size(); i++)
      ArgTypes.push_back(CB->getArgOperand(i)->getType());

    FunctionType *WrapperFT =
        FunctionType::get(CB->getType(), ArrayRef<Type *>(ArgTypes), false);

    Function *Wrapper =
        Function::Create(WrapperFT, GlobalValue::InternalLinkage,
                         "HikariFunctionWrapper", CB->getModule());
    Wrapper->setCallingConv(CB->getCallingConv());
    appendToCompilerUsed(*Wrapper->getParent(), {Wrapper});

    // Build wrapper body: forward all arguments to the real function
    BasicBlock *BB = BasicBlock::Create(Wrapper->getContext(), "", Wrapper);
    IRBuilder<> B(BB);

    SmallVector<Value *, 8> Args;
    for (auto &Arg : Wrapper->args())
      Args.push_back(&Arg);

    // Propagate byval attributes to the wrapper's parameters
    for (unsigned i = 0; i < CalledF->arg_size() && i < Args.size(); i++) {
      if (CalledF->hasParamAttribute(i, Attribute::ByVal)) {
        Type *ByValTy = CalledF->getParamAttribute(i, Attribute::ByVal)
                            .getValueAsType();
        if (ByValTy)
          Wrapper->addParamAttr(i, Attribute::getWithByValType(
                                       Wrapper->getContext(), ByValTy));
      }
    }

    // Call the real function through the wrapper
    CallInst *InnerCall =
        B.CreateCall(CalledF->getFunctionType(), CalledF, Args);
    InnerCall->setCallingConv(CB->getCallingConv());

    if (WrapperFT->getReturnType()->isVoidTy())
      B.CreateRetVoid();
    else
      B.CreateRet(InnerCall);

    // Replace the original call: update the function type first, then the callee
    CB->mutateFunctionType(WrapperFT);
    CB->setCalledOperand(Wrapper);

    return CB;
  }
};

ModulePass *createFunctionWrapperPass(bool flag) {
  return new FunctionWrapper(flag);
}
} // namespace llvm

char FunctionWrapper::ID = 0;
INITIALIZE_PASS(FunctionWrapper, "funcwra", "Enable FunctionWrapper.", false,
                false)
