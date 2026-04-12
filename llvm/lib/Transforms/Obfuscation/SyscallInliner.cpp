// SyscallInliner
//
// Replaces calls to libc syscall-wrapper functions (read, write, openat,
// close, mmap, mprotect, ...) with direct `svc #0` inline-asm sequences.
// Bypasses libc PLT hooks and LD_PRELOAD interposition.
//
// ARM64 Linux only. Applies per-function via annotation
// "syscall_inline" or when the global flag is on.
//
// Args are passed in x0..xN; syscall number goes in x8. Return value
// comes back in x0.

#include "llvm/Transforms/Obfuscation/SyscallInliner.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/TargetParser/Triple.h"
#include <vector>

using namespace llvm;

namespace {

struct SyscallInfo {
  const char *name;
  int num;
  int nargs;
};

// ARM64 Linux syscall numbers (from asm-generic/unistd.h).
static const SyscallInfo kSyscalls[] = {
    {"read", 63, 3},     {"write", 64, 3},     {"openat", 56, 4},
    {"close", 57, 1},    {"lseek", 62, 3},     {"mmap", 222, 6},
    {"mprotect", 226, 3}, {"munmap", 215, 2},   {"getpid", 172, 0},
    {"gettid", 178, 0},  {"getuid", 174, 0},   {"geteuid", 175, 0},
    {"kill", 129, 2},    {"tgkill", 131, 3},   {"fsync", 82, 1},
    {"fstat", 80, 2},    {"readlinkat", 78, 4}, {"prctl", 167, 5},
    {"ptrace", 117, 4},  {"exit", 93, 1},      {"exit_group", 94, 1},
};

struct SyscallInliner : public FunctionPass {
  static char ID;
  bool flag;

  SyscallInliner() : FunctionPass(ID), flag(true) {}
  SyscallInliner(bool flag) : FunctionPass(ID), flag(flag) {}

  bool runOnFunction(Function &F) override;
  StringRef getPassName() const override { return "SyscallInliner"; }

private:
  const SyscallInfo *findSyscall(StringRef name);
  bool replaceCall(CallInst *CI, const SyscallInfo &info);
};

} // namespace

char SyscallInliner::ID = 0;

const SyscallInfo *SyscallInliner::findSyscall(StringRef name) {
  for (const auto &s : kSyscalls)
    if (name == s.name)
      return &s;
  return nullptr;
}

bool SyscallInliner::replaceCall(CallInst *CI, const SyscallInfo &info) {
  if (CI->isInlineAsm())
    return false;
  // Arg count must match exactly; variadics (printf etc.) aren't handled.
  if ((int)CI->arg_size() != info.nargs)
    return false;

  LLVMContext &Ctx = CI->getContext();
  Type *I64Ty = Type::getInt64Ty(Ctx);

  // Build inline-asm argument vector: all args are passed as i64 in
  // registers x0..x5. Promote smaller types via zext/sext; we don't
  // actually know signedness here — for pointer/size args unsigned is
  // safe; for negative fd etc. we'd need sext, but the resulting bits
  // in the 32-bit window are identical for either choice because the
  // kernel only reads the low 32 bits for 32-bit syscall args.
  std::vector<Type *> argTypes;
  std::vector<Value *> args;
  IRBuilder<> B(CI);
  for (unsigned i = 0; i < CI->arg_size(); ++i) {
    Value *a = CI->getArgOperand(i);
    Type *t = a->getType();
    if (t->isPointerTy()) {
      a = B.CreatePtrToInt(a, I64Ty);
    } else if (t->isIntegerTy()) {
      unsigned bw = t->getIntegerBitWidth();
      if (bw < 64)
        a = B.CreateZExt(a, I64Ty);
      else if (bw > 64)
        a = B.CreateTrunc(a, I64Ty);
    } else {
      return false; // float/struct args unsupported
    }
    args.push_back(a);
    argTypes.push_back(I64Ty);
  }

  // Asm string: mov x8, #<n>; svc #0. Input constraints bind x0..xN.
  std::string asmStr;
  char nbuf[32];
  std::snprintf(nbuf, sizeof(nbuf), "mov x8, #%d\n\tsvc #0", info.num);
  asmStr = nbuf;

  // Constraints:
  //   output "={x0}" — return value in x0
  //   inputs  "{x0}","{x1}"... — each arg pinned to its syscall register
  //   clobbers ~{x8},~{memory},~{cc}
  std::string cons = "={x0}";
  static const char *const kRegs[] = {"{x0}", "{x1}", "{x2}",
                                       "{x3}", "{x4}", "{x5}"};
  for (unsigned i = 0; i < args.size(); ++i) {
    cons += ",";
    cons += kRegs[i];
  }
  cons += ",~{x8},~{memory},~{cc}";

  FunctionType *AsmFTy = FunctionType::get(I64Ty, argTypes, false);
  InlineAsm *IA = InlineAsm::get(AsmFTy, asmStr, cons,
                                  /*hasSideEffects=*/true);
  CallInst *NewCI = B.CreateCall(IA, args);

  // Replace uses — handle result type coercion.
  Type *retTy = CI->getType();
  Value *repl = NewCI;
  if (retTy->isVoidTy()) {
    // Nothing to replace with; just drop the original.
  } else if (retTy->isIntegerTy()) {
    unsigned bw = retTy->getIntegerBitWidth();
    if (bw < 64)
      repl = B.CreateTrunc(NewCI, retTy);
    else if (bw > 64)
      repl = B.CreateZExt(NewCI, retTy);
  } else if (retTy->isPointerTy()) {
    repl = B.CreateIntToPtr(NewCI, retTy);
  } else {
    // Unsupported return type — can't complete the swap; bail out by
    // removing the inserted asm call's users and keeping the original.
    NewCI->eraseFromParent();
    return false;
  }

  if (!retTy->isVoidTy())
    CI->replaceAllUsesWith(repl);
  CI->eraseFromParent();
  return true;
}

bool SyscallInliner::runOnFunction(Function &F) {
  if (!toObfuscate(flag, &F, "syscall_inline"))
    return false;
  if (F.isDeclaration())
    return false;

  Module *M = F.getParent();
  Triple T(M->getTargetTriple());
  if (!T.isAArch64() || !T.isOSLinux())
    return false;

  std::vector<std::pair<CallInst *, const SyscallInfo *>> worklist;
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      CallInst *CI = dyn_cast<CallInst>(&I);
      if (!CI)
        continue;
      Function *Callee = CI->getCalledFunction();
      if (!Callee || !Callee->hasName())
        continue;
      StringRef name = Callee->getName();
      // Some libcs use leading "__" prefix.
      if (name.starts_with("__"))
        name = name.drop_front(2);
      const SyscallInfo *info = findSyscall(name);
      if (!info)
        continue;
      worklist.emplace_back(CI, info);
    }
  }

  bool changed = false;
  for (auto &pr : worklist)
    changed |= replaceCall(pr.first, *pr.second);
  return changed;
}

FunctionPass *llvm::createSyscallInlinerPass(bool flag) {
  return new SyscallInliner(flag);
}

INITIALIZE_PASS(SyscallInliner, "syscall-inliner",
                "Replace libc syscall wrappers with direct svc #0", false,
                false)
