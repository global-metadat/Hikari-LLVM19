#ifndef _SYSCALL_INLINER_H_
#define _SYSCALL_INLINER_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
FunctionPass *createSyscallInlinerPass(bool flag);
void initializeSyscallInlinerPass(PassRegistry &Registry);
} // namespace llvm

#endif
