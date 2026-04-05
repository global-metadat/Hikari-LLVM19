#ifndef _OBFUSCATION_ANTILINEARSWEEP_H_
#define _OBFUSCATION_ANTILINEARSWEEP_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
FunctionPass *createAntiLinearSweepPass(bool flag);
void initializeAntiLinearSweepPass(PassRegistry &Registry);
} // namespace llvm

#endif
