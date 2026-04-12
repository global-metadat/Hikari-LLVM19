#ifndef _INSTRUCTION_LEVEL_ANTI_PATCHING_H_
#define _INSTRUCTION_LEVEL_ANTI_PATCHING_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
FunctionPass *createInstructionLevelAntiPatchingPass(bool flag);
void initializeInstructionLevelAntiPatchingPass(PassRegistry &Registry);
} // namespace llvm

#endif
