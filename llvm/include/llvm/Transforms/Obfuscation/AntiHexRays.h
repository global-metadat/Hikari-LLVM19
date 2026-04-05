#ifndef _OBFUSCATION_ANTIHEXRAYS_H_
#define _OBFUSCATION_ANTIHEXRAYS_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
FunctionPass *createAntiHexRaysPass(bool flag);
void initializeAntiHexRaysPass(PassRegistry &Registry);
} // namespace llvm

#endif
