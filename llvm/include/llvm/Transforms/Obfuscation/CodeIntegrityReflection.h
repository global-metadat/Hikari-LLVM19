#ifndef _CODE_INTEGRITY_REFLECTION_H_
#define _CODE_INTEGRITY_REFLECTION_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
ModulePass *createCodeIntegrityReflectionPass(bool flag);
void initializeCodeIntegrityReflectionPass(PassRegistry &Registry);
} // namespace llvm

#endif
