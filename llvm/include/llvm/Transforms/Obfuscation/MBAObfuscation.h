#ifndef _MBAOBFUSCATION_H_
#define _MBAOBFUSCATION_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {

FunctionPass *createMBAObfuscationPass(bool flag);
void initializeMBAObfuscationPass(PassRegistry &Registry);

} // namespace llvm

#endif
