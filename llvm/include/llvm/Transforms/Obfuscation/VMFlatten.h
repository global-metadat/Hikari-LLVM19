#ifndef _VMFLATTEN_H_
#define _VMFLATTEN_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {

FunctionPass *createVMFlattenPass(bool flag);
void initializeVMFlattenPass(PassRegistry &Registry);

} // namespace llvm

#endif
