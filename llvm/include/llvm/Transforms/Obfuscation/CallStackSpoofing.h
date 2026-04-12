#ifndef _CALL_STACK_SPOOFING_H_
#define _CALL_STACK_SPOOFING_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {
FunctionPass *createCallStackSpoofingPass(bool flag);
void initializeCallStackSpoofingPass(PassRegistry &Registry);
} // namespace llvm

#endif
