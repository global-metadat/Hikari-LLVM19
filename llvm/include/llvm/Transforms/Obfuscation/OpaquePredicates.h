#ifndef _OPAQUEPREDICATES_H_
#define _OPAQUEPREDICATES_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {

FunctionPass *createOpaquePredicatesPass(bool flag);
void initializeOpaquePredicatesPass(PassRegistry &Registry);

} // namespace llvm

#endif
