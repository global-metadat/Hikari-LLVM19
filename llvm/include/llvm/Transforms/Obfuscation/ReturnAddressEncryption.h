#ifndef _RETURN_ADDRESS_ENCRYPTION_H_
#define _RETURN_ADDRESS_ENCRYPTION_H_

#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {

FunctionPass *createReturnAddressEncryptionPass(bool flag);
void initializeReturnAddressEncryptionPass(PassRegistry &Registry);

} // namespace llvm

#endif
