#ifndef _OPAQUEPREDICATES_H_
#define _OPAQUEPREDICATES_H_

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"

namespace llvm {

FunctionPass *createOpaquePredicatesPass(bool flag);
void initializeOpaquePredicatesPass(PassRegistry &Registry);

/// Generate a compound always-true predicate by ANDing `count` random
/// number-theoretic predicates. `x` must be an i64 Value (typically loaded
/// from a volatile global). Returns an i1 Value that is provably always true.
/// Used by OpaquePredicates pass and by BCF for stronger bogus conditionals.
Value *genCompoundOpaquePredicate(IRBuilder<> &B, Value *x, uint32_t count);

/// Create a volatile-loaded opaque global suitable for use with
/// genCompoundOpaquePredicate. Returns the LoadInst.
LoadInst *createOpaqueLoad(IRBuilder<> &B, Module &M, const std::string &name);

} // namespace llvm

#endif
