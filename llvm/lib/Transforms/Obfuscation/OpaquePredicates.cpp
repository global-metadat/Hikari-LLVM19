// Strong Opaque Predicates Pass
// Inserts always-true/always-false predicates based on number theory,
// replacing simple BCF predicates with expressions that resist Z3/angr
// symbolic simplification.
//
// Usage: -mllvm --enable-opqpred -mllvm --opq_prob=80

#include "llvm/Transforms/Obfuscation/OpaquePredicates.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <vector>

using namespace llvm;

#define DEBUG_TYPE "opqpred"

static cl::opt<uint32_t>
    OpqProbRate("opq_prob",
                cl::desc("Probability [%] each branch gets an opaque predicate"),
                cl::value_desc("probability"), cl::init(60), cl::Optional);

STATISTIC(OpqTotal, "Total opaque predicates inserted");

// ── Predicate generators ──
// Each returns a Value* that is provably always true (icmp result i1).
// The input 'x' is loaded from a volatile global so LLVM can't constant-fold.

// x*x mod 3 != 2  (quadratic residues mod 3 are {0,1}, never 2)
static Value *genQuadraticResidue3(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod = B.CreateURem(sq, ConstantInt::get(x->getType(), 3), "opq.mod3");
  return B.CreateICmpNE(mod, ConstantInt::get(x->getType(), 2), "opq.qr3");
}

// (7*y*y + 1) mod 7 != 0  (7*y² ≡ 0 mod 7, so 7*y²+1 ≡ 1 mod 7, never 0)
static Value *genEuler7(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mul7 = B.CreateMul(sq, ConstantInt::get(x->getType(), 7), "opq.7sq");
  Value *plus1 = B.CreateAdd(mul7, ConstantInt::get(x->getType(), 1), "opq.7sq1");
  Value *mod = B.CreateURem(plus1, ConstantInt::get(x->getType(), 7), "opq.mod7");
  return B.CreateICmpNE(mod, ConstantInt::get(x->getType(), 0), "opq.e7");
}

// x*(x+1) mod 2 == 0  (product of consecutive integers is always even)
static Value *genConsecutiveEven(IRBuilder<> &B, Value *x) {
  Value *xp1 = B.CreateAdd(x, ConstantInt::get(x->getType(), 1), "opq.xp1");
  Value *prod = B.CreateMul(x, xp1, "opq.prod");
  Value *mod = B.CreateURem(prod, ConstantInt::get(x->getType(), 2), "opq.mod2");
  return B.CreateICmpEQ(mod, ConstantInt::get(x->getType(), 0), "opq.ce");
}

// x*x mod 4 != 3  (squares mod 4 are {0,1}, never 2 or 3)
static Value *genQuadraticResidue4(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod = B.CreateURem(sq, ConstantInt::get(x->getType(), 4), "opq.mod4");
  return B.CreateICmpNE(mod, ConstantInt::get(x->getType(), 3), "opq.qr4");
}

// x*x mod 8 is in {0,1,4}  → x²%8 < 5  (always true since max residue is 4)
static Value *genQuadraticResidue8(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod = B.CreateURem(sq, ConstantInt::get(x->getType(), 8), "opq.mod8");
  return B.CreateICmpULT(mod, ConstantInt::get(x->getType(), 5), "opq.qr8");
}

// (x | 1) != 0  (always true: setting bit 0 guarantees nonzero)
static Value *genOrOne(IRBuilder<> &B, Value *x) {
  Value *ored = B.CreateOr(x, ConstantInt::get(x->getType(), 1), "opq.or1");
  return B.CreateICmpNE(ored, ConstantInt::get(x->getType(), 0), "opq.nz");
}

// x*x + x ≡ 0 mod 2  (x²+x = x(x+1), always even)
static Value *genSqPlusXEven(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *sum = B.CreateAdd(sq, x, "opq.sqx");
  Value *mod = B.CreateURem(sum, ConstantInt::get(x->getType(), 2), "opq.mod2");
  return B.CreateICmpEQ(mod, ConstantInt::get(x->getType(), 0), "opq.sxe");
}

// 3*x*x + 2 mod 3 == 2  (3x² ≡ 0 mod 3, so 3x²+2 ≡ 2 mod 3)
static Value *genCubicResidue(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mul3 = B.CreateMul(sq, ConstantInt::get(x->getType(), 3), "opq.3sq");
  Value *plus2 = B.CreateAdd(mul3, ConstantInt::get(x->getType(), 2), "opq.3sq2");
  Value *mod = B.CreateURem(plus2, ConstantInt::get(x->getType(), 3), "opq.mod3");
  return B.CreateICmpEQ(mod, ConstantInt::get(x->getType(), 2), "opq.cr");
}

// x² mod 5 != 3  (QR mod 5 = {0,1,4}, never 2 or 3)
static Value *genQuadraticResidue5(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod = B.CreateURem(sq, ConstantInt::get(x->getType(), 5), "opq.mod5");
  return B.CreateICmpNE(mod, ConstantInt::get(x->getType(), 3), "opq.qr5");
}

// (x & x) == x  (AND with self is identity, always true)
// Wrapped in more arithmetic to confuse pattern matchers
static Value *genSelfAndObfuscated(IRBuilder<> &B, Value *x) {
  Value *selfAnd = B.CreateAnd(x, x, "opq.aa");
  Value *xorVal = B.CreateXor(selfAnd, x, "opq.xsa");
  return B.CreateICmpEQ(xorVal, ConstantInt::get(x->getType(), 0), "opq.sao");
}

// x*x*x*x mod 5 < 2  (x⁴ mod 5 ∈ {0,1} by Fermat's little theorem)
static Value *genFermat5(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *p4 = B.CreateMul(sq, sq, "opq.p4");
  Value *mod = B.CreateURem(p4, ConstantInt::get(x->getType(), 5), "opq.mod5");
  return B.CreateICmpULT(mod, ConstantInt::get(x->getType(), 2), "opq.f5");
}

// x² + 4 mod 5 != 0  (QR+4 mod 5: {4,0,3} → can be 0 when x²≡1 mod5)
// WRONG — this is not always true. Let me use a correct one:
// (x^2 + x) is always even => (x^2 + x) & 1 == 0
static Value *genSqXAnd1(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *sum = B.CreateAdd(sq, x, "opq.sqx");
  Value *bit = B.CreateAnd(sum, ConstantInt::get(x->getType(), 1), "opq.and1");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.sxa1");
}

using PredicateGen = Value *(*)(IRBuilder<> &, Value *);

static const PredicateGen generators[] = {
    genQuadraticResidue3, genEuler7,          genConsecutiveEven,
    genQuadraticResidue4, genQuadraticResidue8, genOrOne,
    genSqPlusXEven,       genCubicResidue,    genQuadraticResidue5,
    genSelfAndObfuscated, genFermat5,         genSqXAnd1,
};
static constexpr size_t NumGenerators = sizeof(generators) / sizeof(generators[0]);

// Generate a compound predicate: AND together N random always-true predicates
// This makes it much harder for Z3 to simplify — each conjunct uses different
// number theory properties.
static Value *genCompoundPredicate(IRBuilder<> &B, Value *x, uint32_t count) {
  Value *result = generators[cryptoutils->get_range(NumGenerators)](B, x);
  for (uint32_t i = 1; i < count; i++) {
    Value *next = generators[cryptoutils->get_range(NumGenerators)](B, x);
    result = B.CreateAnd(result, next, "opq.compound");
  }
  return result;
}

// Generate dead code for the unreachable (false) branch
static void emitDeadCode(BasicBlock *BB, IRBuilder<> &B) {
  // Insert some junk stores and arithmetic that look real but are never reached
  Type *I64Ty = Type::getInt64Ty(BB->getContext());
  Value *junkA = B.CreateAlloca(I64Ty, nullptr, "opq.junk.a");
  Value *junkB = B.CreateAlloca(I64Ty, nullptr, "opq.junk.b");
  ConstantInt *c1 = ConstantInt::get(I64Ty, cryptoutils->get_uint64_t());
  ConstantInt *c2 = ConstantInt::get(I64Ty, cryptoutils->get_uint64_t());
  B.CreateStore(c1, junkA);
  B.CreateStore(c2, junkB);
  Value *v1 = B.CreateLoad(I64Ty, junkA, "opq.jl1");
  Value *v2 = B.CreateLoad(I64Ty, junkB, "opq.jl2");
  // Random arithmetic chain
  Value *r = v1;
  for (int i = 0; i < 3; i++) {
    switch (cryptoutils->get_range(4)) {
    case 0: r = B.CreateAdd(r, v2, "opq.jd"); break;
    case 1: r = B.CreateXor(r, v2, "opq.jd"); break;
    case 2: r = B.CreateMul(r, v2, "opq.jd"); break;
    case 3: r = B.CreateSub(r, v2, "opq.jd"); break;
    }
  }
  B.CreateStore(r, junkA);
}

// ── Pass implementation ──

namespace {

struct OpaquePredicates : public FunctionPass {
  static char ID;
  bool flag;

  OpaquePredicates() : FunctionPass(ID) { this->flag = true; }
  OpaquePredicates(bool flag) : OpaquePredicates() { this->flag = flag; }

  bool runOnFunction(Function &F) override {
    Function *tmp = &F;
    if (!toObfuscate(flag, tmp, "opqpred"))
      return false;

    errs() << "Running Opaque Predicates On " << F.getName() << "\n";

    Module &M = *F.getParent();
    LLVMContext &Ctx = M.getContext();
    Type *I64Ty = Type::getInt64Ty(Ctx);

    // Create a volatile global for the opaque variable
    // Volatile prevents LLVM from constant-folding the predicate
    GlobalVariable *OpaqueGV = new GlobalVariable(
        M, I64Ty, false, GlobalValue::PrivateLinkage,
        ConstantInt::get(I64Ty, cryptoutils->get_uint64_t()),
        "opq_var_" + F.getName());

    // Collect conditional branches
    std::vector<BranchInst *> branches;
    for (BasicBlock &BB : F) {
      if (BranchInst *BI = dyn_cast<BranchInst>(BB.getTerminator())) {
        if (BI->isConditional()) {
          if (cryptoutils->get_range(100) < OpqProbRate)
            branches.push_back(BI);
        }
      }
    }

    // Also collect unconditional branches to split into conditional
    std::vector<BranchInst *> unconditional;
    for (BasicBlock &BB : F) {
      if (BranchInst *BI = dyn_cast<BranchInst>(BB.getTerminator())) {
        if (!BI->isConditional() && BI->getNumSuccessors() == 1) {
          // Don't mess with entry block's trivial branches
          if (&BB == &F.getEntryBlock())
            continue;
          if (cryptoutils->get_range(100) < OpqProbRate / 2)
            unconditional.push_back(BI);
        }
      }
    }

    if (branches.empty() && unconditional.empty())
      return false;

    bool changed = false;

    // Strengthen existing conditional branches by ANDing an opaque predicate
    for (BranchInst *BI : branches) {
      BasicBlock *BB = BI->getParent();
      IRBuilder<> B(BI);

      // Load the opaque variable with volatile
      LoadInst *x = B.CreateLoad(I64Ty, OpaqueGV, true, "opq.load");

      // Generate compound always-true predicate (2-3 conjuncts)
      uint32_t complexity = 2 + cryptoutils->get_range(2);
      Value *opaqueCond = genCompoundPredicate(B, x, complexity);

      // AND with existing condition: if original was true, opaque is also true,
      // so behavior is preserved. If original was false, stays false.
      Value *origCond = BI->getCondition();
      Value *combined = B.CreateAnd(origCond, opaqueCond, "opq.combined");

      BI->setCondition(combined);
      ++OpqTotal;
      changed = true;
    }

    // Convert unconditional branches to conditional with dead-code false branch
    for (BranchInst *BI : unconditional) {
      BasicBlock *BB = BI->getParent();
      BasicBlock *realDest = BI->getSuccessor(0);

      // Create a dead basic block with junk code
      BasicBlock *deadBB =
          BasicBlock::Create(Ctx, "opq.dead", &F, realDest);
      {
        IRBuilder<> deadB(deadBB);
        emitDeadCode(deadBB, deadB);
        deadB.CreateBr(realDest); // Loop back to real dest to keep CFG valid
      }

      // Replace unconditional branch with conditional
      IRBuilder<> B(BI);
      LoadInst *x = B.CreateLoad(I64Ty, OpaqueGV, true, "opq.load");

      uint32_t complexity = 2 + cryptoutils->get_range(2);
      Value *opaqueCond = genCompoundPredicate(B, x, complexity);

      // Always-true → always goes to realDest, dead block is never reached
      BranchInst::Create(realDest, deadBB, opaqueCond, BI);
      BI->eraseFromParent();

      ++OpqTotal;
      changed = true;
    }

    return changed;
  }
};

} // namespace

char OpaquePredicates::ID = 0;
INITIALIZE_PASS(OpaquePredicates, "opqpred", "Enable Opaque Predicates.", false,
                false)
FunctionPass *llvm::createOpaquePredicatesPass(bool flag) {
  return new OpaquePredicates(flag);
}
