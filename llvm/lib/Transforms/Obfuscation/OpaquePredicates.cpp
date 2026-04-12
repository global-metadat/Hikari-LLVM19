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
//
// IMPORTANT: NO URem operations. URem by small constants (3, 5, 7) compiles to
// recognizable umull/umulh/lsr sequences on ARM64 that Hex-Rays/Ghidra/BinaryNinja
// identify as "x % N" and simplify. All modular arithmetic uses bitwise AND
// (for power-of-2 moduli) or is replaced with purely bitwise predicates.

// x*(x+1) is always even → (x*(x+1)) & 1 == 0
static Value *genConsecutiveProduct(IRBuilder<> &B, Value *x) {
  Value *xp1 = B.CreateAdd(x, ConstantInt::get(x->getType(), 1), "opq.xp1");
  Value *prod = B.CreateMul(x, xp1, "opq.prod");
  Value *bit = B.CreateAnd(prod, ConstantInt::get(x->getType(), 1), "opq.bit");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.ce");
}

// x² + x is always even → (x²+x) & 1 == 0
static Value *genSqPlusXEven(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *sum = B.CreateAdd(sq, x, "opq.sqx");
  Value *bit = B.CreateAnd(sum, ConstantInt::get(x->getType(), 1), "opq.bit");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.sxe");
}

// x² & 3 (= x² mod 4) is in {0,1} → x² & 3 != 3 (always true)
static Value *genQuadraticResidue4(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod4 = B.CreateAnd(sq, ConstantInt::get(x->getType(), 3), "opq.m4");
  return B.CreateICmpNE(mod4, ConstantInt::get(x->getType(), 3), "opq.qr4");
}

// x² & 3 != 2 (squares mod 4 are {0,1}, never 2)
static Value *genQuadraticResidue4v2(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod4 = B.CreateAnd(sq, ConstantInt::get(x->getType(), 3), "opq.m4");
  return B.CreateICmpNE(mod4, ConstantInt::get(x->getType(), 2), "opq.qr4b");
}

// x² & 7 (= x² mod 8) < 5 (QR mod 8 are {0,1,4}, max is 4)
static Value *genQuadraticResidue8(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod8 = B.CreateAnd(sq, ConstantInt::get(x->getType(), 7), "opq.m8");
  return B.CreateICmpULT(mod8, ConstantInt::get(x->getType(), 5), "opq.qr8");
}

// (x | 1) != 0 (setting bit 0 guarantees nonzero)
static Value *genOrOne(IRBuilder<> &B, Value *x) {
  Value *ored = B.CreateOr(x, ConstantInt::get(x->getType(), 1), "opq.or1");
  return B.CreateICmpNE(ored, ConstantInt::get(x->getType(), 0), "opq.nz");
}

// (x+1)*(x+2) is always even → ((x+1)*(x+2)) & 1 == 0
static Value *genConsecutiveProductShifted(IRBuilder<> &B, Value *x) {
  Value *xp1 = B.CreateAdd(x, ConstantInt::get(x->getType(), 1), "opq.xp1");
  Value *xp2 = B.CreateAdd(x, ConstantInt::get(x->getType(), 2), "opq.xp2");
  Value *prod = B.CreateMul(xp1, xp2, "opq.prod");
  Value *bit = B.CreateAnd(prod, ConstantInt::get(x->getType(), 1), "opq.bit");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.cps");
}

// x² + 3x + 2 = (x+1)(x+2) → always even → & 1 == 0
// Different expression form from genConsecutiveProductShifted
static Value *genPolynomialEven(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *x3 = B.CreateMul(x, ConstantInt::get(x->getType(), 3), "opq.3x");
  Value *sum = B.CreateAdd(sq, x3, "opq.sq3x");
  Value *poly = B.CreateAdd(sum, ConstantInt::get(x->getType(), 2), "opq.poly");
  Value *bit = B.CreateAnd(poly, ConstantInt::get(x->getType(), 1), "opq.bit");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.pe");
}

// ((x * x) | 1) != 0 — OR 1 makes any value nonzero
static Value *genSqOrOne(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *ored = B.CreateOr(sq, ConstantInt::get(x->getType(), 1), "opq.or1");
  return B.CreateICmpNE(ored, ConstantInt::get(x->getType(), 0), "opq.sqnz");
}

// x⁴ & 15 (= x⁴ mod 16) < 2 — x⁴ mod 16 ∈ {0,1} for all x
// Proof: x even → x⁴ ≡ 0 mod 16. x odd → x = 2k+1, x² = 4k²+4k+1,
// x⁴ = (4k²+4k+1)² ≡ 1 mod 16.
static Value *genFourthPower16(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *p4 = B.CreateMul(sq, sq, "opq.p4");
  Value *mod16 = B.CreateAnd(p4, ConstantInt::get(x->getType(), 15), "opq.m16");
  return B.CreateICmpULT(mod16, ConstantInt::get(x->getType(), 2), "opq.fp16");
}

// x * (x+1) * (x+2) is always divisible by 6. In particular, always even.
// → (x*(x+1)*(x+2)) & 1 == 0
static Value *genTripleProduct(IRBuilder<> &B, Value *x) {
  Value *xp1 = B.CreateAdd(x, ConstantInt::get(x->getType(), 1), "opq.xp1");
  Value *xp2 = B.CreateAdd(x, ConstantInt::get(x->getType(), 2), "opq.xp2");
  Value *p1 = B.CreateMul(x, xp1, "opq.p1");
  Value *p2 = B.CreateMul(p1, xp2, "opq.p2");
  Value *bit = B.CreateAnd(p2, ConstantInt::get(x->getType(), 1), "opq.bit");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.tp");
}

// 2*x² + x is always: if x even → 0, if x odd → 2+1=3 → always ≡ x mod 2.
// So (2*x² + x) & 1 == x & 1 → xor of them is 0.
// But that's simplifiable... use a harder variant:
// x*(2*x+1) & 1: if x even → 0*odd = 0 → bit0=0. If x odd → odd*odd = odd → bit0=1.
// So x*(2x+1) & 1 == x & 1. But we can express: (x*(2*x+1)) ^ x has bit0=0.
// ((x*(2*x+1)) ^ x) & 1 == 0 → always true
static Value *genMulXorParity(IRBuilder<> &B, Value *x) {
  Value *x2 = B.CreateMul(x, ConstantInt::get(x->getType(), 2), "opq.2x");
  Value *x2p1 = B.CreateAdd(x2, ConstantInt::get(x->getType(), 1), "opq.2xp1");
  Value *prod = B.CreateMul(x, x2p1, "opq.prod");
  Value *xored = B.CreateXor(prod, x, "opq.xor");
  Value *bit = B.CreateAnd(xored, ConstantInt::get(x->getType(), 1), "opq.bit");
  return B.CreateICmpEQ(bit, ConstantInt::get(x->getType(), 0), "opq.mxp");
}

// x² & 15 (mod 16) is in {0,1,4,9} → x² & 15 < 10 (always true, max QR=9)
static Value *genQuadraticResidue16(IRBuilder<> &B, Value *x) {
  Value *sq = B.CreateMul(x, x, "opq.sq");
  Value *mod16 = B.CreateAnd(sq, ConstantInt::get(x->getType(), 15), "opq.m16");
  return B.CreateICmpULT(mod16, ConstantInt::get(x->getType(), 10), "opq.qr16");
}

using PredicateGen = Value *(*)(IRBuilder<> &, Value *);

static const PredicateGen generators[] = {
    genConsecutiveProduct,      genSqPlusXEven,
    genQuadraticResidue4,       genQuadraticResidue4v2,
    genQuadraticResidue8,       genOrOne,
    genConsecutiveProductShifted, genPolynomialEven,
    genSqOrOne,                 genFourthPower16,
    genTripleProduct,           genMulXorParity,
    genQuadraticResidue16,
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

// Public API — callable from BCF and other passes
Value *llvm::genCompoundOpaquePredicate(IRBuilder<> &B, Value *x,
                                        uint32_t count) {
  return genCompoundPredicate(B, x, count);
}

LoadInst *llvm::createOpaqueLoad(IRBuilder<> &B, Module &M,
                                 const std::string &name) {
  Type *I64Ty = Type::getInt64Ty(M.getContext());
  GlobalVariable *GV = new GlobalVariable(
      M, I64Ty, false, GlobalValue::PrivateLinkage,
      ConstantInt::get(I64Ty, cryptoutils->get_uint64_t()), name);
  return B.CreateLoad(I64Ty, GV, /*isVolatile=*/true, "opq.load");
}

// Generate dead code for the unreachable (false) branch
static void emitDeadCode(BasicBlock *BB, IRBuilder<> &B) {
  // Insert some junk stores and arithmetic that look real but are never reached
  Type *I64Ty = Type::getInt64Ty(BB->getContext());
  Value *junkA = B.CreateAlloca(I64Ty, nullptr, "opq.junk.a");
  Value *junkB = B.CreateAlloca(I64Ty, nullptr, "opq.junk.b");
  Constant *c1 = ConstantInt::get(I64Ty, cryptoutils->get_uint64_t());
  Constant *c2 = ConstantInt::get(I64Ty, cryptoutils->get_uint64_t());
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
