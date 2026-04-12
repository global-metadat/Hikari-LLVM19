// MBA (Mixed Boolean-Arithmetic) Obfuscation Pass
// Replaces arithmetic/logic IR instructions with equivalent MBA expressions.
// Unlike Hikari's Substitution pass (1 layer), this applies N layers recursively,
// producing ~50-200 instructions per original operation at depth 3.
//
// Usage: -mllvm --enable-mbaobf -mllvm --mba_prob=60 -mllvm --mba_depth=2

#include "llvm/Transforms/Obfuscation/MBAObfuscation.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/Statistic.h"
#include <vector>

using namespace llvm;

#define DEBUG_TYPE "mbaobf"

static cl::opt<uint32_t>
    MBAProbRate("mba_prob",
                cl::desc("Probability [%] each instruction will be MBA-obfuscated"),
                cl::value_desc("probability"), cl::init(40), cl::Optional);

static cl::opt<uint32_t>
    MBADepth("mba_depth",
             cl::desc("Recursion depth for MBA substitution (1-4)"),
             cl::value_desc("depth"), cl::init(2), cl::Optional);

STATISTIC(MBATotal, "Total MBA substitutions applied");

// ── MBA core: procedural generation via null functions ──
//
// Theory: A "null function" N(a,b) is an expression that always evaluates to 0
// for all inputs a,b. Examples:
//   (a & b) + (a | b) - a - b = 0
//   (a ^ b) + 2*(a & b) - a - b = 0
//   (a | b) - (a ^ b) - (a & b) = 0
//
// For target operation OP(a,b), we generate:
//   OP(a,b) + c1*N1(a,b) + c2*N2(a,b) + ... + cn*Nn(a,b)
//
// where c1..cn are random constants chosen per-instance. Since each constant is
// 64 bits and we use 2-4 null functions, the search space is 2^128 to 2^256 —
// impossible to build a universal pattern database. Each compilation produces
// unique expressions.
//
// Reference: "Information Hiding in Software with Mixed Boolean-Arithmetic
// Transforms" (Zhou, Main, Thomborson, 2007).

// Forward declarations
static Value *mbaAdd(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaSub(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaXor(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaAnd(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaOr(Value *a, Value *b, Instruction *insertPt, uint32_t depth);

// ── Null function emitters ──
// Each returns a Value* that is always 0 for any inputs a, b.

// N0: (a & b) + (a | b) - a - b = 0
// Proof: a&b + a|b = a + b (Boolean identity)
static Value *nullFunc0(Value *a, Value *b, Instruction *ip) {
  Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", ip);
  Value *orAB = BinaryOperator::Create(Instruction::Or, a, b, "", ip);
  Value *sum1 = BinaryOperator::Create(Instruction::Add, andAB, orAB, "", ip);
  Value *sum2 = BinaryOperator::Create(Instruction::Add, a, b, "", ip);
  return BinaryOperator::Create(Instruction::Sub, sum1, sum2, "", ip);
}

// N1: (a ^ b) + 2*(a & b) - a - b = 0
// Proof: a^b + 2*(a&b) = a + b
static Value *nullFunc1(Value *a, Value *b, Instruction *ip) {
  Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", ip);
  Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", ip);
  Constant *two = ConstantInt::get(a->getType(), 2);
  Value *and2 = BinaryOperator::Create(Instruction::Mul, andAB, two, "", ip);
  Value *sum1 = BinaryOperator::Create(Instruction::Add, xorAB, and2, "", ip);
  Value *sum2 = BinaryOperator::Create(Instruction::Add, a, b, "", ip);
  return BinaryOperator::Create(Instruction::Sub, sum1, sum2, "", ip);
}

// N2: (a | b) - (a ^ b) - (a & b) = 0
// Proof: a|b = (a^b) + (a&b) (since a|b = a^b | a&b and they're disjoint)
static Value *nullFunc2(Value *a, Value *b, Instruction *ip) {
  Value *orAB = BinaryOperator::Create(Instruction::Or, a, b, "", ip);
  Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", ip);
  Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", ip);
  Value *sub1 = BinaryOperator::Create(Instruction::Sub, orAB, xorAB, "", ip);
  return BinaryOperator::Create(Instruction::Sub, sub1, andAB, "", ip);
}

// N3: (a & ~b) + (~a & b) - (a ^ b) = 0
// Proof: (a & ~b) | (~a & b) = a ^ b, and for disjoint sets OR = ADD
static Value *nullFunc3(Value *a, Value *b, Instruction *ip) {
  Value *notA = BinaryOperator::CreateNot(a, "", ip);
  Value *notB = BinaryOperator::CreateNot(b, "", ip);
  Value *andANB = BinaryOperator::Create(Instruction::And, a, notB, "", ip);
  Value *andNAB = BinaryOperator::Create(Instruction::And, notA, b, "", ip);
  Value *sum = BinaryOperator::Create(Instruction::Add, andANB, andNAB, "", ip);
  Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", ip);
  return BinaryOperator::Create(Instruction::Sub, sum, xorAB, "", ip);
}

// N4: ~(~a | ~b) - (a & b) = 0
// Proof: De Morgan's law: ~(~a | ~b) = a & b
static Value *nullFunc4(Value *a, Value *b, Instruction *ip) {
  Value *notA = BinaryOperator::CreateNot(a, "", ip);
  Value *notB = BinaryOperator::CreateNot(b, "", ip);
  Value *orNN = BinaryOperator::Create(Instruction::Or, notA, notB, "", ip);
  Value *dm = BinaryOperator::CreateNot(orNN, "", ip);
  Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", ip);
  return BinaryOperator::Create(Instruction::Sub, dm, andAB, "", ip);
}

// N5: ~(~a & ~b) - (a | b) = 0
// Proof: De Morgan's law: ~(~a & ~b) = a | b
static Value *nullFunc5(Value *a, Value *b, Instruction *ip) {
  Value *notA = BinaryOperator::CreateNot(a, "", ip);
  Value *notB = BinaryOperator::CreateNot(b, "", ip);
  Value *andNN = BinaryOperator::Create(Instruction::And, notA, notB, "", ip);
  Value *dm = BinaryOperator::CreateNot(andNN, "", ip);
  Value *orAB = BinaryOperator::Create(Instruction::Or, a, b, "", ip);
  return BinaryOperator::Create(Instruction::Sub, dm, orAB, "", ip);
}

// N6: ((a | b) ^ (a ^ b)) - (a & b) = 0
// Proof: (a|b) ^ (a^b) = a & b
static Value *nullFunc6(Value *a, Value *b, Instruction *ip) {
  Value *orAB = BinaryOperator::Create(Instruction::Or, a, b, "", ip);
  Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", ip);
  Value *xorOX = BinaryOperator::Create(Instruction::Xor, orAB, xorAB, "", ip);
  Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", ip);
  return BinaryOperator::Create(Instruction::Sub, xorOX, andAB, "", ip);
}

// N7: a - (a & ~b) - (a & b) = 0
// Proof: (a & ~b) + (a & b) = a & (~b | b) = a & -1 = a
static Value *nullFunc7(Value *a, Value *b, Instruction *ip) {
  Value *notB = BinaryOperator::CreateNot(b, "", ip);
  Value *andANB = BinaryOperator::Create(Instruction::And, a, notB, "", ip);
  Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", ip);
  Value *sub1 = BinaryOperator::Create(Instruction::Sub, a, andANB, "", ip);
  return BinaryOperator::Create(Instruction::Sub, sub1, andAB, "", ip);
}

using NullFunc = Value *(*)(Value *, Value *, Instruction *);
static const NullFunc nullFuncs[] = {
    nullFunc0, nullFunc1, nullFunc2, nullFunc3,
    nullFunc4, nullFunc5, nullFunc6, nullFunc7,
};
static constexpr size_t NumNullFuncs = sizeof(nullFuncs) / sizeof(nullFuncs[0]);

// Add random null-function noise to a value
// result = val + c1*N_i(a,b) + c2*N_j(a,b) + ...
static Value *addNullNoise(Value *val, Value *a, Value *b, Instruction *ip,
                           uint32_t numTerms) {
  Value *result = val;
  for (uint32_t i = 0; i < numTerms; i++) {
    uint32_t idx = cryptoutils->get_range(NumNullFuncs);
    Value *null_val = nullFuncs[idx](a, b, ip);
    // Multiply by random nonzero constant
    uint64_t coeff = cryptoutils->get_uint64_t();
    if (coeff == 0) coeff = 1;
    Value *scaled = BinaryOperator::Create(
        Instruction::Mul, null_val,
        ConstantInt::get(a->getType(), coeff), "", ip);
    result = BinaryOperator::Create(Instruction::Add, result, scaled, "", ip);
  }
  return result;
}

// ── Base operation emitters (choose a random correct expression) ──
// Each picks a random equivalent expression form, then adds null-function noise.

static Value *mbaAdd(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Add, a, b, "", insertPt);

  // Pick one of several equivalent forms for a + b
  Value *base;
  switch (cryptoutils->get_range(4)) {
  default:
  case 0: {
    // (a ^ b) + 2*(a & b)
    Value *xorAB = mbaXor(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    Constant *two = ConstantInt::get(a->getType(), 2);
    Value *mul = BinaryOperator::Create(Instruction::Mul, andAB, two, "", insertPt);
    base = BinaryOperator::Create(Instruction::Add, xorAB, mul, "", insertPt);
    break;
  }
  case 1: {
    // (a | b) + (a & b)
    Value *orAB = mbaOr(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    base = BinaryOperator::Create(Instruction::Add, orAB, andAB, "", insertPt);
    break;
  }
  case 2: {
    // a - (~b) - 1
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *sub1 = mbaSub(a, notB, insertPt, depth - 1);
    Constant *one = ConstantInt::get(a->getType(), 1);
    base = BinaryOperator::Create(Instruction::Sub, sub1, one, "", insertPt);
    break;
  }
  case 3: {
    // 2*(a | b) - (a ^ b)
    Value *orAB = mbaOr(a, b, insertPt, depth - 1);
    Constant *two = ConstantInt::get(a->getType(), 2);
    Value *dbl = BinaryOperator::Create(Instruction::Mul, orAB, two, "", insertPt);
    Value *xorAB = mbaXor(a, b, insertPt, depth - 1);
    base = BinaryOperator::Create(Instruction::Sub, dbl, xorAB, "", insertPt);
    break;
  }
  }
  // Add null-function noise (2-3 terms with random coefficients)
  return addNullNoise(base, a, b, insertPt, 2 + cryptoutils->get_range(2));
}

static Value *mbaSub(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Sub, a, b, "", insertPt);

  Value *base;
  switch (cryptoutils->get_range(4)) {
  default:
  case 0: {
    // a + (~b) + 1
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *add1 = mbaAdd(a, notB, insertPt, depth - 1);
    Constant *one = ConstantInt::get(a->getType(), 1);
    base = BinaryOperator::Create(Instruction::Add, add1, one, "", insertPt);
    break;
  }
  case 1: {
    // (a ^ b) - 2*(~a & b)
    Value *xorAB = mbaXor(a, b, insertPt, depth - 1);
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *andNAB = mbaAnd(notA, b, insertPt, depth - 1);
    Constant *two = ConstantInt::get(a->getType(), 2);
    Value *mul = BinaryOperator::Create(Instruction::Mul, andNAB, two, "", insertPt);
    base = BinaryOperator::Create(Instruction::Sub, xorAB, mul, "", insertPt);
    break;
  }
  case 2: {
    // (a & ~b) - (~a & b)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andANB = mbaAnd(a, notB, insertPt, depth - 1);
    Value *andNAB = mbaAnd(notA, b, insertPt, depth - 1);
    base = BinaryOperator::Create(Instruction::Sub, andANB, andNAB, "", insertPt);
    break;
  }
  case 3: {
    // 2*(a & ~b) - (a ^ b)
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andANB = mbaAnd(a, notB, insertPt, depth - 1);
    Constant *two = ConstantInt::get(a->getType(), 2);
    Value *dbl = BinaryOperator::Create(Instruction::Mul, andANB, two, "", insertPt);
    Value *xorAB = mbaXor(a, b, insertPt, depth - 1);
    base = BinaryOperator::Create(Instruction::Sub, dbl, xorAB, "", insertPt);
    break;
  }
  }
  return addNullNoise(base, a, b, insertPt, 2 + cryptoutils->get_range(2));
}

static Value *mbaXor(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);

  Value *base;
  switch (cryptoutils->get_range(4)) {
  default:
  case 0: {
    // (a | b) - (a & b)
    Value *orAB = mbaOr(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    base = BinaryOperator::Create(Instruction::Sub, orAB, andAB, "", insertPt);
    break;
  }
  case 1: {
    // (~a & b) | (a & ~b)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andNAB = mbaAnd(notA, b, insertPt, depth - 1);
    Value *andANB = mbaAnd(a, notB, insertPt, depth - 1);
    base = mbaOr(andNAB, andANB, insertPt, depth - 1);
    break;
  }
  case 2: {
    // (a + b) - 2*(a & b)
    Value *addAB = mbaAdd(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    Constant *two = ConstantInt::get(a->getType(), 2);
    Value *mul = BinaryOperator::Create(Instruction::Mul, andAB, two, "", insertPt);
    base = BinaryOperator::Create(Instruction::Sub, addAB, mul, "", insertPt);
    break;
  }
  case 3: {
    // (a | b) + (a | b) - a - b
    // = 2*(a|b) - a - b = 2*(a|b) - (a+b) = 2*(a|b) - (a^b) - 2*(a&b)
    // Simpler form: (a + b) - 2*(a & b)  (same as case 2, different path)
    // Use: a - 2*(a & b) + b
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    Constant *two = ConstantInt::get(a->getType(), 2);
    Value *and2 = BinaryOperator::Create(Instruction::Mul, andAB, two, "", insertPt);
    Value *sub = BinaryOperator::Create(Instruction::Sub, a, and2, "", insertPt);
    base = BinaryOperator::Create(Instruction::Add, sub, b, "", insertPt);
    break;
  }
  }
  return addNullNoise(base, a, b, insertPt, 2 + cryptoutils->get_range(2));
}

static Value *mbaAnd(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::And, a, b, "", insertPt);

  Value *base;
  switch (cryptoutils->get_range(4)) {
  default:
  case 0: {
    // (a | b) ^ (a ^ b)
    Value *orAB = BinaryOperator::Create(Instruction::Or, a, b, "", insertPt);
    Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);
    base = BinaryOperator::Create(Instruction::Xor, orAB, xorAB, "", insertPt);
    break;
  }
  case 1: {
    // ~(~a | ~b)  (De Morgan)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *orNN = BinaryOperator::Create(Instruction::Or, notA, notB, "", insertPt);
    base = BinaryOperator::CreateNot(orNN, "", insertPt);
    break;
  }
  case 2: {
    // a - (a & ~b)
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andANB = BinaryOperator::Create(Instruction::And, a, notB, "", insertPt);
    base = BinaryOperator::Create(Instruction::Sub, a, andANB, "", insertPt);
    break;
  }
  case 3: {
    // (a + b - (a ^ b)) / 2  =  (a + b - (a ^ b)) >> 1
    // Proof: a+b = (a^b) + 2*(a&b), so (a+b-(a^b)) = 2*(a&b), /2 = a&b
    Value *addAB = BinaryOperator::Create(Instruction::Add, a, b, "", insertPt);
    Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);
    Value *sub = BinaryOperator::Create(Instruction::Sub, addAB, xorAB, "", insertPt);
    Constant *one = ConstantInt::get(a->getType(), 1);
    base = BinaryOperator::Create(Instruction::LShr, sub, one, "", insertPt);
    break;
  }
  }
  return addNullNoise(base, a, b, insertPt, 2 + cryptoutils->get_range(2));
}

static Value *mbaOr(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Or, a, b, "", insertPt);

  Value *base;
  switch (cryptoutils->get_range(4)) {
  default:
  case 0: {
    // (a ^ b) | (a & b) — but use ADD since disjoint
    Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);
    Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", insertPt);
    base = BinaryOperator::Create(Instruction::Add, xorAB, andAB, "", insertPt);
    break;
  }
  case 1: {
    // ~(~a & ~b)  (De Morgan)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andNN = BinaryOperator::Create(Instruction::And, notA, notB, "", insertPt);
    base = BinaryOperator::CreateNot(andNN, "", insertPt);
    break;
  }
  case 2: {
    // (a + b) - (a & b)
    Value *addAB = BinaryOperator::Create(Instruction::Add, a, b, "", insertPt);
    Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", insertPt);
    base = BinaryOperator::Create(Instruction::Sub, addAB, andAB, "", insertPt);
    break;
  }
  case 3: {
    // a + (b & ~a) — adds the bits in b that aren't in a
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *andBNA = BinaryOperator::Create(Instruction::And, b, notA, "", insertPt);
    base = BinaryOperator::Create(Instruction::Add, a, andBNA, "", insertPt);
    break;
  }
  }
  return addNullNoise(base, a, b, insertPt, 2 + cryptoutils->get_range(2));
}

// ── Pass implementation ──

namespace {

struct MBAObfuscation : public FunctionPass {
  static char ID;
  bool flag;

  MBAObfuscation() : FunctionPass(ID) { this->flag = true; }
  MBAObfuscation(bool flag) : MBAObfuscation() { this->flag = flag; }

  bool runOnFunction(Function &F) override {
    Function *tmp = &F;
    if (!toObfuscate(flag, tmp, "mba"))
      return false;

    uint32_t depth = MBADepth;
    if (depth > 4) depth = 4;
    if (depth < 1) depth = 1;

    errs() << "Running MBA Obfuscation (depth=" << depth << ") On "
           << F.getName() << "\n";

    // Collect instructions first to avoid iterator invalidation
    std::vector<BinaryOperator *> candidates;
    for (Instruction &I : instructions(F)) {
      if (auto *BO = dyn_cast<BinaryOperator>(&I)) {
        // Only obfuscate integer operations (not float)
        if (!BO->getType()->isIntegerTy())
          continue;
        if (cryptoutils->get_range(100) >= MBAProbRate)
          continue;

        switch (BO->getOpcode()) {
        case Instruction::Add:
        case Instruction::Sub:
        case Instruction::Xor:
        case Instruction::And:
        case Instruction::Or:
          candidates.push_back(BO);
          break;
        default:
          break;
        }
      }
    }

    if (candidates.empty())
      return false;

    for (BinaryOperator *BO : candidates) {
      Value *a = BO->getOperand(0);
      Value *b = BO->getOperand(1);
      Value *result = nullptr;

      switch (BO->getOpcode()) {
      case Instruction::Add:
        result = mbaAdd(a, b, BO, depth);
        break;
      case Instruction::Sub:
        result = mbaSub(a, b, BO, depth);
        break;
      case Instruction::Xor:
        result = mbaXor(a, b, BO, depth);
        break;
      case Instruction::And:
        result = mbaAnd(a, b, BO, depth);
        break;
      case Instruction::Or:
        result = mbaOr(a, b, BO, depth);
        break;
      default:
        continue;
      }

      if (result) {
        BO->replaceAllUsesWith(result);
        ++MBATotal;
      }
    }

    // Erase replaced instructions (reverse order to handle dependencies)
    for (auto it = candidates.rbegin(); it != candidates.rend(); ++it) {
      BinaryOperator *BO = *it;
      if (BO->use_empty())
        BO->eraseFromParent();
    }

    return true;
  }
};

} // namespace

char MBAObfuscation::ID = 0;
INITIALIZE_PASS(MBAObfuscation, "mbaobf", "Enable MBA Obfuscation.", false,
                false)
FunctionPass *llvm::createMBAObfuscationPass(bool flag) {
  return new MBAObfuscation(flag);
}
