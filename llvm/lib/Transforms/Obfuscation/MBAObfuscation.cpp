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

// ── MBA core: recursive substitution ──

// Forward declarations
static Value *mbaAdd(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaSub(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaXor(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaAnd(Value *a, Value *b, Instruction *insertPt, uint32_t depth);
static Value *mbaOr(Value *a, Value *b, Instruction *insertPt, uint32_t depth);

// Noise injection: returns (result + noise - noise) with random constant
static Value *injectNoise(Value *val, Instruction *insertPt) {
  ConstantInt *noise = ConstantInt::get(val->getType(), cryptoutils->get_uint64_t());
  BinaryOperator *added = BinaryOperator::Create(Instruction::Add, val, noise, "", insertPt);
  return BinaryOperator::Create(Instruction::Sub, added, noise, "", insertPt);
}

// ── ADD substitutions ──
// a + b = (a ^ b) + 2*(a & b)
// a + b = (a | b) + (a & b)
// a + b = a - (~b) - 1
static Value *mbaAdd(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Add, a, b, "", insertPt);

  switch (cryptoutils->get_range(3)) {
  case 0: {
    // (a ^ b) + 2*(a & b)
    Value *xorAB = mbaXor(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    ConstantInt *two = ConstantInt::get(a->getType(), 2);
    Value *mul = BinaryOperator::Create(Instruction::Mul, andAB, two, "", insertPt);
    return BinaryOperator::Create(Instruction::Add, xorAB, mul, "", insertPt);
  }
  case 1: {
    // (a | b) + (a & b)
    Value *orAB = mbaOr(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    return BinaryOperator::Create(Instruction::Add, orAB, andAB, "", insertPt);
  }
  case 2: {
    // a - (~b) - 1
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *sub1 = mbaSub(a, notB, insertPt, depth - 1);
    ConstantInt *one = ConstantInt::get(a->getType(), 1);
    return BinaryOperator::Create(Instruction::Sub, sub1, one, "", insertPt);
  }
  }
  llvm_unreachable("bad rng");
}

// ── SUB substitutions ──
// a - b = a + (~b) + 1
// a - b = (a ^ b) - 2*(~a & b)
// a - b = (a & ~b) - (~a & b)
static Value *mbaSub(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Sub, a, b, "", insertPt);

  switch (cryptoutils->get_range(3)) {
  case 0: {
    // a + (~b) + 1
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *add1 = mbaAdd(a, notB, insertPt, depth - 1);
    ConstantInt *one = ConstantInt::get(a->getType(), 1);
    return BinaryOperator::Create(Instruction::Add, add1, one, "", insertPt);
  }
  case 1: {
    // (a ^ b) - 2*(~a & b)
    Value *xorAB = mbaXor(a, b, insertPt, depth - 1);
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *andNAB = mbaAnd(notA, b, insertPt, depth - 1);
    ConstantInt *two = ConstantInt::get(a->getType(), 2);
    Value *mul = BinaryOperator::Create(Instruction::Mul, andNAB, two, "", insertPt);
    return BinaryOperator::Create(Instruction::Sub, xorAB, mul, "", insertPt);
  }
  case 2: {
    // (a & ~b) - (~a & b)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andANB = mbaAnd(a, notB, insertPt, depth - 1);
    Value *andNAB = mbaAnd(notA, b, insertPt, depth - 1);
    return BinaryOperator::Create(Instruction::Sub, andANB, andNAB, "", insertPt);
  }
  }
  llvm_unreachable("bad rng");
}

// ── XOR substitutions ──
// a ^ b = (a | b) - (a & b)
// a ^ b = (~a & b) | (a & ~b)
// a ^ b = (a + b) - 2*(a & b)
static Value *mbaXor(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);

  switch (cryptoutils->get_range(3)) {
  case 0: {
    // (a | b) - (a & b)
    Value *orAB = mbaOr(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    return BinaryOperator::Create(Instruction::Sub, orAB, andAB, "", insertPt);
  }
  case 1: {
    // (~a & b) | (a & ~b)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andNAB = mbaAnd(notA, b, insertPt, depth - 1);
    Value *andANB = mbaAnd(a, notB, insertPt, depth - 1);
    return mbaOr(andNAB, andANB, insertPt, depth - 1);
  }
  case 2: {
    // (a + b) - 2*(a & b)
    Value *addAB = mbaAdd(a, b, insertPt, depth - 1);
    Value *andAB = mbaAnd(a, b, insertPt, depth - 1);
    ConstantInt *two = ConstantInt::get(a->getType(), 2);
    Value *mul = BinaryOperator::Create(Instruction::Mul, andAB, two, "", insertPt);
    return BinaryOperator::Create(Instruction::Sub, addAB, mul, "", insertPt);
  }
  }
  llvm_unreachable("bad rng");
}

// ── AND substitutions ──
// a & b = (a | b) ^ (a ^ b)
// a & b = (a + b - (a ^ b)) >> 1  -- only for depth 0/1 to avoid complexity
// a & b = ~(~a | ~b)
static Value *mbaAnd(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::And, a, b, "", insertPt);

  switch (cryptoutils->get_range(3)) {
  case 0: {
    // (a | b) ^ (a ^ b)
    Value *orAB = BinaryOperator::Create(Instruction::Or, a, b, "", insertPt);
    Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);
    return BinaryOperator::Create(Instruction::Xor, orAB, xorAB, "", insertPt);
  }
  case 1: {
    // ~(~a | ~b)  (De Morgan)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *orNN = BinaryOperator::Create(Instruction::Or, notA, notB, "", insertPt);
    return BinaryOperator::CreateNot(orNN, "", insertPt);
  }
  case 2: {
    // a - (a & ~b)  →  a & b
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andANB = BinaryOperator::Create(Instruction::And, a, notB, "", insertPt);
    return BinaryOperator::Create(Instruction::Sub, a, andANB, "", insertPt);
  }
  }
  llvm_unreachable("bad rng");
}

// ── OR substitutions ──
// a | b = (a ^ b) | (a & b)
// a | b = (a & b) + (a ^ b)
// a | b = ~(~a & ~b)
static Value *mbaOr(Value *a, Value *b, Instruction *insertPt, uint32_t depth) {
  if (depth == 0)
    return BinaryOperator::Create(Instruction::Or, a, b, "", insertPt);

  switch (cryptoutils->get_range(3)) {
  case 0: {
    // (a ^ b) | (a & b)
    Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);
    Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", insertPt);
    return BinaryOperator::Create(Instruction::Or, xorAB, andAB, "", insertPt);
  }
  case 1: {
    // (a & b) + (a ^ b)
    Value *andAB = BinaryOperator::Create(Instruction::And, a, b, "", insertPt);
    Value *xorAB = BinaryOperator::Create(Instruction::Xor, a, b, "", insertPt);
    return BinaryOperator::Create(Instruction::Add, andAB, xorAB, "", insertPt);
  }
  case 2: {
    // ~(~a & ~b)  (De Morgan)
    Value *notA = BinaryOperator::CreateNot(a, "", insertPt);
    Value *notB = BinaryOperator::CreateNot(b, "", insertPt);
    Value *andNN = BinaryOperator::Create(Instruction::And, notA, notB, "", insertPt);
    return BinaryOperator::CreateNot(andNN, "", insertPt);
  }
  }
  llvm_unreachable("bad rng");
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
        // Randomly inject noise (30% chance)
        if (cryptoutils->get_range(100) < 30)
          result = injectNoise(result, BO);

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
