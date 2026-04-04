// VM-based Control Flow Virtualization Pass
//
// Translates a function's basic blocks into a custom bytecode program
// executed by an embedded interpreter loop. Each function gets a unique
// random opcode mapping, making static analysis extremely difficult.
//
// Architecture:
//   1. Lower all branches to an explicit switch dispatcher (like CFF)
//   2. For each original BB, encode its "case id" into bytecode
//   3. Replace the switch with a VM interpreter that fetches opcodes
//      from a bytecode array, decodes them through a per-function
//      XOR key, and dispatches to handler blocks
//   4. Add fake handlers with dead code to confuse analysis
//
// Usage: -mllvm --enable-vmflatten -mllvm --vm_prob=50

#include "llvm/Transforms/Obfuscation/VMFlatten.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/LowerSwitch.h"
#include <algorithm>
#include <vector>
#include <unordered_map>

using namespace llvm;

#define DEBUG_TYPE "vmflatten"

static cl::opt<uint32_t>
    VMProbRate("vm_prob",
               cl::desc("Probability [%] a function is VM-virtualized"),
               cl::value_desc("probability"), cl::init(100), cl::Optional);

static cl::opt<uint32_t>
    VMFakeHandlers("vm_fakes",
                   cl::desc("Number of fake VM handler blocks"),
                   cl::value_desc("count"), cl::init(4), cl::Optional);

namespace {

// ── VM Opcode definitions ──
// These are logical opcodes; actual encoding is XOR'd with a per-function key.
enum VMOpcode : uint8_t {
  VM_NOP = 0x00,
  VM_GOTO = 0x01,      // unconditional jump: operand = target block index
  VM_BRANCH = 0x02,    // conditional: operand = true_idx, next byte = false_idx
  VM_HALT = 0x03,      // function return
  VM_DECODE = 0x04,    // decode next opcode with secondary key
};

struct VMFlatten : public FunctionPass {
  static char ID;
  bool flag;

  VMFlatten() : FunctionPass(ID) { this->flag = true; }
  VMFlatten(bool flag) : VMFlatten() { this->flag = flag; }

  bool runOnFunction(Function &F) override {
    Function *tmp = &F;
    if (!toObfuscate(flag, tmp, "vmfla"))
      return false;

    // Skip trivial functions
    if (F.size() <= 2)
      return false;

    // Skip functions with exception handling
    for (BasicBlock &BB : F) {
      if (BB.isEHPad() || BB.isLandingPad())
        return false;
      // Only handle branch and return terminators
      if (!isa<BranchInst>(BB.getTerminator()) &&
          !isa<ReturnInst>(BB.getTerminator()))
        return false;
    }

    errs() << "Running VM Virtualization On " << F.getName() << "\n";
    virtualize(&F);
    return true;
  }

  void virtualize(Function *F) {
    Module &M = *F->getParent();
    LLVMContext &Ctx = M.getContext();
    const DataLayout &DL = M.getDataLayout();
    Type *I32Ty = Type::getInt32Ty(Ctx);
    Type *I8Ty = Type::getInt8Ty(Ctx);

    // ── Step 1: Lower switches to branches ──
    {
      PassBuilder PB;
      FunctionAnalysisManager FAM;
      FunctionPassManager FPM;
      PB.registerFunctionAnalyses(FAM);
      FPM.addPass(LowerSwitchPass());
      FPM.run(*F, FAM);
    }

    // ── Step 2: Collect original basic blocks ──
    SmallVector<BasicBlock *, 16> origBBs;
    for (BasicBlock &BB : *F)
      origBBs.push_back(&BB);

    if (origBBs.size() <= 1)
      return;

    // Separate entry block
    BasicBlock *entryBB = origBBs[0];
    origBBs.erase(origBBs.begin());

    // If entry block ends with conditional branch, split it
    if (BranchInst *br = dyn_cast<BranchInst>(entryBB->getTerminator())) {
      if (br->isConditional() || br->getNumSuccessors() > 1) {
        BasicBlock::iterator i = entryBB->end();
        --i;
        if (entryBB->size() > 1)
          --i;
        BasicBlock *splitBB = entryBB->splitBasicBlock(i, "entry.split");
        origBBs.insert(origBBs.begin(), splitBB);
      }
    }

    // ── Step 3: Generate per-function random keys ──
    uint32_t xorKey = cryptoutils->get_uint32_t();
    if (xorKey == 0) xorKey = 0xDEADBEEF;

    // Assign random case IDs to each block
    std::unordered_map<uint32_t, uint32_t> scrambling_key;
    std::vector<uint32_t> caseIDs;
    for (size_t i = 0; i < origBBs.size(); i++) {
      uint32_t id = cryptoutils->scramble32(i, scrambling_key);
      caseIDs.push_back(id);
    }

    // Map BasicBlock* -> case ID
    std::unordered_map<BasicBlock *, uint32_t> bbToCase;
    for (size_t i = 0; i < origBBs.size(); i++)
      bbToCase[origBBs[i]] = caseIDs[i];

    // ── Step 4: Create VM infrastructure ──
    // Allocate: switchVar (current state), PC (bytecode index), xorKeyVar
    Instruction *oldTerm = entryBB->getTerminator();

    AllocaInst *switchVar = new AllocaInst(I32Ty, DL.getAllocaAddrSpace(),
                                           "vm.state", oldTerm);
    AllocaInst *switchVarAddr = new AllocaInst(
        PointerType::get(I32Ty, DL.getAllocaAddrSpace()),
        DL.getAllocaAddrSpace(), "vm.stateaddr", BasicBlock::iterator(oldTerm));
    AllocaInst *pcVar = new AllocaInst(I32Ty, DL.getAllocaAddrSpace(),
                                       "vm.pc", oldTerm);

    oldTerm->eraseFromParent();

    // Initialize state to first block's case ID
    new StoreInst(ConstantInt::get(I32Ty, caseIDs[0]), switchVar, entryBB);
    new StoreInst(switchVar, switchVarAddr, entryBB);
    new StoreInst(ConstantInt::get(I32Ty, 0), pcVar, entryBB);

    // ── Step 5: Build bytecode array ──
    // Bytecode layout: each entry is (encoded_case_id ^ xorKey)
    // The VM loads bytecode[pc], XORs with key, and uses result as next state
    std::vector<uint32_t> bytecode;

    // Build a mapping: for each original BB, store the bytecode offset
    // where its "next state" entries begin
    std::unordered_map<BasicBlock *, uint32_t> bbToBytecodePC;

    for (size_t i = 0; i < origBBs.size(); i++) {
      BasicBlock *BB = origBBs[i];
      bbToBytecodePC[BB] = bytecode.size();

      Instruction *term = BB->getTerminator();
      if (ReturnInst *RI = dyn_cast<ReturnInst>(term)) {
        // Halt: encode a special sentinel
        bytecode.push_back(0xFFFFFFFF ^ xorKey);
      } else if (BranchInst *BI = dyn_cast<BranchInst>(term)) {
        if (!BI->isConditional()) {
          // Unconditional: encode target case ID
          BasicBlock *succ = BI->getSuccessor(0);
          uint32_t targetCase = bbToCase.count(succ) ? bbToCase[succ] : caseIDs[0];
          bytecode.push_back(targetCase ^ xorKey);
        } else {
          // Conditional: encode true_case, false_case
          BasicBlock *succT = BI->getSuccessor(0);
          BasicBlock *succF = BI->getSuccessor(1);
          uint32_t tCase = bbToCase.count(succT) ? bbToCase[succT] : caseIDs[0];
          uint32_t fCase = bbToCase.count(succF) ? bbToCase[succF] : caseIDs[0];
          bytecode.push_back(tCase ^ xorKey);
          bytecode.push_back(fCase ^ xorKey);
        }
      }
    }

    // Add noise entries at the end to confuse analysis
    for (uint32_t i = 0; i < 8; i++)
      bytecode.push_back(cryptoutils->get_uint32_t());

    // Create the bytecode as a constant array in the module
    std::vector<Constant *> bcElements;
    for (uint32_t val : bytecode)
      bcElements.push_back(ConstantInt::get(I32Ty, val));

    ArrayType *bcArrayTy = ArrayType::get(I32Ty, bcElements.size());
    Constant *bcInit = ConstantArray::get(bcArrayTy, bcElements);
    GlobalVariable *bcGV = new GlobalVariable(
        M, bcArrayTy, true, GlobalValue::PrivateLinkage, bcInit,
        "vm.bytecode." + F->getName());

    // XOR key as a volatile global (prevents constant propagation)
    GlobalVariable *keyGV = new GlobalVariable(
        M, I32Ty, false, GlobalValue::PrivateLinkage,
        ConstantInt::get(I32Ty, xorKey), "vm.key." + F->getName());

    // ── Step 6: Create the VM dispatcher loop ──
    BasicBlock *loopEntry = BasicBlock::Create(Ctx, "vm.loop", F, entryBB);
    BasicBlock *loopEnd = BasicBlock::Create(Ctx, "vm.loopEnd", F, entryBB);

    // Load current state
    LoadInst *stateLoad = new LoadInst(I32Ty, switchVar, "vm.curState", loopEntry);

    // Entry block jumps to loop
    entryBB->moveBefore(loopEntry);
    BranchInst::Create(loopEntry, entryBB);

    // Loop end jumps back to loop
    BranchInst::Create(loopEntry, loopEnd);

    // Default case
    BasicBlock *swDefault = BasicBlock::Create(Ctx, "vm.default", F, loopEnd);
    BranchInst::Create(loopEnd, swDefault);

    // Create the main dispatch switch
    SwitchInst *switchI = SwitchInst::Create(stateLoad, swDefault, 0, loopEntry);

    // ── Step 7: Wire original BBs into the switch ──
    for (size_t i = 0; i < origBBs.size(); i++) {
      BasicBlock *BB = origBBs[i];
      BB->moveBefore(loopEnd);

      ConstantInt *caseVal = ConstantInt::get(I32Ty, caseIDs[i]);
      switchI->addCase(caseVal, BB);
    }

    // ── Step 8: Replace terminators with VM bytecode fetch + state update ──
    for (size_t i = 0; i < origBBs.size(); i++) {
      BasicBlock *BB = origBBs[i];
      Instruction *term = BB->getTerminator();
      uint32_t pc = bbToBytecodePC[BB];

      if (isa<ReturnInst>(term)) {
        // Return blocks stay as-is — no state update needed
        continue;
      }

      if (BranchInst *BI = dyn_cast<BranchInst>(term)) {
        if (!BI->isConditional()) {
          // Fetch bytecode[pc], XOR with key → next state
          BI->eraseFromParent();
          IRBuilder<> B(BB);

          Value *pcVal = ConstantInt::get(I32Ty, pc);
          Value *indices[] = {ConstantInt::get(I32Ty, 0), pcVal};
          Value *bcPtr = B.CreateInBoundsGEP(bcArrayTy, bcGV, indices, "vm.bc.ptr");
          Value *encoded = B.CreateLoad(I32Ty, bcPtr, "vm.encoded");
          Value *key = B.CreateLoad(I32Ty, keyGV, true, "vm.key"); // volatile
          Value *decoded = B.CreateXor(encoded, key, "vm.decoded");

          // Store decoded state
          B.CreateStore(decoded,
                        B.CreateLoad(switchVarAddr->getAllocatedType(),
                                     switchVarAddr, "vm.saddr"));
          B.CreateBr(loopEnd);
        } else {
          // Conditional branch: select between bytecode[pc] and bytecode[pc+1]
          Value *cond = BI->getCondition();
          BI->eraseFromParent();
          IRBuilder<> B(BB);

          // Load true case
          Value *pcTrue = ConstantInt::get(I32Ty, pc);
          Value *idxT[] = {ConstantInt::get(I32Ty, 0), pcTrue};
          Value *ptrT = B.CreateInBoundsGEP(bcArrayTy, bcGV, idxT, "vm.bc.t");
          Value *encT = B.CreateLoad(I32Ty, ptrT, "vm.enc.t");

          // Load false case
          Value *pcFalse = ConstantInt::get(I32Ty, pc + 1);
          Value *idxF[] = {ConstantInt::get(I32Ty, 0), pcFalse};
          Value *ptrF = B.CreateInBoundsGEP(bcArrayTy, bcGV, idxF, "vm.bc.f");
          Value *encF = B.CreateLoad(I32Ty, ptrF, "vm.enc.f");

          // Decode
          Value *key = B.CreateLoad(I32Ty, keyGV, true, "vm.key");
          Value *decT = B.CreateXor(encT, key, "vm.dec.t");
          Value *decF = B.CreateXor(encF, key, "vm.dec.f");

          // Select based on condition
          Value *nextState = B.CreateSelect(cond, decT, decF, "vm.next");

          B.CreateStore(nextState,
                        B.CreateLoad(switchVarAddr->getAllocatedType(),
                                     switchVarAddr, "vm.saddr"));
          B.CreateBr(loopEnd);
        }
      }
    }

    // ── Step 9: Add fake handler blocks ──
    for (uint32_t i = 0; i < VMFakeHandlers; i++) {
      BasicBlock *fakeBB = BasicBlock::Create(Ctx, "vm.fake", F, loopEnd);
      IRBuilder<> B(fakeBB);

      // Generate random junk computation
      AllocaInst *junkVar = B.CreateAlloca(I32Ty, nullptr, "vm.fjunk");
      B.CreateStore(ConstantInt::get(I32Ty, cryptoutils->get_uint32_t()), junkVar);
      Value *jv = B.CreateLoad(I32Ty, junkVar, "vm.fload");

      // Random arithmetic chain
      for (int j = 0; j < 2 + (int)cryptoutils->get_range(3); j++) {
        uint32_t c = cryptoutils->get_range(1, UINT16_MAX);
        switch (cryptoutils->get_range(4)) {
        case 0: jv = B.CreateAdd(jv, ConstantInt::get(I32Ty, c), "vm.fop"); break;
        case 1: jv = B.CreateXor(jv, ConstantInt::get(I32Ty, c), "vm.fop"); break;
        case 2: jv = B.CreateMul(jv, ConstantInt::get(I32Ty, c), "vm.fop"); break;
        case 3: jv = B.CreateSub(jv, ConstantInt::get(I32Ty, c), "vm.fop"); break;
        }
      }
      B.CreateStore(jv, junkVar);

      // Jump back into the loop
      B.CreateBr(loopEnd);

      // Add a random case ID to the switch (unreachable)
      uint32_t fakeID = cryptoutils->get_uint32_t();
      // Ensure no collision with real cases
      bool collision = true;
      while (collision) {
        collision = false;
        for (uint32_t id : caseIDs) {
          if (id == fakeID) {
            fakeID = cryptoutils->get_uint32_t();
            collision = true;
            break;
          }
        }
      }
      switchI->addCase(ConstantInt::get(I32Ty, fakeID), fakeBB);
    }

    // ── Step 10: Fix SSA (demote to stack for cross-block references) ──
    errs() << "VM: Fixing Stack for " << F->getName() << "\n";
    fixStack(F);
    errs() << "VM: Done\n";
  }
};

} // namespace

char VMFlatten::ID = 0;
INITIALIZE_PASS(VMFlatten, "vmflatten",
                "Enable VM-based Control Flow Virtualization.", false, false)
FunctionPass *llvm::createVMFlattenPass(bool flag) {
  return new VMFlatten(flag);
}
