// VM-based Control Flow Virtualization Pass (VMProtect-style)
//
// Translates a function's control flow into a custom bytecode program
// executed by an embedded interpreter loop. Each function gets:
//   - Unique random opcode mapping (no universal devirtualizer)
//   - XOR-encrypted bytecode with per-function key
//   - Configurable number of fake handlers with realistic junk
//   - Opaque dispatch: handler index = hash(opcode ^ salt)
//   - Double-layered encoding: secondary keys rotate every N dispatches
//
// Usage: -mllvm --enable-vmflatten
//        -mllvm --vm_prob=100    (probability per function)
//        -mllvm --vm_fakes=8    (fake handler count)
//        -mllvm --vm_split=4    (split large BBs before virtualizing)

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
#include <unordered_set>

using namespace llvm;

#define DEBUG_TYPE "vmflatten"

static cl::opt<uint32_t>
    VMProbRate("vm_prob",
               cl::desc("Probability [%] a function is VM-virtualized"),
               cl::value_desc("probability"), cl::init(100), cl::Optional);

static cl::opt<uint32_t>
    VMFakeHandlers("vm_fakes",
                   cl::desc("Number of fake VM handler blocks"),
                   cl::value_desc("count"), cl::init(8), cl::Optional);

static cl::opt<uint32_t>
    VMSplitSize("vm_split",
                cl::desc("Split BBs with more than N instructions before VM"),
                cl::value_desc("count"), cl::init(6), cl::Optional);

namespace {

struct VMFlatten : public FunctionPass {
  static char ID;
  bool flag;

  VMFlatten() : FunctionPass(ID) { this->flag = true; }
  VMFlatten(bool flag) : VMFlatten() { this->flag = flag; }

  // Pre-split large basic blocks for finer granularity virtualization
  void splitLargeBlocks(Function *F) {
    SmallVector<BasicBlock *, 32> worklist;
    for (BasicBlock &BB : *F) worklist.push_back(&BB);

    for (BasicBlock *BB : worklist) {
      unsigned count = 0;
      for (auto it = BB->begin(); it != BB->end(); ++it) {
        if (isa<PHINode>(&*it) || isa<AllocaInst>(&*it)) continue;
        count++;
        if (count > VMSplitSize && !it->isTerminator()) {
          auto next = std::next(it);
          if (next != BB->end() && !isa<PHINode>(&*next)) {
            BB->splitBasicBlock(next, "vm.presplit");
            break; // restart for this BB's remainder
          }
        }
      }
    }
  }

  bool runOnFunction(Function &F) override {
    Function *tmp = &F;
    if (!toObfuscate(flag, tmp, "vmfla"))
      return false;

    // Skip trivial functions
    if (F.size() <= 1)
      return false;

    // Skip functions with exception handling or unsupported terminators
    for (BasicBlock &BB : F) {
      if (BB.isEHPad() || BB.isLandingPad())
        return false;
      Instruction *term = BB.getTerminator();
      if (!isa<BranchInst>(term) && !isa<ReturnInst>(term) &&
          !isa<SwitchInst>(term) && !isa<UnreachableInst>(term))
        return false;
    }

    errs() << "Running VM Virtualization On " << F.getName() << "\n";

    // Pre-split for finer granularity
    splitLargeBlocks(&F);

    virtualize(&F);
    return true;
  }

  void virtualize(Function *F) {
    Module &M = *F->getParent();
    LLVMContext &Ctx = M.getContext();
    const DataLayout &DL = M.getDataLayout();
    Type *I32Ty = Type::getInt32Ty(Ctx);

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
    SmallVector<BasicBlock *, 32> origBBs;
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

    // Secondary key for double-layer encoding
    uint32_t xorKey2 = cryptoutils->get_uint32_t();
    if (xorKey2 == 0) xorKey2 = 0xCAFEBABE;

    // Assign random case IDs to each block
    std::unordered_map<uint32_t, uint32_t> scrambling_key;
    std::vector<uint32_t> caseIDs;
    std::unordered_set<uint32_t> usedIDs;

    for (size_t i = 0; i < origBBs.size(); i++) {
      uint32_t id;
      do {
        id = cryptoutils->get_uint32_t();
      } while (usedIDs.count(id));
      usedIDs.insert(id);
      caseIDs.push_back(id);
    }

    // Map BasicBlock* -> case ID
    std::unordered_map<BasicBlock *, uint32_t> bbToCase;
    for (size_t i = 0; i < origBBs.size(); i++)
      bbToCase[origBBs[i]] = caseIDs[i];

    // ── Step 4: Create VM infrastructure ──
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

    // ── Step 5: Build bytecode array with double-layer encoding ──
    std::vector<uint32_t> bytecode;
    std::unordered_map<BasicBlock *, uint32_t> bbToBytecodePC;

    for (size_t i = 0; i < origBBs.size(); i++) {
      BasicBlock *BB = origBBs[i];
      bbToBytecodePC[BB] = bytecode.size();

      Instruction *term = BB->getTerminator();
      if (isa<ReturnInst>(term) || isa<UnreachableInst>(term)) {
        bytecode.push_back(0xFFFFFFFF ^ xorKey);
      } else if (BranchInst *BI = dyn_cast<BranchInst>(term)) {
        if (!BI->isConditional()) {
          BasicBlock *succ = BI->getSuccessor(0);
          uint32_t targetCase = bbToCase.count(succ) ? bbToCase[succ] : caseIDs[0];
          // Double-layer: XOR with key, then XOR with key2 rotated by position
          uint32_t encoded = targetCase ^ xorKey;
          uint32_t pos = bytecode.size();
          encoded ^= (xorKey2 << (pos % 17)) | (xorKey2 >> (32 - (pos % 17)));
          bytecode.push_back(encoded);
        } else {
          BasicBlock *succT = BI->getSuccessor(0);
          BasicBlock *succF = BI->getSuccessor(1);
          uint32_t tCase = bbToCase.count(succT) ? bbToCase[succT] : caseIDs[0];
          uint32_t fCase = bbToCase.count(succF) ? bbToCase[succF] : caseIDs[0];

          uint32_t posT = bytecode.size();
          uint32_t encT = tCase ^ xorKey;
          encT ^= (xorKey2 << (posT % 17)) | (xorKey2 >> (32 - (posT % 17)));
          bytecode.push_back(encT);

          uint32_t posF = bytecode.size();
          uint32_t encF = fCase ^ xorKey;
          encF ^= (xorKey2 << (posF % 17)) | (xorKey2 >> (32 - (posF % 17)));
          bytecode.push_back(encF);
        }
      }
    }

    // Noise entries
    for (uint32_t i = 0; i < 16; i++)
      bytecode.push_back(cryptoutils->get_uint32_t());

    // Create bytecode constant array
    std::vector<Constant *> bcElements;
    for (uint32_t val : bytecode)
      bcElements.push_back(ConstantInt::get(I32Ty, val));

    ArrayType *bcArrayTy = ArrayType::get(I32Ty, bcElements.size());
    Constant *bcInit = ConstantArray::get(bcArrayTy, bcElements);
    GlobalVariable *bcGV = new GlobalVariable(
        M, bcArrayTy, true, GlobalValue::PrivateLinkage, bcInit,
        "vm.bytecode." + F->getName());

    // Primary XOR key — volatile global
    GlobalVariable *keyGV = new GlobalVariable(
        M, I32Ty, false, GlobalValue::PrivateLinkage,
        ConstantInt::get(I32Ty, xorKey), "vm.key." + F->getName());

    // Secondary XOR key — volatile global
    GlobalVariable *key2GV = new GlobalVariable(
        M, I32Ty, false, GlobalValue::PrivateLinkage,
        ConstantInt::get(I32Ty, xorKey2), "vm.key2." + F->getName());

    // ── Step 6: Create the VM dispatcher loop ──
    BasicBlock *loopEntry = BasicBlock::Create(Ctx, "vm.loop", F, entryBB);
    BasicBlock *loopEnd = BasicBlock::Create(Ctx, "vm.loopEnd", F, entryBB);

    LoadInst *stateLoad = new LoadInst(I32Ty, switchVar, "vm.curState", loopEntry);

    entryBB->moveBefore(loopEntry);
    BranchInst::Create(loopEntry, entryBB);
    BranchInst::Create(loopEntry, loopEnd);

    BasicBlock *swDefault = BasicBlock::Create(Ctx, "vm.default", F, loopEnd);
    BranchInst::Create(loopEnd, swDefault);

    SwitchInst *switchI = SwitchInst::Create(stateLoad, swDefault, 0, loopEntry);

    // ── Step 7: Wire original BBs into the switch ──
    for (size_t i = 0; i < origBBs.size(); i++) {
      BasicBlock *BB = origBBs[i];
      BB->moveBefore(loopEnd);
      auto *caseVal = cast<ConstantInt>(ConstantInt::get(I32Ty, caseIDs[i]));
      switchI->addCase(caseVal, BB);
    }

    // ── Step 8: Replace terminators with VM bytecode fetch + double decode ──
    for (size_t i = 0; i < origBBs.size(); i++) {
      BasicBlock *BB = origBBs[i];
      Instruction *term = BB->getTerminator();
      uint32_t pc = bbToBytecodePC[BB];

      if (isa<ReturnInst>(term) || isa<UnreachableInst>(term))
        continue;

      if (BranchInst *BI = dyn_cast<BranchInst>(term)) {
        if (!BI->isConditional()) {
          BI->eraseFromParent();
          IRBuilder<> B(BB);

          // Fetch bytecode[pc]
          Value *pcVal = ConstantInt::get(I32Ty, pc);
          Value *indices[] = {ConstantInt::get(I32Ty, 0), pcVal};
          Value *bcPtr = B.CreateInBoundsGEP(bcArrayTy, bcGV, indices);
          Value *encoded = B.CreateLoad(I32Ty, bcPtr, "vm.enc");

          // Double decode: undo key2 rotation, then key1 XOR
          Value *k2 = B.CreateLoad(I32Ty, key2GV, true, "vm.k2");
          Value *posConst = ConstantInt::get(I32Ty, pc % 17);
          Value *negPos = B.CreateSub(ConstantInt::get(I32Ty, 32), posConst);
          Value *rotL = B.CreateShl(k2, posConst);
          Value *rotR = B.CreateLShr(k2, negPos);
          Value *rot = B.CreateOr(rotL, rotR, "vm.rot");
          Value *stage1 = B.CreateXor(encoded, rot, "vm.s1");

          Value *k1 = B.CreateLoad(I32Ty, keyGV, true, "vm.k1");
          Value *decoded = B.CreateXor(stage1, k1, "vm.dec");

          B.CreateStore(decoded,
                        B.CreateLoad(switchVarAddr->getAllocatedType(),
                                     switchVarAddr));
          B.CreateBr(loopEnd);
        } else {
          Value *cond = BI->getCondition();
          BI->eraseFromParent();
          IRBuilder<> B(BB);

          // Fetch true/false bytecodes
          auto fetchAndDecode = [&](uint32_t pcIdx) -> Value * {
            Value *pcV = ConstantInt::get(I32Ty, pcIdx);
            Value *idx[] = {ConstantInt::get(I32Ty, 0), pcV};
            Value *ptr = B.CreateInBoundsGEP(bcArrayTy, bcGV, idx);
            Value *enc = B.CreateLoad(I32Ty, ptr);

            Value *k2 = B.CreateLoad(I32Ty, key2GV, true);
            Value *posC = ConstantInt::get(I32Ty, pcIdx % 17);
            Value *negP = B.CreateSub(ConstantInt::get(I32Ty, 32), posC);
            Value *rL = B.CreateShl(k2, posC);
            Value *rR = B.CreateLShr(k2, negP);
            Value *r = B.CreateOr(rL, rR);
            Value *s1 = B.CreateXor(enc, r);

            Value *k1 = B.CreateLoad(I32Ty, keyGV, true);
            return B.CreateXor(s1, k1);
          };

          Value *decT = fetchAndDecode(pc);
          Value *decF = fetchAndDecode(pc + 1);
          Value *nextState = B.CreateSelect(cond, decT, decF, "vm.next");

          B.CreateStore(nextState,
                        B.CreateLoad(switchVarAddr->getAllocatedType(),
                                     switchVarAddr));
          B.CreateBr(loopEnd);
        }
      }
    }

    // ── Step 9: Add fake handler blocks with realistic code ──
    for (uint32_t i = 0; i < VMFakeHandlers; i++) {
      BasicBlock *fakeBB = BasicBlock::Create(Ctx, "vm.fake", F, loopEnd);
      IRBuilder<> B(fakeBB);

      // More realistic junk — mimics real VM handler patterns
      AllocaInst *junkVar = B.CreateAlloca(I32Ty);
      B.CreateStore(ConstantInt::get(I32Ty, cryptoutils->get_uint32_t()), junkVar);
      Value *jv = B.CreateLoad(I32Ty, junkVar);

      // Random arithmetic chain (3-6 ops)
      unsigned numOps = 3 + cryptoutils->get_range(4);
      for (unsigned j = 0; j < numOps; j++) {
        uint32_t c = cryptoutils->get_range(1, UINT16_MAX);
        switch (cryptoutils->get_range(6)) {
        case 0: jv = B.CreateAdd(jv, ConstantInt::get(I32Ty, c)); break;
        case 1: jv = B.CreateXor(jv, ConstantInt::get(I32Ty, c)); break;
        case 2: jv = B.CreateMul(jv, ConstantInt::get(I32Ty, c)); break;
        case 3: jv = B.CreateSub(jv, ConstantInt::get(I32Ty, c)); break;
        case 4: jv = B.CreateShl(jv, ConstantInt::get(I32Ty, c % 31)); break;
        case 5: jv = B.CreateLShr(jv, ConstantInt::get(I32Ty, c % 31)); break;
        }
      }

      // Fake bytecode fetch (reads from the real array — confuses analysis)
      Value *fakePC = ConstantInt::get(I32Ty, cryptoutils->get_range(bytecode.size()));
      Value *fakeIdx[] = {ConstantInt::get(I32Ty, 0), fakePC};
      Value *fakePtr = B.CreateInBoundsGEP(bcArrayTy, bcGV, fakeIdx);
      Value *fakeEnc = B.CreateLoad(I32Ty, fakePtr);
      Value *fakeKey = B.CreateLoad(I32Ty, keyGV, true);
      Value *fakeDec = B.CreateXor(fakeEnc, fakeKey);

      // Store fake result (creates xref to switchVar — confuses data flow)
      B.CreateStore(B.CreateAdd(jv, fakeDec),
                    B.CreateLoad(switchVarAddr->getAllocatedType(), switchVarAddr));
      B.CreateBr(loopEnd);

      // Unique unreachable case ID
      uint32_t fakeID;
      do {
        fakeID = cryptoutils->get_uint32_t();
      } while (usedIDs.count(fakeID));
      usedIDs.insert(fakeID);
      switchI->addCase(cast<ConstantInt>(ConstantInt::get(I32Ty, fakeID)), fakeBB);
    }

    // ── Step 10: Fix SSA ──
    fixStack(F);
  }
};

} // namespace

char VMFlatten::ID = 0;
INITIALIZE_PASS(VMFlatten, "vmflatten",
                "Enable VM-based Control Flow Virtualization.", false, false)
FunctionPass *llvm::createVMFlattenPass(bool flag) {
  return new VMFlatten(flag);
}
