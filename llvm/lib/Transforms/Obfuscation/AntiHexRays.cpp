// AntiHexRays.cpp — Anti-decompiler pass targeting Hex-Rays microcode
//
// Goal: make Hex-Rays produce garbage, timeout, or crash on every function.
//
// Techniques:
// 1. Stack pointer desync — SP modifications Hex-Rays can't track
// 2. Opaque indirect calls — BLR to next insn = phantom function calls
// 3. Opaque constant replacement — constants → complex volatile expressions
// 4. Dead volatile stores — uncollapsible side effects
// 5. Fake conditional splits — opaque branches with trap dead code
// 6. Register aliasing — same value shuffled through registers via asm
// 7. Nested ternary chains — deep expression trees that blow up microcode
// 8. Mixed-width operations — i32/i64 casts that confuse type analysis

#include "llvm/Transforms/Obfuscation/AntiHexRays.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static cl::opt<unsigned> AHRProb(
    "ahr_prob", cl::init(60), cl::NotHidden,
    cl::desc("Probability (0-100) of applying anti-decompiler per block"));

static cl::opt<unsigned> AHRDepth(
    "ahr_depth", cl::init(3), cl::NotHidden,
    cl::desc("Nesting depth for opaque expression chains (1-6)"));

static cl::opt<unsigned> AHRDensity(
    "ahr_density", cl::init(2), cl::NotHidden,
    cl::desc("Number of anti-decompiler insertions per block (1-4)"));

namespace {

static GlobalVariable *getOrCreateOpaqueGlobal(Module &M, const std::string &name) {
    if (auto *GV = M.getGlobalVariable(name, true))
        return GV;
    auto *I64Ty = Type::getInt64Ty(M.getContext());
    auto *GV = new GlobalVariable(
        M, I64Ty, false, GlobalValue::PrivateLinkage,
        ConstantInt::get(I64Ty, cryptoutils->get_uint64_t()), name);
    GV->setAlignment(Align(8));
    return GV;
}

// Build opaque zero: always evaluates to 0 but Hex-Rays can't prove it
static Value *buildOpaqueZero(IRBuilder<> &B, GlobalVariable *opqVar, unsigned depth) {
    auto *I64Ty = B.getInt64Ty();
    Value *v = B.CreateLoad(I64Ty, opqVar);
    cast<LoadInst>(v)->setVolatile(true);

    // Layer 1: (v * v + v) & 1 == 0 always (n^2 + n is always even)
    Value *v2 = B.CreateMul(v, v);
    Value *v2pv = B.CreateAdd(v2, v);
    Value *result = B.CreateAnd(v2pv, B.getInt64(1));

    for (unsigned d = 1; d < depth; d++) {
        // Additional layers: each produces 0
        Value *a = B.CreateLoad(I64Ty, opqVar);
        cast<LoadInst>(a)->setVolatile(true);

        switch (d % 4) {
        case 0: {
            // (a | 1) * ((a | 1) - 1) is always even → & 1 == 0
            Value *a1 = B.CreateOr(a, B.getInt64(1));
            Value *a1m1 = B.CreateSub(a1, B.getInt64(1));
            Value *prod = B.CreateMul(a1, a1m1);
            result = B.CreateAdd(result, B.CreateAnd(prod, B.getInt64(1)));
            break;
        }
        case 1: {
            // a ^ a == 0 always, but volatile loads make it opaque
            Value *b = B.CreateLoad(I64Ty, opqVar);
            cast<LoadInst>(b)->setVolatile(true);
            // Use a - a instead (Hex-Rays might simplify x^x but not vol1-vol2)
            Value *sub = B.CreateSub(a, B.CreateLoad(I64Ty, opqVar));
            result = B.CreateAdd(result, sub);
            if (auto *SubI = dyn_cast<Instruction>(sub))
                if (auto *LI = dyn_cast<LoadInst>(SubI->getOperand(1)))
                    LI->setVolatile(false); // trick
            break;
        }
        case 2: {
            // (a * a) % 4 < 4 always, mapped to 0
            Value *sq = B.CreateMul(a, a);
            Value *mod4 = B.CreateAnd(sq, B.getInt64(3));
            // (mod4 >> 2) is always 0 (mod4 is 0 or 1)
            result = B.CreateAdd(result, B.CreateLShr(mod4, B.getInt64(2)));
            break;
        }
        case 3: {
            // |a & ~a| is always 0
            Value *nota = B.CreateXor(a, B.getInt64(-1));
            result = B.CreateAdd(result, B.CreateAnd(a, nota));
            break;
        }
        }
    }
    return result;
}

// Build an expression that always equals `val` but looks complex
static Value *buildOpaqueConstant(IRBuilder<> &B, uint64_t val,
                                  GlobalVariable *opqVar, unsigned depth) {
    Value *zero = buildOpaqueZero(B, opqVar, depth);
    return B.CreateAdd(zero, B.getInt64(val));
}

struct AntiHexRays : public FunctionPass {
    static char ID;
    bool flag;

    AntiHexRays(bool flag) : FunctionPass(ID), flag(flag) {
        initializeAntiHexRaysPass(*PassRegistry::getPassRegistry());
    }

    bool runOnFunction(Function &F) override {
        if (!flag) return false;

        bool hasAnnotation = false;
        if (auto *MD = F.getMetadata("MD_obf")) {
            for (unsigned i = 0; i < MD->getNumOperands(); i++) {
                if (auto *S = dyn_cast<MDString>(MD->getOperand(i))) {
                    if (S->getString() == "ahr" || S->getString() == "antihexrays")
                        hasAnnotation = true;
                }
            }
        }
        if (!flag && !hasAnnotation) return false;

        std::string triple = F.getParent()->getTargetTriple();
        bool isAArch64 = triple.find("aarch64") != std::string::npos ||
                         triple.find("arm64") != std::string::npos;

        Module &M = *F.getParent();
        auto &Ctx = F.getContext();
        std::string opqName = "ahr_opq_" + F.getName().str();
        GlobalVariable *opqVar = getOrCreateOpaqueGlobal(M, opqName);

        bool modified = false;
        SmallVector<BasicBlock *, 32> blocks;
        for (auto &BB : F) blocks.push_back(&BB);

        for (BasicBlock *BB : blocks) {
            if (cryptoutils->get_range(100) >= AHRProb) continue;

            for (unsigned d = 0; d < AHRDensity; d++) {
                Instruction *insertPt = BB->getFirstNonPHI();
                if (!insertPt) continue;

                // Walk to random position
                if (d > 0) {
                    unsigned steps = cryptoutils->get_range(BB->size());
                    auto it = BB->begin();
                    for (unsigned s = 0; s < steps && it != BB->end(); s++) ++it;
                    if (it != BB->end() && !isa<PHINode>(&*it))
                        insertPt = &*it;
                }

                unsigned technique = cryptoutils->get_range(8);

                switch (technique) {
                case 0:
                    // Stack pointer manipulation (AArch64)
                    if (isAArch64) {
                        unsigned off = 16 * (1 + cryptoutils->get_range(8));
                        char buf[256];
                        snprintf(buf, sizeof(buf),
                            "sub sp, sp, #%u\n"
                            "stp x16, x17, [sp]\n"
                            "mov x16, sp\n"
                            "add x16, x16, #%u\n"
                            "mov sp, x16\n",
                            off, off);
                        auto *IA = InlineAsm::get(
                            FunctionType::get(Type::getVoidTy(Ctx), false),
                            buf, "~{sp},~{x16},~{x17},~{memory}", true);
                        CallInst::Create(IA, "", insertPt);
                        modified = true;
                    }
                    break;

                case 1:
                    // Opaque indirect call to next instruction
                    if (isAArch64) {
                        auto *IA = InlineAsm::get(
                            FunctionType::get(Type::getVoidTy(Ctx), false),
                            "adr x16, 1f\n"
                            "blr x16\n"
                            "1:\n",
                            "~{x16},~{x30},~{cc}", true);
                        CallInst::Create(IA, "", insertPt);
                        modified = true;
                    }
                    break;

                case 2:
                    // Replace constant operands with opaque expressions
                    {
                        for (auto it = BB->begin(); it != BB->end(); ++it) {
                            if (auto *BO = dyn_cast<BinaryOperator>(&*it)) {
                                for (unsigned op = 0; op < 2; op++) {
                                    if (auto *CI = dyn_cast<ConstantInt>(BO->getOperand(op))) {
                                        if (CI->getBitWidth() == 64 &&
                                            cryptoutils->get_range(100) < 40) {
                                            IRBuilder<> B(BO);
                                            Value *opaque = buildOpaqueConstant(
                                                B, CI->getZExtValue(), opqVar, AHRDepth);
                                            BO->setOperand(op, opaque);
                                            modified = true;
                                            goto nextBlock; // one replacement per block per density
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;

                case 3:
                    // Dead volatile stores (Hex-Rays can't remove)
                    {
                        IRBuilder<> B(insertPt);
                        Value *zero = buildOpaqueZero(B, opqVar, AHRDepth);
                        auto *store = B.CreateStore(zero, opqVar);
                        store->setVolatile(true);
                        modified = true;
                    }
                    break;

                case 4:
                    // Fake conditional split with trap
                    {
                        IRBuilder<> B(insertPt);
                        auto *I64Ty = B.getInt64Ty();

                        Value *v = B.CreateLoad(I64Ty, opqVar);
                        cast<LoadInst>(v)->setVolatile(true);
                        // (v | 1) != 0 is ALWAYS true
                        Value *v_or = B.CreateOr(v, B.getInt64(1));
                        Value *cond = B.CreateICmpNE(v_or, B.getInt64(0));

                        Instruction *splitPt = insertPt->getNextNode();
                        if (!splitPt || splitPt == BB->getTerminator() ||
                            isa<PHINode>(splitPt)) break;

                        BasicBlock *trueBB = BB->splitBasicBlock(splitPt, "ahr.true");
                        BasicBlock *fakeBB = BasicBlock::Create(Ctx, "ahr.trap", &F, trueBB);

                        BB->getTerminator()->eraseFromParent();
                        B.SetInsertPoint(BB);
                        B.CreateCondBr(cond, trueBB, fakeBB);

                        // Fake block with realistic-looking dead code
                        B.SetInsertPoint(fakeBB);
                        // Dead volatile write
                        auto *deadStore = B.CreateStore(B.getInt64(0xDEADC0DE), opqVar);
                        deadStore->setVolatile(true);
                        if (isAArch64) {
                            auto *trap = InlineAsm::get(
                                FunctionType::get(Type::getVoidTy(Ctx), false),
                                "brk #0xF000", "", true);
                            B.CreateCall(trap);
                        }
                        B.CreateUnreachable();

                        modified = true;
                        goto nextBlock;
                    }
                    break;

                case 5:
                    // Register shuffle through inline asm (AArch64)
                    // Moves a value through multiple registers — Hex-Rays loses track
                    if (isAArch64) {
                        auto *IA = InlineAsm::get(
                            FunctionType::get(Type::getVoidTy(Ctx), false),
                            "mov x16, xzr\n"
                            "mov x17, x16\n"
                            "eor x16, x17, x16\n"  // x16 = 0
                            "add x17, x16, x17\n"  // x17 = x17
                            "sub x16, x17, x16\n", // x16 = x17
                            "~{x16},~{x17},~{cc}", true);
                        CallInst::Create(IA, "", insertPt);
                        modified = true;
                    }
                    break;

                case 6:
                    // Nested opaque zero chain (deep expression tree)
                    {
                        IRBuilder<> B(insertPt);
                        // Build very deep expression that equals 0
                        // Hex-Rays' expression simplifier gives up at depth ~10
                        Value *deep = buildOpaqueZero(B, opqVar, AHRDepth + 2);
                        // Use it in a comparison that's always true
                        Value *cmp = B.CreateICmpEQ(deep, B.getInt64(0));
                        // Branch on it — Hex-Rays must analyze the full expression
                        Instruction *nextI = insertPt->getNextNode();
                        if (nextI && nextI != BB->getTerminator() && !isa<PHINode>(nextI)) {
                            BasicBlock *contBB = BB->splitBasicBlock(nextI, "ahr.cont");
                            BasicBlock *deadBB = BasicBlock::Create(Ctx, "ahr.dead", &F, contBB);
                            BB->getTerminator()->eraseFromParent();
                            B.SetInsertPoint(BB);
                            B.CreateCondBr(cmp, contBB, deadBB);

                            IRBuilder<> DB(deadBB);
                            auto *dstore = DB.CreateStore(DB.getInt64(cryptoutils->get_uint64_t()), opqVar);
                            dstore->setVolatile(true);
                            DB.CreateBr(contBB);
                            modified = true;
                            goto nextBlock;
                        }
                    }
                    break;

                case 7:
                    // Mixed-width confusion — i32 truncation + sext
                    // Hex-Rays type analysis gets confused by width changes
                    {
                        IRBuilder<> B(insertPt);
                        auto *I64Ty = B.getInt64Ty();
                        auto *I32Ty = B.getInt32Ty();
                        Value *v = B.CreateLoad(I64Ty, opqVar);
                        cast<LoadInst>(v)->setVolatile(true);
                        // Trunc to i32, then sext back — produces same value
                        // for values < 2^31, but Hex-Rays shows explicit casts
                        Value *trunc = B.CreateTrunc(v, I32Ty);
                        Value *sext = B.CreateSExt(trunc, I64Ty);
                        Value *xor1 = B.CreateXor(v, sext);
                        // High bits are different → xor1 != 0 (usually)
                        // But we don't use the result meaningfully
                        auto *store = B.CreateStore(xor1, opqVar);
                        store->setVolatile(true);
                        modified = true;
                    }
                    break;
                }
            }
            nextBlock:;
        }

        return modified;
    }
};

char AntiHexRays::ID = 0;

} // anonymous namespace

INITIALIZE_PASS(AntiHexRays, "anti-hexrays",
                "Anti Hex-Rays Decompiler", false, false)

FunctionPass *llvm::createAntiHexRaysPass(bool flag) {
    return new AntiHexRays(flag);
}
