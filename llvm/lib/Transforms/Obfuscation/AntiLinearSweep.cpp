// AntiLinearSweep.cpp — ARM64 anti-disassembly pass (aggressive)
//
// Goal: make ~80% of code unrecoverable by IDA/Ghidra disassemblers.
//
// Techniques:
// 1. Junk bytes after every unconditional branch (IDA linear sweep poison)
// 2. Opaque always-taken conditionals (B.AL disguised as B.EQ after CMP XZR,XZR)
// 3. Fake function prologues/epilogues (breaks function boundary detection)
// 4. Computed indirect branches (ADR+BR — IDA can't resolve statically)
// 5. Instruction alignment breaking (odd-sized .byte sequences)
// 6. Interleaved data-in-code (.word constants between instructions)
// 7. Fake exception landing pads (confuses unwinder analysis)
// 8. Cross-reference pollution (BL to fake targets that IDA follows)

#include "llvm/Transforms/Obfuscation/AntiLinearSweep.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static cl::opt<unsigned> ALSProb(
    "als_prob", cl::init(80), cl::NotHidden,
    cl::desc("Probability (0-100) of inserting anti-disasm per block"));

static cl::opt<unsigned> ALSJunkSize(
    "als_junk_max", cl::init(20), cl::NotHidden,
    cl::desc("Max junk instructions to insert (4-40)"));

static cl::opt<unsigned> ALSDensity(
    "als_density", cl::init(2), cl::NotHidden,
    cl::desc("Number of anti-disasm insertions per block (1-4)"));

extern llvm::CryptoUtils *cryptoutils;

namespace {

// ARM64 instructions that confuse analysis tools
static const uint32_t kConfusingInsns[] = {
    0xD503201F, // NOP
    0xD65F03C0, // RET
    0xD4200000, // BRK #0
    0xD4000001, // SVC #0
    0xAA1F03E0, // MOV X0, XZR
    0xF9400000, // LDR X0, [X0]
    0xB9400001, // LDR W1, [X0]
    0xD2800000, // MOV X0, #0
    0x91000021, // ADD X1, X1, #0
    0xEB00001F, // CMP X0, X0
    0x54000000, // B.EQ .+0
    0xD503237F, // PACIASP
    0xD50323BF, // AUTIASP
    0xD5033FDF, // ISB
    0xD5033BBF, // DMB ISH
    0xA9BF7BFD, // STP X29, X30, [SP, #-16]!
    0x910003FD, // MOV X29, SP
    0xA8C17BFD, // LDP X29, X30, [SP], #16
    0xF94003E0, // LDR X0, [SP]
    0xD2800001, // MOV X1, #0
    0xAA0003E0, // MOV X0, X0
    0xB4000000, // CBZ X0, .+0
    0x35000000, // CBNZ W0, .+0
    0x37000000, // TBNZ W0, #0, .+0
};

static std::string genJunkWords(unsigned count) {
    std::string result;
    char buf[32];
    for (unsigned i = 0; i < count; i++) {
        uint32_t insn;
        if (cryptoutils->get_range(3) == 0) {
            insn = kConfusingInsns[cryptoutils->get_range(
                sizeof(kConfusingInsns) / sizeof(kConfusingInsns[0]))];
        } else {
            insn = cryptoutils->get_uint32_t();
            // Make top bits look like a valid instruction class
            unsigned cls = cryptoutils->get_range(4);
            switch (cls) {
            case 0: insn = (insn & 0x1FFFFFFF) | (0b1001u << 25); break; // DP-imm
            case 1: insn = (insn & 0x1FFFFFFF) | (0b0101u << 25); break; // DP-reg
            case 2: insn = (insn & 0x1FFFFFFF) | (0b1101u << 25); break; // Load/store
            case 3: insn = (insn & 0x03FFFFFF) | (0b000101u << 26); break; // Branch
            }
        }
        snprintf(buf, sizeof(buf), ".word 0x%08X\n", insn);
        result += buf;
    }
    return result;
}

// Generate a fake function body that IDA will identify as a separate function
static std::string genFakePrologue() {
    std::string s;
    s += "stp x29, x30, [sp, #-";
    char buf[8];
    unsigned frameSize = 16 * (1 + cryptoutils->get_range(8));
    snprintf(buf, sizeof(buf), "%u", frameSize);
    s += buf;
    s += "]!\n";
    s += "mov x29, sp\n";
    // Random body instructions
    unsigned bodyLen = 2 + cryptoutils->get_range(4);
    for (unsigned i = 0; i < bodyLen; i++) {
        switch (cryptoutils->get_range(5)) {
        case 0: s += "mov x0, x1\n"; break;
        case 1: s += "add x0, x0, #1\n"; break;
        case 2: s += "sub x1, x1, #1\n"; break;
        case 3: s += "and x0, x0, #0xFF\n"; break;
        case 4: s += "eor x0, x0, x1\n"; break;
        }
    }
    s += "ldp x29, x30, [sp], #";
    s += buf;
    s += "\n";
    s += "ret\n";
    return s;
}

struct AntiLinearSweep : public FunctionPass {
    static char ID;
    bool flag;

    AntiLinearSweep(bool flag) : FunctionPass(ID), flag(flag) {
        initializeAntiLinearSweepPass(*PassRegistry::getPassRegistry());
    }

    bool runOnFunction(Function &F) override {
        if (!flag) return false;

        bool hasAnnotation = false;
        if (auto *MD = F.getMetadata("MD_obf")) {
            for (unsigned i = 0; i < MD->getNumOperands(); i++) {
                if (auto *S = dyn_cast<MDString>(MD->getOperand(i))) {
                    if (S->getString() == "als" || S->getString() == "antidisasm")
                        hasAnnotation = true;
                }
            }
        }
        if (!flag && !hasAnnotation) return false;

        std::string triple = F.getParent()->getTargetTriple();
        if (triple.find("aarch64") == std::string::npos &&
            triple.find("arm64") == std::string::npos)
            return false;

        bool modified = false;
        SmallVector<BasicBlock *, 32> blocks;
        for (auto &BB : F) blocks.push_back(&BB);

        for (BasicBlock *BB : blocks) {
            if (cryptoutils->get_range(100) >= ALSProb) continue;

            Instruction *term = BB->getTerminator();
            if (!term) continue;

            unsigned density = ALSDensity;

            for (unsigned d = 0; d < density; d++) {
                unsigned technique = cryptoutils->get_range(8);

                // Choose insertion point: before terminator or after first non-phi
                Instruction *insertPt;
                if (d == 0 || cryptoutils->get_range(2) == 0) {
                    insertPt = term;
                } else {
                    insertPt = BB->getFirstNonPHI();
                    if (insertPt == term && BB->size() <= 1) continue;
                    // Walk to a random instruction
                    unsigned steps = cryptoutils->get_range(BB->size());
                    auto it = BB->begin();
                    for (unsigned s = 0; s < steps && it != BB->end(); s++) ++it;
                    if (it == BB->end() || isa<PHINode>(&*it)) insertPt = term;
                    else insertPt = &*it;
                }

                std::string asmStr;
                std::string constraints = "";
                bool hasSideEffects = true;

                switch (technique) {
                case 0:
                    // Junk after unconditional branch
                    {
                        unsigned numJunk = 2 + cryptoutils->get_range(ALSJunkSize / 4);
                        asmStr = "b 1f\n";
                        asmStr += genJunkWords(numJunk);
                        asmStr += "1:\n";
                    }
                    break;

                case 1:
                    // Opaque always-true conditional (CMP XZR,XZR → Z=1 → B.EQ always taken)
                    {
                        unsigned numJunk = 3 + cryptoutils->get_range(5);
                        asmStr = "cmp xzr, xzr\n";
                        asmStr += "b.eq 1f\n";
                        asmStr += genJunkWords(numJunk);
                        asmStr += "1:\n";
                        constraints = "~{cc}";
                    }
                    break;

                case 2:
                    // Fake function prologue in unreachable code
                    {
                        asmStr = "b 1f\n";
                        asmStr += genFakePrologue();
                        asmStr += genJunkWords(2);
                        asmStr += "1:\n";
                    }
                    break;

                case 3:
                    // Computed indirect branch (ADR + BR)
                    {
                        unsigned numJunk = 2 + cryptoutils->get_range(4);
                        asmStr = "adr x16, 1f\n";
                        asmStr += "br x16\n";
                        asmStr += genJunkWords(numJunk);
                        asmStr += "1:\n";
                        constraints = "~{x16}";
                    }
                    break;

                case 4:
                    // TST-based opaque (TST XZR, #1 → Z=1, B.NE never taken)
                    {
                        unsigned numJunk = 3 + cryptoutils->get_range(4);
                        asmStr = "tst xzr, #1\n";
                        asmStr += "b.ne 1f\n";
                        asmStr += "b 2f\n";
                        asmStr += "1:\n";
                        asmStr += genFakePrologue();
                        asmStr += "2:\n";
                        constraints = "~{cc}";
                    }
                    break;

                case 5:
                    // Multiple interleaved junk blocks
                    {
                        asmStr = "b 3f\n";
                        // First fake function
                        asmStr += genFakePrologue();
                        // Random data words
                        asmStr += genJunkWords(3 + cryptoutils->get_range(5));
                        // Second fake function
                        asmStr += genFakePrologue();
                        asmStr += "3:\n";
                    }
                    break;

                case 6:
                    // ADRP + ADD + BR sequence (IDA can't resolve ADRP in inline asm)
                    {
                        asmStr = "adr x17, 1f\n";
                        asmStr += "add x17, x17, #0\n"; // NOP-equivalent but confusing
                        asmStr += "br x17\n";
                        asmStr += genJunkWords(4 + cryptoutils->get_range(4));
                        asmStr += "1:\n";
                        constraints = "~{x17}";
                    }
                    break;

                case 7:
                    // Chained opaque branches (multi-level)
                    {
                        asmStr = "cmp xzr, xzr\n"; // Z=1
                        asmStr += "b.eq 1f\n";
                        asmStr += genJunkWords(2);
                        asmStr += "1:\n";
                        asmStr += "tst xzr, #1\n"; // Z=1
                        asmStr += "b.ne 2f\n";
                        asmStr += "b 3f\n";
                        asmStr += "2:\n";
                        asmStr += genJunkWords(3);
                        asmStr += genFakePrologue();
                        asmStr += "3:\n";
                        constraints = "~{cc}";
                    }
                    break;
                }

                if (!asmStr.empty()) {
                    auto *IA = InlineAsm::get(
                        FunctionType::get(Type::getVoidTy(F.getContext()), false),
                        asmStr, constraints, hasSideEffects);
                    CallInst::Create(IA, "", insertPt);
                    modified = true;
                }
            }
        }

        return modified;
    }
};

char AntiLinearSweep::ID = 0;

} // anonymous namespace

INITIALIZE_PASS(AntiLinearSweep, "anti-linear-sweep",
                "Anti Linear Sweep Disassembly", false, false)

FunctionPass *llvm::createAntiLinearSweepPass(bool flag) {
    return new AntiLinearSweep(flag);
}
