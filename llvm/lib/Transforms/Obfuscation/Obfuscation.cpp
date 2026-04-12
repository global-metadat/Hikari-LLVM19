// For open-source license, please refer to
// [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
/*
  Hikari 's own "Pass Scheduler".
  Because currently there is no way to add dependency to transform passes
  Ref : http://lists.llvm.org/pipermail/llvm-dev/2011-February/038109.html
*/
#include "llvm/Transforms/Obfuscation/Obfuscation.h"
#include "llvm/Transforms/Obfuscation/MBAObfuscation.h"
#include "llvm/Transforms/Obfuscation/OpaquePredicates.h"
#include "llvm/Transforms/Obfuscation/VMFlatten.h"
#include "llvm/Transforms/Obfuscation/AntiLinearSweep.h"
#include "llvm/Transforms/Obfuscation/AntiHexRays.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Format.h"
#include <cstdlib>

using namespace llvm;

// Begin Obfuscator Options
static cl::opt<bool>
    EnableIRObfusaction("hikari", cl::init(false), cl::NotHidden,
                        cl::desc("Enable IR Code Obfuscation."),
                        cl::ZeroOrMore);
static cl::opt<uint64_t> AesSeed("aesSeed", cl::init(0x1337),
                                 cl::desc("seed for the PRNG"));
static cl::opt<uint64_t>
    ObfSeed("obf-seed", cl::init(0),
            cl::desc("Deterministic seed for obfuscation PRNG. When non-zero, "
                     "overrides -aesSeed and time-based seeding. Use the same "
                     "value across builds for reproducible obfuscated output."));
static cl::opt<bool> EnableAntiClassDump("enable-acdobf", cl::init(false),
                                         cl::NotHidden,
                                         cl::desc("Enable AntiClassDump."));
static cl::opt<bool> EnableAntiHooking("enable-antihook", cl::init(false),
                                       cl::NotHidden,
                                       cl::desc("Enable AntiHooking."));
static cl::opt<bool> EnableAntiDebugging("enable-adb", cl::init(false),
                                         cl::NotHidden,
                                         cl::desc("Enable AntiDebugging."));
static cl::opt<bool>
    EnableBogusControlFlow("enable-bcfobf", cl::init(false), cl::NotHidden,
                           cl::desc("Enable BogusControlFlow."));
static cl::opt<bool> EnableFlattening("enable-cffobf", cl::init(false),
                                      cl::NotHidden,
                                      cl::desc("Enable Flattening."));
static cl::opt<bool>
    EnableBasicBlockSplit("enable-splitobf", cl::init(false), cl::NotHidden,
                          cl::desc("Enable BasicBlockSpliting."));
static cl::opt<bool>
    EnableSubstitution("enable-subobf", cl::init(false), cl::NotHidden,
                       cl::desc("Enable Instruction Substitution."));
static cl::opt<bool> EnableAllObfuscation("enable-allobf", cl::init(false),
                                          cl::NotHidden,
                                          cl::desc("Enable All Obfuscation."));
static cl::opt<bool> EnableFunctionCallObfuscate(
    "enable-fco", cl::init(false), cl::NotHidden,
    cl::desc("Enable Function CallSite Obfuscation."));
static cl::opt<bool>
    EnableStringEncryption("enable-strcry", cl::init(false), cl::NotHidden,
                           cl::desc("Enable String Encryption."));
static cl::opt<bool>
    EnableConstantEncryption("enable-constenc", cl::init(false), cl::NotHidden,
                             cl::desc("Enable Constant Encryption."));
static cl::opt<bool>
    EnableIndirectBranching("enable-indibran", cl::init(false), cl::NotHidden,
                            cl::desc("Enable Indirect Branching."));
static cl::opt<bool>
    EnableFunctionWrapper("enable-funcwra", cl::init(false), cl::NotHidden,
                          cl::desc("Enable Function Wrapper."));
static cl::opt<bool>
    EnableMBAObfuscation("enable-mbaobf", cl::init(false), cl::NotHidden,
                         cl::desc("Enable MBA Obfuscation."));
static cl::opt<bool>
    EnableOpaquePredicates("enable-opqpred", cl::init(false), cl::NotHidden,
                           cl::desc("Enable Strong Opaque Predicates."));
static cl::opt<bool>
    EnableVMFlatten("enable-vmflatten", cl::init(false), cl::NotHidden,
                    cl::desc("Enable VM-based Control Flow Virtualization."));
static cl::opt<bool>
    EnableAntiLinearSweep("enable-antidisasm", cl::init(false), cl::NotHidden,
                          cl::desc("Enable Anti-Disassembly (junk bytes, fake branches)."));
static cl::opt<bool>
    EnableAntiHexRays("enable-antihexrays", cl::init(false), cl::NotHidden,
                      cl::desc("Enable Anti-Decompiler (breaks Hex-Rays)."));
static cl::opt<bool>
    EnableReturnAddressEncryption("enable-retenc", cl::init(false),
                                 cl::NotHidden,
                                 cl::desc("Enable Return Address Encryption."));
static cl::opt<bool>
    EnableInstructionLevelAntiPatching(
        "enable-iap", cl::init(false), cl::NotHidden,
        cl::desc("Enable Instruction-Level Anti-Patching integrity checks."));
static cl::opt<bool>
    EnableCallStackSpoofing("enable-callstack-spoof", cl::init(false),
                            cl::NotHidden,
                            cl::desc("Enable Call Stack Spoofing."));
static cl::opt<bool>
    EnableSyscallInliner("enable-syscall-inliner", cl::init(false),
                         cl::NotHidden,
                         cl::desc("Replace libc syscall wrappers with svc."));
static cl::opt<bool>
    EnableCodeIntegrityReflection(
        "enable-cir", cl::init(false), cl::NotHidden,
        cl::desc("Enable cross-function Code Integrity Reflection."));
// End Obfuscator Options

static void LoadEnv(void) {
  if (getenv("SPLITOBF")) {
    EnableBasicBlockSplit = true;
  }
  if (getenv("SUBOBF")) {
    EnableSubstitution = true;
  }
  if (getenv("ALLOBF")) {
    EnableAllObfuscation = true;
  }
  if (getenv("FCO")) {
    EnableFunctionCallObfuscate = true;
  }
  if (getenv("STRCRY")) {
    EnableStringEncryption = true;
  }
  if (getenv("INDIBRAN")) {
    EnableIndirectBranching = true;
  }
  if (getenv("FUNCWRA")) {
    EnableFunctionWrapper = true;
  }
  if (getenv("BCFOBF")) {
    EnableBogusControlFlow = true;
  }
  if (getenv("ACDOBF")) {
    EnableAntiClassDump = true;
  }
  if (getenv("CFFOBF")) {
    EnableFlattening = true;
  }
  if (getenv("CONSTENC")) {
    EnableConstantEncryption = true;
  }
  if (getenv("ANTIHOOK")) {
    EnableAntiHooking = true;
  }
  if (getenv("ADB")) {
    EnableAntiDebugging = true;
  }
  if (getenv("MBAOBF")) {
    EnableMBAObfuscation = true;
  }
  if (getenv("OPQPRED")) {
    EnableOpaquePredicates = true;
  }
  if (getenv("VMFLATTEN")) {
    EnableVMFlatten = true;
  }
  if (getenv("ANTIDISASM")) {
    EnableAntiLinearSweep = true;
  }
  if (getenv("ANTIHEXRAYS")) {
    EnableAntiHexRays = true;
  }
  if (getenv("RETENC")) {
    EnableReturnAddressEncryption = true;
  }
  if (getenv("IAP")) {
    EnableInstructionLevelAntiPatching = true;
  }
  if (getenv("CALLSTACK_SPOOF")) {
    EnableCallStackSpoofing = true;
  }
  if (getenv("SYSCALL_INLINE")) {
    EnableSyscallInliner = true;
  }
  if (getenv("CIR")) {
    EnableCodeIntegrityReflection = true;
  }
}
namespace llvm {
struct Obfuscation : public ModulePass {
  static char ID;
  Obfuscation() : ModulePass(ID) {
    initializeObfuscationPass(*PassRegistry::getPassRegistry());
  }
  StringRef getPassName() const override {
    return "HikariObfuscationScheduler";
  }
  bool runOnModule(Module &M) override {
    if (!EnableIRObfusaction)
      return 0;
    TimerGroup *tg =
        new TimerGroup("Obfuscation Timer Group", "Obfuscation Timer Group");
    Timer *timer = new Timer("Obfuscation Timer", "Obfuscation Timer", *tg);
    timer->startTimer();

    errs() << "Running Hikari On " << M.getSourceFileName() << "\n";

    annotation2Metadata(M);

    ModulePass *MP = createAntiHookPass(EnableAntiHooking);
    MP->doInitialization(M);
    MP->runOnModule(M);
    delete MP;
    // Initial ACD Pass
    if (EnableAllObfuscation || EnableAntiClassDump) {
      ModulePass *P = createAntiClassDumpPass();
      P->doInitialization(M);
      P->runOnModule(M);
      delete P;
    }
    // SyscallInliner runs BEFORE FunctionCallObfuscate so libc syscall
    // wrappers are replaced with svc #0 before FCO obfuscates the call.
    FunctionPass *FP = createSyscallInlinerPass(
        EnableAllObfuscation || EnableSyscallInliner);
    for (Function &F : M)
      if (!F.isDeclaration())
        FP->runOnFunction(F);
    delete FP;
    // Now do FCO
    FP = createFunctionCallObfuscatePass(EnableAllObfuscation ||
                                         EnableFunctionCallObfuscate);
    for (Function &F : M)
      if (!F.isDeclaration())
        FP->runOnFunction(F);
    delete FP;
    MP = createAntiDebuggingPass(EnableAntiDebugging);
    MP->runOnModule(M);
    delete MP;
    // Now Encrypt Strings
    MP = createStringEncryptionPass(EnableAllObfuscation ||
                                    EnableStringEncryption);
    MP->runOnModule(M);
    delete MP;
    // Now perform Function-Level Obfuscation
    for (Function &F : M)
      if (!F.isDeclaration()) {
        FunctionPass *P = nullptr;
        // ReturnAddressEncryption runs FIRST so later passes (BCF, MBA, Sub)
        // obfuscate the key-load + XOR code itself
        P = createReturnAddressEncryptionPass(EnableAllObfuscation ||
                                              EnableReturnAddressEncryption);
        P->runOnFunction(F);
        delete P;
        P = createSplitBasicBlockPass(EnableAllObfuscation ||
                                      EnableBasicBlockSplit);
        P->runOnFunction(F);
        delete P;
        // Arithmetic obfuscations FIRST — they produce more operations that
        // the subsequent CFG-distortion passes can then hide behind fake
        // branches and flattening.
        P = createSubstitutionPass(EnableAllObfuscation || EnableSubstitution);
        P->runOnFunction(F);
        delete P;
        P = createMBAObfuscationPass(EnableAllObfuscation || EnableMBAObfuscation);
        P->runOnFunction(F);
        delete P;
        P = createOpaquePredicatesPass(EnableAllObfuscation || EnableOpaquePredicates);
        P->runOnFunction(F);
        delete P;
        // CFG-distortion passes AFTER arithmetic — BCF's opaque predicates
        // feed from OpaquePredicates, and Flattening must see the final
        // arithmetic form.
        P = createBogusControlFlowPass(EnableAllObfuscation ||
                                       EnableBogusControlFlow);
        P->runOnFunction(F);
        delete P;
        P = createFlatteningPass(EnableAllObfuscation || EnableFlattening);
        P->runOnFunction(F);
        delete P;
        // VM Virtualization — applies to ALL functions when flag is set
        // (no annotation needed, unlike before)
        P = createVMFlattenPass(EnableAllObfuscation || EnableVMFlatten);
        P->runOnFunction(F);
        delete P;
        // Callstack spoofing — rewrites saved LR around callsites. Runs
        // before IAP so the inserted pre/post-call stores are included in
        // the integrity measurement.
        P = createCallStackSpoofingPass(
            EnableAllObfuscation || EnableCallStackSpoofing);
        P->runOnFunction(F);
        delete P;
        // Integrity checks — placed before anti-RE passes so the inserted
        // check blocks themselves get additional junk from AntiLinearSweep.
        P = createInstructionLevelAntiPatchingPass(
            EnableAllObfuscation || EnableInstructionLevelAntiPatching);
        P->runOnFunction(F);
        delete P;
        // Anti-RE passes — LAST, after all obfuscation
        P = createAntiHexRaysPass(EnableAllObfuscation || EnableAntiHexRays);
        P->runOnFunction(F);
        delete P;
        P = createAntiLinearSweepPass(EnableAllObfuscation || EnableAntiLinearSweep);
        P->runOnFunction(F);
        delete P;
      }
    MP = createConstantEncryptionPass(EnableConstantEncryption);
    MP->runOnModule(M);
    delete MP;
    // CIR runs LAST of the obfuscation module-passes so it sees the
    // final per-function layouts when reasoning about hash targets.
    MP = createCodeIntegrityReflectionPass(EnableAllObfuscation ||
                                           EnableCodeIntegrityReflection);
    MP->runOnModule(M);
    delete MP;
    errs() << "Doing Post-Run Cleanup\n";
    FunctionPass *P = createIndirectBranchPass(EnableAllObfuscation ||
                                               EnableIndirectBranching);
    for (Function &F : M)
      if (!F.isDeclaration())
        P->runOnFunction(F);
    delete P;
    MP = createFunctionWrapperPass(EnableAllObfuscation ||
                                   EnableFunctionWrapper);
    MP->runOnModule(M);
    delete MP;
    // Cleanup Flags
    SmallVector<Function *, 8> toDelete;
    for (Function &F : M)
      if (F.isDeclaration() && F.hasName() &&
#if LLVM_VERSION_MAJOR >= 18
          F.getName().starts_with("hikari_")) {
#else
          F.getName().startswith("hikari_")) {
#endif
        for (User *U : F.users())
          if (Instruction *Inst = dyn_cast<Instruction>(U))
            Inst->eraseFromParent();
        toDelete.emplace_back(&F);
      }
    for (Function *F : toDelete)
      F->eraseFromParent();

    timer->stopTimer();
    errs() << "Hikari Out\n";
    errs() << "Spend Time: "
           << format("%.7f", timer->getTotalTime().getWallTime()) << "s"
           << "\n";
    tg->clearAll();
    return true;
  } // End runOnModule
};
ModulePass *createObfuscationLegacyPass() {
  LoadEnv();
  // Deterministic build: --obf-seed wins if set. Otherwise --aesSeed.
  // Otherwise time-based.
  if (ObfSeed != 0) {
    cryptoutils->prng_seed(ObfSeed);
    errs() << "Obfuscation PRNG seeded deterministically with --obf-seed="
           << format_hex(ObfSeed, 18) << "\n";
  } else if (AesSeed != 0x1337) {
    cryptoutils->prng_seed(AesSeed);
  } else if (const char *envSeed = getenv("OBF_SEED")) {
    uint64_t s = strtoull(envSeed, nullptr, 0);
    cryptoutils->prng_seed(s);
    errs() << "Obfuscation PRNG seeded from OBF_SEED="
           << format_hex(s, 18) << "\n";
  } else {
    cryptoutils->prng_seed();
  }
  errs() << "Initializing Hikari Core with Revision ID:" << GIT_COMMIT_HASH
         << "\n";
  return new Obfuscation();
}

PreservedAnalyses ObfuscationPass::run(Module &M, ModuleAnalysisManager &MAM) {
  if (createObfuscationLegacyPass()->runOnModule(M)) {
    return PreservedAnalyses::none();
  }
  return PreservedAnalyses::all();
}

} // namespace llvm
char Obfuscation::ID = 0;
INITIALIZE_PASS_BEGIN(Obfuscation, "obfus", "Enable Obfuscation", false, false)
INITIALIZE_PASS_DEPENDENCY(AntiClassDump);
INITIALIZE_PASS_DEPENDENCY(BogusControlFlow);
INITIALIZE_PASS_DEPENDENCY(Flattening);
INITIALIZE_PASS_DEPENDENCY(FunctionCallObfuscate);
INITIALIZE_PASS_DEPENDENCY(IndirectBranch);
INITIALIZE_PASS_DEPENDENCY(SplitBasicBlock);
INITIALIZE_PASS_DEPENDENCY(StringEncryption);
INITIALIZE_PASS_DEPENDENCY(Substitution);
INITIALIZE_PASS_DEPENDENCY(MBAObfuscation);
INITIALIZE_PASS_DEPENDENCY(OpaquePredicates);
INITIALIZE_PASS_DEPENDENCY(VMFlatten);
INITIALIZE_PASS_DEPENDENCY(AntiLinearSweep);
INITIALIZE_PASS_DEPENDENCY(AntiHexRays);
INITIALIZE_PASS_DEPENDENCY(ReturnAddressEncryption);
INITIALIZE_PASS_DEPENDENCY(InstructionLevelAntiPatching);
INITIALIZE_PASS_DEPENDENCY(CallStackSpoofing);
INITIALIZE_PASS_DEPENDENCY(SyscallInliner);
INITIALIZE_PASS_DEPENDENCY(CodeIntegrityReflection);
INITIALIZE_PASS_END(Obfuscation, "obfus", "Enable Obfuscation", false, false)

#if LLVM_VERSION_MAJOR >= 18

namespace llvm {

PassPluginLibraryInfo getHikariPluginInfo() {
  return {
      LLVM_PLUGIN_API_VERSION, "Hikari", LLVM_VERSION_STRING,
      [](PassBuilder &PB) {
        PB.registerPipelineParsingCallback(
            [](StringRef Name, ModulePassManager &FPM,
               ArrayRef<PassBuilder::PipelineElement> InnerPipeline) {
              if (Name == EnableIRObfusaction.ArgStr) {
                EnableIRObfusaction = true;
                for (const auto &Element : InnerPipeline) {
                  if (Element.Name == EnableAntiClassDump.ArgStr) {
                    EnableAntiClassDump = true;
                  } else if (Element.Name == EnableAntiHooking.ArgStr) {
                    EnableAntiHooking = true;
                  } else if (Element.Name == EnableAntiDebugging.ArgStr) {
                    EnableAntiDebugging = true;
                  } else if (Element.Name == EnableBogusControlFlow.ArgStr) {
                    EnableBogusControlFlow = true;
                  } else if (Element.Name == EnableFlattening.ArgStr) {
                    EnableFlattening = true;
                  } else if (Element.Name == EnableBasicBlockSplit.ArgStr) {
                    EnableBasicBlockSplit = true;
                  } else if (Element.Name == EnableSubstitution.ArgStr) {
                    EnableSubstitution = true;
                  } else if (Element.Name == EnableAllObfuscation.ArgStr) {
                    EnableAllObfuscation = true;
                  } else if (Element.Name ==
                             EnableFunctionCallObfuscate.ArgStr) {
                    EnableFunctionCallObfuscate = true;
                  } else if (Element.Name == EnableStringEncryption.ArgStr) {
                    EnableStringEncryption = true;
                  } else if (Element.Name == EnableConstantEncryption.ArgStr) {
                    EnableConstantEncryption = true;
                  } else if (Element.Name == EnableIndirectBranching.ArgStr) {
                    EnableIndirectBranching = true;
                  } else if (Element.Name == EnableFunctionWrapper.ArgStr) {
                    EnableFunctionWrapper = true;
                  } else if (Element.Name == EnableMBAObfuscation.ArgStr) {
                    EnableMBAObfuscation = true;
                  } else if (Element.Name == EnableOpaquePredicates.ArgStr) {
                    EnableOpaquePredicates = true;
                  } else if (Element.Name == EnableVMFlatten.ArgStr) {
                    EnableVMFlatten = true;
                  } else if (Element.Name == EnableAntiLinearSweep.ArgStr) {
                    EnableAntiLinearSweep = true;
                  } else if (Element.Name == EnableAntiHexRays.ArgStr) {
                    EnableAntiHexRays = true;
                  } else if (Element.Name ==
                             EnableReturnAddressEncryption.ArgStr) {
                    EnableReturnAddressEncryption = true;
                  } else if (Element.Name ==
                             EnableInstructionLevelAntiPatching.ArgStr) {
                    EnableInstructionLevelAntiPatching = true;
                  } else if (Element.Name ==
                             EnableCallStackSpoofing.ArgStr) {
                    EnableCallStackSpoofing = true;
                  } else if (Element.Name ==
                             EnableSyscallInliner.ArgStr) {
                    EnableSyscallInliner = true;
                  } else if (Element.Name ==
                             EnableCodeIntegrityReflection.ArgStr) {
                    EnableCodeIntegrityReflection = true;
                  }
                }

                FPM.addPass(ObfuscationPass());
                return true;
              } else {
                return false;
              }
            });
      }};
}

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getHikariPluginInfo();
}

} // namespace llvm

#endif
