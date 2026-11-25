// The implementation of `gandr_mlir_compile`. The order of the steps is the
// specification: the parse and the verifier first, then the translation to
// LLVM IR, then the code generator of the target.
//
// The entry is total. A fatal error of LLVM in the translation or in the code
// generator gives the status `GANDR_MLIR_COMPILE_ERROR` with its reason, and
// the process of the caller continues. The two steps run inside a
// `llvm::CrashRecoveryContext`, and the fatal error handler of the shim leaves
// the step through that context.

#include "gandr_mlir_shim.h"

#include "answer.h"
#include "dialect.h"

#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/IR/Verifier.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Target/LLVMIR/Dialect/Builtin/BuiltinToLLVMIRTranslation.h"
#include "mlir/Target/LLVMIR/Dialect/LLVMIR/LLVMToLLVMIRTranslation.h"
#include "mlir/Target/LLVMIR/Export.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/CrashRecoveryContext.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Triple.h"

#include <cstdlib>
#include <cstring>
#include <memory>
#include <mutex>
#include <string>

namespace {

using gandr::answer;

/// The reason of the last fatal error of LLVM on this thread.
thread_local std::string fatalReason;

/// The fatal error handler of the shim.
///
/// # Specification
/// - ensures: `fatalReason` holds `reason`. Inside a recovery context, the
///   step leaves through that context, and `RunSafely` returns false.
///   Outside a context, the handler returns, and LLVM stops the process as
///   before.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the fatal error of `tailcc` on riscv64 gives its reason
///   as a compile error, and the process continues.
/// - witness: ctest `convention-tailcc-riscv64-refused`
void onFatalError(void *, const char *reason, bool) {
  fatalReason = reason;
  if (llvm::CrashRecoveryContext *context =
          llvm::CrashRecoveryContext::GetCurrent())
    context->HandleExit(1);
}

/// Register each target of the pin, and the recovery of a fatal error, one
/// time in the process.
///
/// # Specification
/// - ensures: each target, its code generator and its asm parser are known
///   to LLVM. The recovery contexts work, and the fatal error handler of the
///   shim is installed.
/// - panics: none.
/// - intension: the work runs one time, also with calls on more than one
///   thread.
///
/// # Adequacy
/// - hypothesis: L3 — an object for each backend and an inline assembly body
///   need the registration, and a fatal error needs the handler.
/// - witness: ctest `object-aarch64`
/// - witness: ctest `operation-inline-asm`
/// - witness: ctest `convention-tailcc-riscv64-refused`
void initializeTargets() {
  static std::once_flag once;
  std::call_once(once, [] {
    llvm::InitializeAllTargetInfos();
    llvm::InitializeAllTargets();
    llvm::InitializeAllTargetMCs();
    llvm::InitializeAllAsmPrinters();
    // The object streamer parses inline assembly with the asm parser.
    llvm::InitializeAllAsmParsers();
    // The recovery of a fatal error. `Enable` also installs the signal
    // handlers of LLVM. A signal outside a recovery context restores the
    // handlers of the process and raises the signal again.
    llvm::CrashRecoveryContext::Enable();
    llvm::install_fatal_error_handler(onFatalError);
  });
}

} // namespace

/// Parse, verify, lower, translate and compile `text` for `triple`.
///
/// # Specification
/// - requires: `text` is valid for `text_len` bytes and `triple` for
///   `triple_len` bytes.
/// - ensures: status `GANDR_MLIR_OK` with the bytes of a relocatable object.
/// - fails: the first step that fails gives its status with its text: the
///   diagnostics of the parser, the verifier or the lowering of the `gandr`
///   dialect, the reason that the target is not known, or the error of the
///   translation or the code generator. A fatal error of LLVM in steps 3 and
///   4 gives `GANDR_MLIR_COMPILE_ERROR` with its reason, and the call returns.
/// - panics: none. Outside the two steps, a fatal error of LLVM stops the
///   process as LLVM does.
/// - intension: each call has its own MLIR context, so calls on more than one
///   thread share no state of MLIR.
///
/// # Cost
/// - allocation: one MLIR context and one LLVM context; after a fatal error
///   the LLVM context and the module of the step leak, because their state is
///   not known.
///
/// # Adequacy
/// - hypothesis: L3 — each status is reached by one input that fails only its
///   step, with a phrase of its text; each backend, each operation of the
///   minimal core and each transition of the `gandr` dialect gives an ELF
///   object.
/// - witness: ctest `object-x86_64`
/// - witness: ctest `object-aarch64`
/// - witness: ctest `object-riscv64`
/// - witness: ctest `verifier-refuses`
/// - witness: ctest `unknown-target`
/// - witness: ctest `operation-integers`
/// - witness: ctest `operation-load-store`
/// - witness: ctest `operation-atomic`
/// - witness: ctest `operation-inline-asm`
/// - witness: ctest `convention-tailcc-x86_64`
/// - witness: ctest `convention-tailcc-riscv64-refused`
/// - witness: ctest `convention-preserve-none`
/// - witness: ctest `dialect-transitions`
/// - witness: ctest `dialect-return-wrong-type`
/// - witness: ctest `dialect-call-wrong-operand`
/// - witness: ctest `dialect-jump-wrong-result`
extern "C" gandr_mlir_output gandr_mlir_compile(const char *text,
                                                size_t text_len,
                                                const char *triple,
                                                size_t triple_len) {
  mlir::DialectRegistry registry;
  registry.insert<mlir::LLVM::LLVMDialect, gandr::GandrDialect>();
  mlir::registerBuiltinDialectTranslation(registry);
  mlir::registerLLVMDialectTranslation(registry);
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  // The shim runs on the thread of its caller.
  context.disableMultithreading();

  // Step 1: the parse and the verifier. Each diagnostic goes to the answer.
  std::string diagnostics;
  llvm::raw_string_ostream diagnosticStream(diagnostics);
  llvm::SourceMgr sourceMgr;
  sourceMgr.AddNewSourceBuffer(
      llvm::MemoryBuffer::getMemBuffer(llvm::StringRef(text, text_len),
                                       "input", /*RequiresNullTerminator=*/false),
      llvm::SMLoc());
  mlir::SourceMgrDiagnosticHandler handler(sourceMgr, &context,
                                           diagnosticStream);
  mlir::ParserConfig config(&context, /*verifyAfterParse=*/true);
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceFile<mlir::ModuleOp>(sourceMgr, config);
  if (!module)
    return answer(GANDR_MLIR_INVALID_TEXT, diagnostics);

  // Step 1b: the lowering of the `gandr` dialect, then the verifier again.
  if (mlir::failed(gandr::lower(*module)) || mlir::failed(mlir::verify(*module)))
    return answer(GANDR_MLIR_INVALID_TEXT, diagnostics);

  // Step 2: the target.
  initializeTargets();
  llvm::Triple targetTriple(llvm::StringRef(triple, triple_len));
  std::string lookupError;
  const llvm::Target *target =
      llvm::TargetRegistry::lookupTarget(targetTriple, lookupError);
  if (target == nullptr)
    return answer(GANDR_MLIR_UNKNOWN_TARGET, lookupError);
  std::unique_ptr<llvm::TargetMachine> machine(target->createTargetMachine(
      targetTriple, /*CPU=*/"generic", /*Features=*/"", llvm::TargetOptions(),
      llvm::Reloc::PIC_));
  if (!machine)
    return answer(GANDR_MLIR_UNKNOWN_TARGET, "no target machine");

  // Steps 3 and 4 run inside a recovery context. After a fatal error, the
  // state of LLVM in the step is not known, so the shim leaks the context and
  // the module of the step and does not destroy them.
  auto llvmContext = std::make_unique<llvm::LLVMContext>();
  std::unique_ptr<llvm::Module> llvmModule;
  llvm::SmallVector<char, 0> object;
  std::string stepError;
  fatalReason.clear();
  llvm::CrashRecoveryContext recovery;
  bool finished = recovery.RunSafely([&] {
    // Step 3: the translation to LLVM IR.
    llvmModule = mlir::translateModuleToLLVMIR(*module, *llvmContext);
    if (!llvmModule) {
      stepError = diagnostics.empty() ? "the translation to LLVM IR failed"
                                      : diagnostics;
      return;
    }
    llvmModule->setTargetTriple(targetTriple);
    llvmModule->setDataLayout(machine->createDataLayout());

    // Step 4: the object.
    llvm::raw_svector_ostream objectStream(object);
    llvm::legacy::PassManager passes;
    if (machine->addPassesToEmitFile(passes, objectStream, nullptr,
                                     llvm::CodeGenFileType::ObjectFile)) {
      stepError = "the target cannot write an object file";
      return;
    }
    passes.run(*llvmModule);
  });
  if (!finished) {
    (void)llvmModule.release();
    (void)llvmContext.release();
    return answer(GANDR_MLIR_COMPILE_ERROR,
                  fatalReason.empty() ? "LLVM stopped the step" : fatalReason);
  }
  if (!stepError.empty())
    return answer(GANDR_MLIR_COMPILE_ERROR, stepError);
  return answer(GANDR_MLIR_OK, llvm::StringRef(object.data(), object.size()));
}

/// Release the bytes of an answer.
///
/// # Specification
/// - requires: `output` is null or an answer of `gandr_mlir_compile` whose
///   bytes no earlier call released.
/// - ensures: the bytes go back to `free`, and the answer holds null bytes and
///   a zero count. A null `output` does nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the test runner releases the answer of each status,
///   and the Rust tests release answers on eight threads.
/// - witness: ctest `object-x86_64`
/// - witness: ctest `unknown-target`
extern "C" void gandr_mlir_output_free(gandr_mlir_output *output) {
  if (output == nullptr)
    return;
  std::free(output->bytes);
  output->bytes = nullptr;
  output->len = 0;
}
