// The implementation of `gandr_mlir_read`: the second entry of the shim. The
// text of a machine body and the type of each hole go in. The verifier runs.
// The facts of each operation come out.
//
// The shim puts the body into one function of the `llvm` dialect, with one
// argument for each hole, and appends `llvm.unreachable` as the terminator:
//
//   line 1        llvm.func @gandr_body(%address: i64) {
//   lines 2 to n  the body, with each `${name}` as `%name` and two spaces
//   line n + 1    llvm.unreachable
//   line n + 2    }
//
// A hole keeps its length, so a column of a diagnostic is the column in the
// body. The shim takes 1 from each line, so a line of a diagnostic is the line
// in the body. Line 0 is the line of the holes.

#include "gandr_mlir_shim.h"

#include "answer.h"

#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/IR/Block.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/Location.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/IR/Operation.h"
#include "mlir/Parser/Parser.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <cctype>
#include <string>

namespace {

using gandr::answer;

/// The name of the function around the body.
constexpr llvm::StringLiteral bodyFunction = "gandr_body";

/// Whether `name` is the name of a hole: a letter or `_`, then letters,
/// digits and `_`.
///
/// # Specification
/// trivial.
bool isIdentifier(llvm::StringRef name) {
  if (name.empty() || !(std::isalpha(static_cast<unsigned char>(name[0])) ||
                        name[0] == '_'))
    return false;
  return llvm::all_of(name, [](char c) {
    return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
  });
}

/// The body with each hole `${name}` as `%name` and two spaces.
///
/// # Specification
/// - ensures: each `${name}` with an identifier is `%name` and two spaces, so
///   each column after it stays. A `${` with no identifier and `}` after it
///   stays as it is, and the parser refuses it.
/// - panics: none.
///
/// # Cost
/// - allocation: one string of the size of the body, setup
///
/// # Adequacy
/// - hypothesis: L3 — a hole that the list does not name gives the diagnostic
///   at its column in the body.
/// - witness: `read::tests::read_unknown_hole`
std::string substituteHoles(llvm::StringRef body) {
  std::string text;
  text.reserve(body.size());
  while (!body.empty()) {
    size_t start = body.find("${");
    if (start == llvm::StringRef::npos) {
      text += body;
      break;
    }
    text += body.take_front(start);
    body = body.drop_front(start);
    size_t end = body.find('}');
    llvm::StringRef name =
        end == llvm::StringRef::npos ? "" : body.slice(2, end);
    if (!isIdentifier(name)) {
      text += body.take_front(2);
      body = body.drop_front(2);
      continue;
    }
    text += '%';
    text += name;
    text += "  ";
    body = body.drop_front(end + 1);
  }
  return text;
}

/// The name of a severity, as the facts of a diagnostic write it.
///
/// # Specification
/// trivial.
const char *severityName(mlir::DiagnosticSeverity severity) {
  switch (severity) {
  case mlir::DiagnosticSeverity::Note:
    return "note";
  case mlir::DiagnosticSeverity::Warning:
    return "warning";
  case mlir::DiagnosticSeverity::Error:
    return "error";
  case mlir::DiagnosticSeverity::Remark:
    return "remark";
  }
  return "error";
}

/// Write one line `<line>:<column>: <severity>: <message>` for a diagnostic,
/// with the line of the body.
///
/// # Specification
/// - ensures: one line, with the line of the body (the line of the text less
///   one) and the column of the text. A message on more than one line goes on
///   one line.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an atomic load with no alignment gives its error at
///   line 2 and column 9 of the body.
/// - witness: ctest `read-verifier-refuses`
/// - witness: `read::tests::read_verifier_refuses`
void writeDiagnostic(llvm::raw_ostream &os, mlir::Location location,
                     mlir::DiagnosticSeverity severity,
                     llvm::StringRef message) {
  unsigned line = 0;
  unsigned column = 0;
  if (auto place = location->findInstanceOf<mlir::FileLineColLoc>()) {
    line = place.getLine() > 0 ? place.getLine() - 1 : 0;
    column = place.getColumn();
  }
  os << line << ':' << column << ": " << severityName(severity) << ": ";
  for (char c : message)
    os << (c == '\n' ? ' ' : c);
  os << '\n';
}

} // namespace

/// Parse and verify a machine body, and write the facts of each operation.
///
/// # Specification
/// - requires: `body` is valid for `body_len` bytes, and `holes` for
///   `hole_count` holes, each with its name and its type.
/// - ensures: status `GANDR_MLIR_OK` with one block of facts for each
///   operation of the body, in order.
/// - fails: `GANDR_MLIR_INVALID_TEXT` with each diagnostic of the parser or
///   the verifier, at its line and column in the body. A name that is not an
///   identifier, or a type on more than one line, gives a diagnostic at line
///   0.
/// - panics: none.
/// - intension: each call has its own MLIR context, so calls on more than one
///   thread share no state of MLIR.
///
/// # Cost
/// - allocation: one MLIR context, the text of the function, and the facts or
///   the diagnostics, setup
///
/// # Adequacy
/// - hypothesis: L3 — a load, a store, an atomic load and an inline assembly
///   body give their facts files, and a refused body gives its diagnostic.
/// - witness: ctest `read-load`
/// - witness: ctest `read-store`
/// - witness: ctest `read-atomic-load`
/// - witness: ctest `read-inline-asm`
/// - witness: ctest `read-verifier-refuses`
extern "C" gandr_mlir_output gandr_mlir_read(const char *body, size_t body_len,
                                             const gandr_mlir_hole *holes,
                                             size_t hole_count) {
  std::string diagnostics;
  llvm::raw_string_ostream diagnosticStream(diagnostics);

  // The line of the holes. A name is an identifier, and a type is on one line.
  std::string text = ("llvm.func @" + bodyFunction + "(").str();
  for (size_t index = 0; index < hole_count; ++index) {
    llvm::StringRef name(holes[index].name, holes[index].name_len);
    llvm::StringRef type(holes[index].type, holes[index].type_len);
    if (!isIdentifier(name) || type.contains('\n')) {
      diagnosticStream << "0:0: error: hole " << index << ": the name `"
                       << name << "` is not an identifier, or the type `"
                       << type << "` is not on one line\n";
      return answer(GANDR_MLIR_INVALID_TEXT, diagnostics);
    }
    if (index > 0)
      text += ", ";
    text += '%';
    text += name;
    text += ": ";
    text += type;
  }
  text += ") {\n";
  text += substituteHoles(llvm::StringRef(body, body_len));
  text += "\nllvm.unreachable\n}\n";

  mlir::DialectRegistry registry;
  registry.insert<mlir::LLVM::LLVMDialect>();
  mlir::MLIRContext context(registry);
  context.loadAllAvailableDialects();
  context.disableMultithreading();

  // The parse and the verifier. Each diagnostic and each of its notes goes to
  // the answer, with the line of the body.
  mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &diag) {
    writeDiagnostic(diagnosticStream, diag.getLocation(), diag.getSeverity(),
                    diag.str());
    for (mlir::Diagnostic &note : diag.getNotes())
      writeDiagnostic(diagnosticStream, note.getLocation(), note.getSeverity(),
                      note.str());
    return mlir::success();
  });
  llvm::SourceMgr sourceMgr;
  sourceMgr.AddNewSourceBuffer(llvm::MemoryBuffer::getMemBufferCopy(text, "body"),
                               llvm::SMLoc());
  mlir::ParserConfig config(&context, /*verifyAfterParse=*/true);
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceFile<mlir::ModuleOp>(sourceMgr, config);
  if (!module)
    return answer(GANDR_MLIR_INVALID_TEXT, diagnostics);

  auto function = module->lookupSymbol<mlir::LLVM::LLVMFuncOp>(bodyFunction);
  if (!function || function.getBody().getBlocks().size() != 1) {
    diagnosticStream << "0:0: error: a body is one sequence of operations "
                        "with no branch\n";
    return answer(GANDR_MLIR_INVALID_TEXT, diagnostics);
  }

  // The facts: one `operation` line, then a line for each operand, each
  // attribute and each result.
  //
  //   operation <name>
  //   operand hole <index of the hole>
  //   operand result <index of the operation> <index of the result>
  //   attribute <name> <the attribute as text>
  //   result <type>
  std::string facts;
  llvm::raw_string_ostream factStream(facts);
  llvm::DenseMap<mlir::Operation *, size_t> indexOf;
  mlir::Block &entry = function.getBody().front();
  for (mlir::Operation &op : entry.without_terminator()) {
    if (op.getNumRegions() > 0) {
      writeDiagnostic(diagnosticStream, op.getLoc(),
                      mlir::DiagnosticSeverity::Error,
                      ("the operation `" + op.getName().getStringRef() +
                       "` has a region, and a body has no region")
                          .str());
      return answer(GANDR_MLIR_INVALID_TEXT, diagnostics);
    }
    indexOf[&op] = indexOf.size();
    factStream << "operation " << op.getName().getStringRef() << '\n';
    for (mlir::Value operand : op.getOperands()) {
      if (auto hole = llvm::dyn_cast<mlir::BlockArgument>(operand)) {
        factStream << "operand hole " << hole.getArgNumber() << '\n';
        continue;
      }
      auto result = llvm::cast<mlir::OpResult>(operand);
      factStream << "operand result " << indexOf.lookup(result.getOwner())
                 << ' ' << result.getResultNumber() << '\n';
    }
    for (mlir::NamedAttribute attribute : op.getAttrDictionary()) {
      factStream << "attribute " << attribute.getName().getValue() << ' ';
      attribute.getValue().print(factStream);
      factStream << '\n';
    }
    for (mlir::Type type : op.getResultTypes()) {
      factStream << "result ";
      type.print(factStream);
      factStream << '\n';
    }
  }
  return answer(GANDR_MLIR_OK, facts);
}
