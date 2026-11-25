// The `gandr` dialect of the shim: its registration and its lowering to the
// `llvm` dialect. `gandr.td` defines the operations.

#ifndef GANDR_DIALECT_H
#define GANDR_DIALECT_H

#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Dialect.h"
#include "mlir/IR/OpDefinition.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/InferTypeOpInterface.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

#include "GandrDialect.h.inc"

#define GET_OP_CLASSES
#include "GandrOps.h.inc"

namespace gandr {

/// Lower each operation of the `gandr` dialect in `module` to the `llvm`
/// dialect.
///
/// # Specification
/// - requires: `module` passed the verifier.
/// - ensures: on success no operation of the `gandr` dialect is left, and
///   each one is replaced by its lowering.
/// - fails: a diagnostic at the operation that has no lowering.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture of the transitions gives an object, which
///   the translation refuses while a `gandr` operation is left.
/// - witness: ctest `dialect-transitions`
mlir::LogicalResult lower(mlir::ModuleOp module);

} // namespace gandr

#endif // GANDR_DIALECT_H
