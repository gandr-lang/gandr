// The answer of an entry of the shim: a status and a copy of the bytes, from
// `malloc`, for `gandr_mlir_output_free`. Each entry of the shim uses it.
#ifndef GANDR_MLIR_SHIM_ANSWER_H
#define GANDR_MLIR_SHIM_ANSWER_H

#include "gandr_mlir_shim.h"

#include "llvm/ADT/StringRef.h"

#include <cstdlib>
#include <cstring>

namespace gandr {

/// Copy `bytes` into one `malloc` block, and make the answer of a call.
///
/// # Specification
/// - ensures: the answer has `status`. Its bytes are a copy of `bytes` in a
///   block that `gandr_mlir_output_free` releases, or null when `bytes` is
///   empty.
/// - fails: with no memory for the copy, the answer has `status`, null bytes
///   and a zero count.
/// - panics: none.
///
/// # Cost
/// - allocation: one `malloc` block of the size of `bytes`, none for empty
///   bytes.
///
/// # Adequacy
/// - hypothesis: L3 — an object, the facts of a body and a diagnostic each
///   come back whole.
/// - witness: ctest `object-x86_64`
/// - witness: ctest `verifier-refuses`
/// - witness: ctest `read-load`
inline gandr_mlir_output answer(gandr_mlir_status status,
                                llvm::StringRef bytes) {
  gandr_mlir_output output{status, nullptr, bytes.size()};
  if (!bytes.empty()) {
    output.bytes = static_cast<uint8_t *>(std::malloc(bytes.size()));
    if (output.bytes == nullptr) {
      // No memory for the answer: report the status with no bytes.
      output.len = 0;
      return output;
    }
    std::memcpy(output.bytes, bytes.data(), bytes.size());
  }
  return output;
}

} // namespace gandr

#endif // GANDR_MLIR_SHIM_ANSWER_H
