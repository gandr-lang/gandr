/* The shim of gandr over MLIR: two entries.
 *
 * `gandr_mlir_compile`: MLIR text and a target triple go in. The verifier
 * runs first. The bytes of an object come out, or the text of the
 * diagnostics. The text is in the `llvm` and `gandr` dialects, with the
 * builtin module around it. After the verifier, the shim lowers each `gandr`
 * operation to the `llvm` dialect.
 *
 * `gandr_mlir_read`: the text of a machine body in the `llvm` dialect and the
 * type of each hole go in. The verifier runs. The facts of each operation
 * come out, or the diagnostics with the line and the column in the body.
 *
 * The library holds the MLIR and LLVM of the pin of `toolchain/mlir.pin`,
 * linked into it, and exports only the symbols of this header. */
#ifndef GANDR_MLIR_SHIM_H
#define GANDR_MLIR_SHIM_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The status of a call. */
typedef enum gandr_mlir_status {
  /* `bytes` holds an object file, or the facts of a body for
   * `gandr_mlir_read`. */
  GANDR_MLIR_OK = 0,
  /* `bytes` holds the diagnostics of the parser or of the verifier. */
  GANDR_MLIR_INVALID_TEXT = 1,
  /* `bytes` holds the reason why the target is not known. */
  GANDR_MLIR_UNKNOWN_TARGET = 2,
  /* `bytes` holds the error of the translation or of the code generator. A
   * fatal error of LLVM in those steps also gives this status, with its
   * reason, and the process of the caller continues. */
  GANDR_MLIR_COMPILE_ERROR = 3,
} gandr_mlir_status;

/* The answer of a call. The shim owns `bytes` until
 * `gandr_mlir_output_free`. */
typedef struct gandr_mlir_output {
  gandr_mlir_status status;
  uint8_t *bytes;
  size_t len;
} gandr_mlir_output;

/* Parse and verify `text`, translate it to LLVM IR, and generate an object
 * for `triple`, for example "x86_64-unknown-linux-gnu". Neither input needs a
 * terminating zero. The call is safe on more than one thread: each call has
 * its own MLIR context. */
gandr_mlir_output gandr_mlir_compile(const char *text, size_t text_len,
                                     const char *triple, size_t triple_len);

/* Release the bytes of an output. */
void gandr_mlir_output_free(gandr_mlir_output *output);

/* One hole of a machine body: its name, as `${name}` in the body, and its
 * type in the `llvm` dialect, for example "i64". */
typedef struct gandr_mlir_hole {
  const char *name;
  size_t name_len;
  const char *type;
  size_t type_len;
} gandr_mlir_hole;

/* Parse and verify a machine body: a sequence of operations of the `llvm`
 * dialect with no branch and no terminator. Each `${name}` in `body` is the
 * hole of that name, an argument of type `type`.
 *
 * With `GANDR_MLIR_OK`, `bytes` holds the facts of each operation in order,
 * one line each:
 *
 *   operation <name>
 *   operand hole <index of the hole>
 *   operand result <index of the operation> <index of the result>
 *   attribute <name> <the attribute as text>
 *   result <type>
 *
 * With `GANDR_MLIR_INVALID_TEXT`, `bytes` holds one line for each
 * diagnostic: `<line>:<column>: <severity>: <message>`. The line and the
 * column are those of the body, from 1. Line 0 is the list of the holes.
 * No input needs a terminating zero. The call is safe on more than one
 * thread. */
gandr_mlir_output gandr_mlir_read(const char *body, size_t body_len,
                                  const gandr_mlir_hole *holes,
                                  size_t hole_count);

#ifdef __cplusplus
}
#endif

#endif /* GANDR_MLIR_SHIM_H */
