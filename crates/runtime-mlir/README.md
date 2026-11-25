# gandr-runtime-mlir

The Rust side of the MLIR shim. It compiles MLIR text for a target triple into the bytes of an object, and it reads the facts of a machine body. It lowers focused definitions to MLIR text of the `gandr` dialect. It prints a term of a signature as MLIR text, and it reads the facts of a body back into a term.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `compile` takes MLIR text in the `llvm` and `gandr` dialects and a target triple. It gives an `Object` with the bytes of a relocatable object file, or a `CompileError` that names the step that refused the text. `read` gives the facts of a machine body. The C++ shim in `cxx/` does the work of both, through one C entry for each. `print_term` writes a term of a signature, such as the block `Llvm` of `std.llvm`, as MLIR text in the generic form. `read_term` reads the facts of a body into a term of that signature, and its print is the body.

`lower` takes the focused definitions of a module and gives one `tailcc` function of the `gandr` dialect for each, or the `Form` that it refuses. A node or a type that the lowering has no form for gives `Form::Outside` with the name of its variant. `Lowered::entry` adds the entry of a program with no libc, and `Export` a symbol of the C convention.

**Why.** gandr writes native code through MLIR. One small C entry keeps the C++ of the pin out of the Rust build. The verifier runs before the translation. Thus a wrong text gives a diagnostic and not a crash of the code generator. The `gandr` dialect writes each transition of the machine one time, as one operation with one lowering.

**How.** Under the feature `full`, the build script builds the shim from `cxx/` with CMake, into one shared library that exports three symbols, and links it. The toolchain of the pin, which `GANDR_MLIR_TOOLCHAIN` names, gives the libraries of MLIR and LLVM. Without the feature the crate holds the types of the answers and builds no C++, so the workspace builds on a host with no toolchain.

## References

- `vault:01a1f7d8-3d56-7502-b037-3d37c5464b50` — dependency: § mojo-shim of the vault page `mojo-and-gandr`. The crate takes the boundary of MLIR text, the one C entry, and the verifier first.

## Provided features

- `compile`, under `full`: MLIR text and a triple in, an `Object` out. First come the parse with the verifier and the lowering of the `gandr` dialect. Then come the lookup of the target, the translation to LLVM IR, and the code generator.
- `Object`, under `full`, with `AsRef<[u8]>`: the bytes of the object file, in the format of the target.
- `CompileError`: the step that failed, with the text of its diagnostics.
- The targets of the pin: x86-64, aarch64 and riscv64.
- `read`, under `full`: the facts of a machine body and its `Hole`s, with one `Operation` for each operation of the body. An `Operation` has its name, its `Operand`s, its attributes and its result types.
- `ReadError`: each `Diagnostic` of a refused body, at its line and column in the body.
- `print_term` and `TermPrinter`: a `BindingTerm` and the table of its signature in, a `Printed` out, with one operation on each line and the type of each result. A `Place` puts the body inside a function. A `PrintError` names the port that has no print.
- `read_term`: the `Operation`s of a body, the table of a signature and a `Naming` in, a `BindingTerm` out. A `TermReadError` names the operation or the port that does not read.
- `Naming`: the MLIR names of a block where they are not the names of the block. `Naming::LLVM` is the table of `std.llvm`, and `Naming::NONE` keeps each name.
- `lower`, `Definition`, `Lowered` and `Form`: a definition whose type is a thunk of arrows over widths, `Unit` and sums of two words or units, to a returner of such a type or of `Void`, lowers to one function. A native row lowers by its typed operation, `Primitive::machine_operation` or `Primitive::checked_operation`. The effect row of a returner does not refuse a definition: each node of its body does.
- `Entry` and `ENTRY`: the entry of a program with no libc, which calls the main definition and gives its word to the system call `exit_group` of Linux x86-64.
- `Export`: a function of the C convention that calls a definition of widths.
- The `gandr` dialect in `cxx/src/gandr.td`. Each operation lowers to the `llvm` dialect:

| Operation | Transition | Lowering |
| --------- | ---------- | -------- |
| `gandr.return` | a value to the return continuation, or no value from a function of `void` | `llvm.return` |
| `gandr.wrapping_add`, `gandr.wrapping_sub`, `gandr.wrapping_mul` | a native operation of a width | `llvm.add`, `llvm.sub`, `llvm.mul` |
| `gandr.and`, `gandr.or`, `gandr.xor` | a bit operation of a width | `llvm.and`, `llvm.or`, `llvm.xor` |
| `gandr.not` | the bit negation of a width | `llvm.xor` with the word of all ones |
| `gandr.call` | a definition against a frame that binds its result; no result for a callee of `void` | `llvm.call` with `tailcc` |
| `gandr.jump` | a definition against the return continuation | `llvm.call` with `tailcc` and `musttail`, then `llvm.return` |

The verifier refuses a return type, a callee, an operand or a convention that does not agree with the function.

## Expected features

- Under `full`, `GANDR_MLIR_TOOLCHAIN` names the root of the unpacked toolchain `llvmorg-23.1.6`. The build script reads `lib/cmake/mlir` below it, and CMake refuses a toolchain of another release.
- Under `full`, the host has `cmake`, a Clang 23 C++ compiler and `mold`. The archives of the toolchain hold ThinLTO bitcode, so the link of the shim runs LTO.
- A binary that links this crate finds `libgandr_mlir_shim.so` at run time. The tests of this crate get an rpath. A consumer reads the directory from `DEP_GANDR_MLIR_SHIM_LIB`.

## Examples

```rust
# #[cfg(feature = "full")]
# fn main() -> Result<(), gandr_runtime_mlir::CompileError> {
use gandr_runtime_mlir::compile;

let text = "llvm.func @zero() -> i32 {
  %zero = llvm.mlir.constant(0 : i32) : i32
  llvm.return %zero : i32
}";
let object = compile(text.into(), "x86_64-unknown-linux-gnu".into())?;
assert!(object.as_ref().starts_with(b"\x7fELF"));
# Ok(())
# }
# #[cfg(not(feature = "full"))]
# fn main() {}
```

The tests of the crate read the MLIR files of the C++ tests in `cxx/tests/`, and the tests of the read of a term and of the agreement read the block of `library/std/src/llvm.gandr` through the lowering of the surface. The tests of the lowering link each program with the `ld.lld` of the toolchain and run it. `tests/corpus.rs` holds the executor and the compiled code to one answer for each `runs` item of `corpus/model/programs` that the lowering accepts, and counts each refused item by the name of its refusal. They run under the feature:

```sh
GANDR_MLIR_TOOLCHAIN=<root> cargo nextest run -p gandr-runtime-mlir --features full
```

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The steps of a call, and the errors | [`src/lib.rs`](src/lib.rs) |
| The C interface, and the owner of the bytes | [`src/ffi.rs`](src/ffi.rs) |
| The build and the link of the library | [`build.rs`](build.rs) |
| The shim, and the order of its steps | [`cxx/src/shim.cpp`](cxx/src/shim.cpp) |
| The operations of the `gandr` dialect | [`cxx/src/gandr.td`](cxx/src/gandr.td) |
| The verifiers and the lowering of the dialect | [`cxx/src/dialect.cpp`](cxx/src/dialect.cpp) |
| The read entry, and the form of its facts | [`src/read.rs`](src/read.rs) |
| The forms of the lowering, command by command, and each refusal | [`src/lower.rs`](src/lower.rs) |
| The entry of a program with no libc | [`src/entry.rs`](src/entry.rs) |
| The symbol of an export | [`src/export.rs`](src/export.rs) |
| The print of a term, port by port | [`src/print.rs`](src/print.rs) |
| The read of the facts into a term | [`src/term.rs`](src/term.rs) |
| The MLIR names of a block | [`src/naming.rs`](src/naming.rs) |
| The body inside its function, and the facts | [`cxx/src/read.cpp`](cxx/src/read.cpp) |

## License

Apache-2.0 WITH LLVM-exception, the license of the workspace. The text is at the root of the repository.
