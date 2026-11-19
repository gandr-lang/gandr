# gandr-runtime-rust-reader

The reader of a Rust crate: a driver on rustc's own libraries that writes the record of each requested function.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `gandr-rust-reader` takes rustc's arguments, compiles the crate to its analysis, and stops before code generation. It then asks rustc for each requested function's symbol, its convention and the layout of each type of its signature. It writes the answers as an entry of `runtime-rust-record`, with the digest of each source that rustc read.

**Why.** rustc computes a function's symbol and its convention for one build, and no stable interface gives them. A Dylint driver adds its own `-C metadata`, so its symbols name nothing in the real build, and it lowers the MIR optimisation level, so it misjudges which functions keep a symbol. A driver of its own runs rustc with the build's flags, so its answers are the build's answers.

**How.** The driver's file loader reads each source for rustc and keeps the BLAKE3 digest of the bytes that rustc read, so no edit falls between the read and the digest. After the analysis, `read::outcome` finds each requested function by its path, refuses one that has no symbol of its own, and asks `symbol_name`, `fn_abi_of_instance` and `layout_of`. Each LLVM type is spelled as rustc's LLVM backend spells it for that passage.

## References

- `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — the direction of the interop (§ io-direction-interop): a call into Rust uses rustc's own record of the function.

## Provided features

- `gandr-rust-reader <rustc arguments>`: the paths in `GANDR_RUST_RECORD_FUNCTIONS`, one on each line, are read, and the entry goes to `GANDR_RUST_RECORD_ENTRY`.
- Exit 0 with an entry, rustc's own status when the crate does not compile, 2 when an environment variable is missing, 3 when the entry is not written, and 4 when no analysis ran.

## Expected features

- **The `rustc-dev` component.** The reader links rustc's libraries, so it builds only where that component is installed. It is a workspace of its own, out of the root workspace, and `check:rust-record` builds it.
- **The toolchain of the build.** The reader runs only with the libraries of the toolchain that built it. Its rpath names that toolchain's library directory.

## Examples

`runtime-rust-record`'s `Cache::read` runs the reader. The tests in [`tests/reader.rs`](tests/reader.rs) read three crates of [`tests/fixtures`](tests/fixtures) through it. They compare each record with the `define` line that rustc emits and with the goldens of `corpus/model/layouts/rust-default.gandr`.

```sh
mise run check:rust-record
```

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
