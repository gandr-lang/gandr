# gandr-runtime-emitter

Copy-and-patch emission of the L machine's lowered commands: native code under a content cache where the host has a patcher, the portable executor everywhere else.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [Mutation backlog](#mutation-backlog)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `lower` turns a focused command into a `Function`: a straight list of stencil instructions over one slot per binder, frames on the frame region, constructor fields pushed before their constructor and constants in the function's data. `evaluate` runs it on the tier the process's policy picks and moves the answer into the L machine's `Store`, so the machine's readback reads it; `evaluate_on` runs one tier. A command outside the lowered fragment is `Declined` by the form the lowering refused, and the caller runs it on the L machine.

**Why.** The L machine steps a command at a time through a dispatch loop; emitted code runs the same transitions with the registers pinned and no loop, and the emission cost is a copy and a few patches per stencil. It replaces the MLIR compile host: `src/lib.rs` states that decision and the measurement that would reverse it.

**How.** The build script compiles `gandr-runtime-stencils` under `--cfg gandr_stencil_object` with the toolchain's own `rustc`, reads the object with `object`, refuses any section, symbol or relocation the patcher cannot take, and writes the stencil table. Emission copies each instruction's stencil into a region of executable memory and patches its holes: operands, the next copy, a label, the shared exits. macOS arm64 patches `BRANCH26` and relaxes `GOT_LOAD` pairs; Linux x86-64 patches `PLT32`/`PC32` displacements and `32`/`32S` absolute fields under the static relocation model. Emitted functions live in a process-wide cache keyed by the function's content. The executor tier builds an instruction array from the same `Function` and runs the same stencil functions through their dispatch table.

## References

- Haoran Xu and Fredrik Kjolstad. "Copy-and-Patch Compilation: A Fast Compilation Algorithm for High-Level Languages and Bytecode." _Proceedings of the ACM on Programming Languages_ 5 (OOPSLA), article 136, 2021. [doi:10.1145/3485513](https://doi.org/10.1145/3485513). The algorithm: stencils with holes, copied and patched per item.
- [`object`](https://docs.rs/object/0.40.0/object/): the relocation view over ELF and Mach-O the build script reads the stencil object through.

## Provided features

- `lower`, `Lowered`, `Function`, `Form`: the lowering, its closure sites, the function it builds and the form it refuses.
- `evaluate`, `evaluate_on`, `Tier`, `Declined`: a run under the policy or on one tier, its answer moved into the machine's store, or the reason the machine runs it instead.
- `Policy` and `POLICY_VARIABLE`: `GANDR_NATIVE=always` (the default) emits on first run, `never` takes the executor, `cached` serves only what the cache holds.
- `PATCHER`: whether this host emits native code.
- `Fuel`, re-exported: the code-word jumps a run may take.

## Expected features

- **A host with a patcher for native code.** macOS on arm64 and Linux on x86-64; every other host runs the executor, with the same answers.
- **Executable memory.** macOS grants `MAP_JIT` to an unsigned or ad-hoc signed binary; a hardened-runtime binary needs the `com.apple.security.cs.allow-jit` entitlement. Linux needs `memfd_create` and a mapping below 2 GiB.
- **Defined constants.** Every constant a command reaches is defined in the `Definitions` given; an opaque one is carried as itself, and a run that observes it stops naming the constant, which the dispatcher blames as the L machine would.

## Examples

The emitter's witnesses run the named programs on both tiers and under the policy, each answer compared with the L machine's value by value; the stencil crate's suite runs the generated programs and the corpus through the same paths.

```sh
cargo test -p gandr-runtime-emitter
GANDR_NATIVE=never cargo run -p gandr-lang -- test crates/surface-corpus/fixture/model
```

## Where the detail lives

`src/lib.rs` states the tiers, the policy, the patchers, the runtime support and the retired compile host, each with its alternatives and reversal; `src/lower.rs` the linear form; `src/native.rs` and its `table`, `memory`, `aarch64` and `x86_64` modules emission, regions and patching; `src/transfer.rs` how an answer reaches the store; `build.rs` the stencil table and every refusal it makes.

## Mutation backlog

A standalone campaign over this crate's first landing should mutate the patch arithmetic in `src/native/aarch64.rs` and `src/native/x86_64.rs` (page offsets, displacements, addends, reach checks), the lowering's slot and label assignment, and the transfer's field order and capture binding. Hypotheses: the agreement suites reject a changed answer or a crash on either tier; the build script's refusals reject an unpatchable relocation. No mutation score is claimed.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
