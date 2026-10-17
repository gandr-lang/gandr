# gandr-runtime-stencils

The L machine's transitions written once: the stencils copy-and-patch emits, and the portable executor that dispatches the same functions.

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

**What.** Every transition of the L machine is one stencil: an `extern "rust-preserve-none"` function over five pinned registers — the run's record, the heap's bump pointer, the frame region's top, the current window of slots and the value in hand — that ends in a `become` to a continuation. Constants, variables, binds, constructors and their matches, closures and their entries, frames and the exits make up the set, and `StencilId` names each one.

**Why.** Two implementations of the same transitions, an interpreter and a code generator, are held together only by tests. Written once, the emitted code and the executor cannot drift, and the executor is the differential the emitted code answers to on every host.

**How.** The crate compiles two ways. `gandr-runtime-emitter`'s build script compiles `src/lib.rs` alone under `--cfg gandr_stencil_object`: each operand is the address of an undefined static and each continuation a call to an undefined function, so every use is a relocation the emitter patches when it copies the stencil. The ordinary library build defines those holes instead: an operand reads the current `Instruction`, a continuation advances to the next one and `become`s its stencil, and `execute` enters that chain. Heap objects are a header word — kind, tag, arity and family — followed by fields; frames are two words, a code word and the window it resumes in, above a sentinel whose code halts; every code-word jump spends one unit of fuel.

## References

- Haoran Xu and Fredrik Kjolstad. "Copy-and-Patch Compilation: A Fast Compilation Algorithm for High-Level Languages and Bytecode." _Proceedings of the ACM on Programming Languages_ 5 (OOPSLA), article 136, 2021. [doi:10.1145/3485513](https://doi.org/10.1145/3485513). Stencils compiled ahead of time with holes, copied and patched at run time.
- Haoran Xu and Fredrik Kjolstad. "Deegen: A JIT-Capable VM Generator for Dynamic Languages." 2024. [arXiv:2411.11469](https://arxiv.org/abs/2411.11469). One semantic definition generating both the interpreter and the baseline compiler.
- Paul Downen and Zena M. Ariola. "A Tutorial on Computational Classical Logic and the Sequent Calculus." _Journal of Functional Programming_ 28 (2018), e3. [doi:10.1017/S0956796818000023](https://doi.org/10.1017/S0956796818000023). The sequent machine whose transitions these are.

## Provided features

- `Stencil`, `Runtime`, `Word`, `Instruction`: the stencil signature, the per-run record the stencils read their limits and fuel from and write their exit to, the machine word, and the executor's instruction.
- `StencilId` with `ALL`, `symbol` and `handler`: every stencil by name, the list the emitter's build script holds the object to.
- `execute` and `enter`: the two entries from Rust, into an executor program or into emitted code.
- `Header`, `Kind`, `Tag`, `Arity`, `Family`, `Flavour`: the heap object header and its fields, each refusing a value past its width with `FieldOverflow`.
- `Status` and `Fuel`: why a run returned — halted, unmatched, or a region or the fuel spent — and the jumps it may take.

## Expected features

- **A pinned nightly toolchain.** The crate enables `rust_preserve_none_cc` and `explicit_tail_calls`; `src/lib.rs` states why neither has a stable equivalent.
- **A 64-bit host.** An integer literal is one word and a header's family rides in its high half.
- **A lowering that keeps the invariants.** A stencil dereferences its registers unchecked; `gandr-runtime-emitter` establishes every slot, mark and object it reads, and the entries are `unsafe` for that reason.

## Examples

The witnesses run every program three ways — emitted native code where the host has a patcher, the executor, and the L machine — and compare the answers value by value: the named programs, 512 generated programs over budgets 1 to 1024, and every `runs` item of the corpus, with the lowering's refusals counted by form.

```sh
cargo test -p gandr-runtime-stencils
```

## Where the detail lives

`src/lib.rs` states the registers, the holes, the authoring rules a stencil must keep and the feature gates; `src/layout.rs` the header and the exit statuses; `src/transitions.rs` each stencil's transition; `src/holes.rs` the two definitions of every hole; `src/executor.rs` the dispatch table and the entries.

## Mutation backlog

A standalone campaign over this crate's first landing, restricted to `src/transitions.rs`, `src/holes.rs` and `src/layout.rs`, should mutate operand selection, field order in the constructor and frame stencils, the header shifts and masks, the match comparisons and the fuel decrement. Hypotheses: the agreement suite rejects a changed answer on either tier; the exit witnesses reject a moved limit or an unspent jump; the layout witnesses reject overlapping fields. No mutation score is claimed.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
