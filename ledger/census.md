# Bootstrap census

Each workspace crate with a library, measured for the first rewrite in gandr: the runtime bootstrap (#2895) rewrites one crate at a time, and this census is its first rung (#2896), the record the boundary (#2901) and the first twin read. `mise run report:bootstrap-census` writes the block between the markers; `census.yml` reports a stale block weekly on one issue. The text outside the block is written by hand.

- **Public items:** the library's public items as `purposes:items` lists them, modules and the crate root left out.
- **Boundary types:** the types the crate's own public items name, in a signature, a field, a variant, an alias or a constant, each counted once; a trait implementation's own items are left out, the trait fixing their signatures. A type another crate defines must cross the rewrite's boundary as it stands.
- **Specs per item:** the specification bullets and the `- witness:` bullets of the public items' documentation, with the library's `#[spec]` attributes, over its public items.
- **Hotpath:** a function of the library is measured by `hotpath::measure`. A rewrite there answers to the runtime's speed before anything else, so it ranks after every crate that is not on the hotpath.
- **Depth:** the longest chain of workspace dependencies under the crate. A leaf, depth 0, is rewritten without rewriting anything it calls first.
- **Lines:** the library's Rust sources, test modules left out.

The ranking puts the crates off the hotpath first, then leaves before the rest, then the fewest boundary types per public item, then the most specs per item. A crate with no public item is last.

<!-- census:begin -->
The table gives each crate's census.

| Crate | Public items | Boundary types | Specs per item | Hotpath | Depth | Lines |
| ----- | ------------ | -------------- | -------------- | ------- | ----- | ----- |
| `core-checker` | 242 | 332 | 7.93 | yes | 8 | 109152 |
| `core-fork` | 11 | 8 | 6.82 | no | 0 | 2177 |
| `core-incremental` | 115 | 224 | 7.14 | no | 9 | 35651 |
| `core-nbe` | 168 | 182 | 8.92 | no | 7 | 54296 |
| `core-publish` | 7 | 10 | 2.86 | no | 0 | 475 |
| `core-sequent` | 93 | 100 | 5.84 | no | 6 | 20244 |
| `core-session` | 35 | 43 | 3.29 | no | 6 | 2221 |
| `core-term` | 323 | 240 | 7.07 | no | 5 | 47461 |
| `core-unify` | 10 | 18 | 3.70 | no | 6 | 2360 |
| `kernel-check-memo` | 21 | 17 | 13.14 | no | 0 | 4128 |
| `kernel-conversion-trace` | 8 | 5 | 13.25 | no | 0 | 1195 |
| `kernel-core` | 224 | 256 | 8.00 | no | 3 | 97860 |
| `kernel-strata` | 51 | 43 | 8.02 | no | 0 | 9468 |
| `kernel-term` | 375 | 209 | 4.96 | no | 1 | 49258 |
| `runtime-emitter` | 96 | 107 | 1.09 | no | 7 | 22020 |
| `runtime-net` | 26 | 25 | 4.27 | no | 6 | 3642 |
| `runtime-stencils` | 33 | 18 | 2.06 | no | 0 | 5243 |
| `storage-artifact` | 28 | 46 | 9.82 | no | 6 | 4419 |
| `storage-chunker` | 35 | 32 | 8.09 | no | 0 | 4454 |
| `storage-records` | 85 | 56 | 13.58 | no | 1 | 13982 |
| `storage-schema` | 55 | 53 | 6.35 | yes | 2 | 9502 |
| `storage-store` | 11 | 25 | 7.64 | no | 2 | 3359 |
| `storage-values` | 62 | 47 | 9.69 | no | 1 | 10223 |
| `surface-agentic` | 14 | 23 | 5.14 | no | 17 | 10710 |
| `surface-corpus` | 51 | 68 | 11.22 | no | 9 | 19098 |
| `surface-diagnostics` | 54 | 100 | 6.44 | no | 11 | 19091 |
| `surface-dispatcher` | 268 | 358 | 6.45 | yes | 13 | 70687 |
| `surface-features` | 8 | 15 | 7.63 | no | 0 | 1336 |
| `surface-format` | 31 | 47 | 2.26 | no | 12 | 11908 |
| `surface-grammar` | 85 | 76 | 7.88 | no | 2 | 27766 |
| `surface-layout` | 73 | 74 | 10.38 | no | 0 | 14877 |
| `surface-lowering` | 84 | 151 | 19.71 | yes | 7 | 135676 |
| `surface-lowering-base` | 316 | 373 | 7.68 | yes | 6 | 57540 |
| `surface-lsp` | 52 | 82 | 9.81 | yes | 15 | 51371 |
| `surface-lsp-base` | 346 | 278 | 1.41 | no | 12 | 16101 |
| `surface-parser` | 86 | 84 | 11.80 | no | 3 | 39458 |
| `surface-pretty` | 54 | 81 | 10.11 | no | 10 | 27224 |
| `surface-render-remote` | 103 | 89 | 3.49 | no | 0 | 8623 |
| `surface-render-terminal` | 4 | 5 | 6.50 | no | 12 | 533 |
| `surface-repl` | 34 | 54 | 6.21 | no | 15 | 4257 |
| `surface-session` | 57 | 159 | 10.96 | no | 14 | 19293 |
| `surface-syntax` | 37 | 37 | 10.92 | no | 0 | 8033 |
| `surface-tui` | 23 | 33 | 7.09 | no | 16 | 5163 |
| `theory-cell-complexes` | 77 | 71 | 7.13 | no | 1 | 12916 |
| `theory-cell-complexes-tools` | 19 | 12 | 7.68 | no | 2 | 3047 |
| `theory-cellular-sheaves` | 22 | 28 | 7.77 | no | 3 | 3760 |
| `theory-circuit-algebras` | 66 | 73 | 4.71 | no | 2 | 9620 |
| `theory-coherent-resolutions` | 92 | 82 | 4.14 | yes | 3 | 11723 |
| `theory-computads` | 48 | 54 | 6.54 | no | 5 | 12075 |
| `theory-decomposition-spaces` | 25 | 30 | 2.36 | no | 5 | 2249 |
| `theory-deep-inference` | 118 | 114 | 5.16 | no | 4 | 14299 |
| `theory-discrete-morse` | 37 | 29 | 5.46 | no | 2 | 5164 |
| `theory-dynamic-graphs` | 24 | 29 | 3.21 | no | 2 | 3466 |
| `theory-e-graphs` | 26 | 32 | 1.92 | no | 4 | 2432 |
| `theory-exact-reals` | 133 | 121 | 3.99 | no | 3 | 21029 |
| `theory-graded-posets` | 9 | 20 | 10.89 | no | 1 | 2403 |
| `theory-graphs` | 56 | 50 | 6.64 | no | 1 | 6490 |
| `theory-levitation` | 158 | 138 | 3.70 | no | 1 | 22422 |
| `theory-nominal-automata` | 31 | 31 | 3.13 | no | 0 | 2201 |
| `theory-order-maintenance` | 10 | 12 | 22.00 | no | 0 | 3169 |
| `theory-ordered-algebras` | 37 | 28 | 4.92 | no | 4 | 3818 |
| `theory-path-orders` | 24 | 20 | 2.17 | no | 0 | 1887 |
| `theory-probability` | 19 | 23 | 7.42 | no | 5 | 3179 |
| `theory-shapes` | 25 | 25 | 6.44 | no | 1 | 3063 |
| `theory-sites` | 114 | 99 | 3.92 | no | 3 | 13508 |
| `theory-spec-combinators` | 5 | 2 | 4.40 | no | 0 | 524 |
| `theory-stone-duality` | 21 | 19 | 9.67 | no | 0 | 3034 |
| `theory-virtual-doctrines` | 80 | 88 | 3.48 | no | 6 | 5439 |
| `workflow-build-state` | 8 | 12 | 6.13 | no | 0 | 1585 |
| `workflow-coverage-guard` | 39 | 35 | 4.31 | no | 1 | 2921 |
| `workflow-debt-ledger` | 7 | 8 | 4.57 | no | 0 | 360 |
| `workflow-github` | 7 | 9 | 4.14 | no | 0 | 544 |
| `workflow-host-tools` | 29 | 29 | 4.34 | no | 0 | 2746 |
| `workflow-hotpath-guard` | 76 | 59 | 4.00 | no | 1 | 6970 |
| `workflow-lane-budget` | 37 | 30 | 5.76 | no | 1 | 4067 |
| `workflow-ledger-tasks` | 10 | 24 | 9.60 | no | 14 | 8165 |
| `workflow-prose` | 40 | 32 | 2.75 | no | 1 | 5019 |
| `workflow-spec-cost` | 33 | 39 | 4.82 | no | 2 | 3691 |
| `workflow-sweep` | 29 | 27 | 5.10 | no | 13 | 3056 |
| `workflow-test-timing` | 31 | 30 | 5.71 | no | 1 | 2537 |

The table ranks the crates for the first rewrite.

| Rank | Crate | Why |
| ---- | ----- | --- |
| 1 | `theory-spec-combinators` | leaf; 0.40 boundary types per item; 4.40 specs per item |
| 2 | `runtime-stencils` | leaf; 0.55 boundary types per item; 2.06 specs per item |
| 3 | `kernel-conversion-trace` | leaf; 0.63 boundary types per item; 13.25 specs per item |
| 4 | `core-fork` | leaf; 0.73 boundary types per item; 6.82 specs per item |
| 5 | `kernel-check-memo` | leaf; 0.81 boundary types per item; 13.14 specs per item |
| 6 | `theory-path-orders` | leaf; 0.83 boundary types per item; 2.17 specs per item |
| 7 | `kernel-strata` | leaf; 0.84 boundary types per item; 8.02 specs per item |
| 8 | `surface-render-remote` | leaf; 0.86 boundary types per item; 3.49 specs per item |
| 9 | `theory-stone-duality` | leaf; 0.90 boundary types per item; 9.67 specs per item |
| 10 | `storage-chunker` | leaf; 0.91 boundary types per item; 8.09 specs per item |
| 11 | `surface-syntax` | leaf; 1.00 boundary types per item; 10.92 specs per item |
| 12 | `workflow-host-tools` | leaf; 1.00 boundary types per item; 4.34 specs per item |
| 13 | `theory-nominal-automata` | leaf; 1.00 boundary types per item; 3.13 specs per item |
| 14 | `surface-layout` | leaf; 1.01 boundary types per item; 10.38 specs per item |
| 15 | `workflow-debt-ledger` | leaf; 1.14 boundary types per item; 4.57 specs per item |
| 16 | `theory-order-maintenance` | leaf; 1.20 boundary types per item; 22.00 specs per item |
| 17 | `workflow-github` | leaf; 1.29 boundary types per item; 4.14 specs per item |
| 18 | `core-publish` | leaf; 1.43 boundary types per item; 2.86 specs per item |
| 19 | `workflow-build-state` | leaf; 1.50 boundary types per item; 6.13 specs per item |
| 20 | `surface-features` | leaf; 1.88 boundary types per item; 7.63 specs per item |
| 21 | `kernel-term` | depth 1; 0.56 boundary types per item; 4.96 specs per item |
| 22 | `theory-cell-complexes-tools` | depth 2; 0.63 boundary types per item; 7.68 specs per item |
| 23 | `storage-records` | depth 1; 0.66 boundary types per item; 13.58 specs per item |
| 24 | `core-term` | depth 5; 0.74 boundary types per item; 7.07 specs per item |
| 25 | `theory-ordered-algebras` | depth 4; 0.76 boundary types per item; 4.92 specs per item |
| 26 | `storage-values` | depth 1; 0.76 boundary types per item; 9.69 specs per item |
| 27 | `workflow-hotpath-guard` | depth 1; 0.78 boundary types per item; 4.00 specs per item |
| 28 | `theory-discrete-morse` | depth 2; 0.78 boundary types per item; 5.46 specs per item |
| 29 | `workflow-prose` | depth 1; 0.80 boundary types per item; 2.75 specs per item |
| 30 | `surface-lsp-base` | depth 12; 0.80 boundary types per item; 1.41 specs per item |
| 31 | `workflow-lane-budget` | depth 1; 0.81 boundary types per item; 5.76 specs per item |
| 32 | `theory-sites` | depth 3; 0.87 boundary types per item; 3.92 specs per item |
| 33 | `theory-levitation` | depth 1; 0.87 boundary types per item; 3.70 specs per item |
| 34 | `theory-graphs` | depth 1; 0.89 boundary types per item; 6.64 specs per item |
| 35 | `surface-grammar` | depth 2; 0.89 boundary types per item; 7.88 specs per item |
| 36 | `workflow-coverage-guard` | depth 1; 0.90 boundary types per item; 4.31 specs per item |
| 37 | `theory-exact-reals` | depth 3; 0.91 boundary types per item; 3.99 specs per item |
| 38 | `theory-cell-complexes` | depth 1; 0.92 boundary types per item; 7.13 specs per item |
| 39 | `workflow-sweep` | depth 13; 0.93 boundary types per item; 5.10 specs per item |
| 40 | `runtime-net` | depth 6; 0.96 boundary types per item; 4.27 specs per item |
| 41 | `theory-deep-inference` | depth 4; 0.97 boundary types per item; 5.16 specs per item |
| 42 | `workflow-test-timing` | depth 1; 0.97 boundary types per item; 5.71 specs per item |
| 43 | `surface-parser` | depth 3; 0.98 boundary types per item; 11.80 specs per item |
| 44 | `theory-shapes` | depth 1; 1.00 boundary types per item; 6.44 specs per item |
| 45 | `core-sequent` | depth 6; 1.08 boundary types per item; 5.84 specs per item |
| 46 | `core-nbe` | depth 7; 1.08 boundary types per item; 8.92 specs per item |
| 47 | `theory-virtual-doctrines` | depth 6; 1.10 boundary types per item; 3.48 specs per item |
| 48 | `theory-circuit-algebras` | depth 2; 1.11 boundary types per item; 4.71 specs per item |
| 49 | `runtime-emitter` | depth 7; 1.11 boundary types per item; 1.09 specs per item |
| 50 | `theory-computads` | depth 5; 1.13 boundary types per item; 6.54 specs per item |
| 51 | `kernel-core` | depth 3; 1.14 boundary types per item; 8.00 specs per item |
| 52 | `workflow-spec-cost` | depth 2; 1.18 boundary types per item; 4.82 specs per item |
| 53 | `theory-decomposition-spaces` | depth 5; 1.20 boundary types per item; 2.36 specs per item |
| 54 | `theory-dynamic-graphs` | depth 2; 1.21 boundary types per item; 3.21 specs per item |
| 55 | `theory-probability` | depth 5; 1.21 boundary types per item; 7.42 specs per item |
| 56 | `core-session` | depth 6; 1.23 boundary types per item; 3.29 specs per item |
| 57 | `theory-e-graphs` | depth 4; 1.23 boundary types per item; 1.92 specs per item |
| 58 | `surface-render-terminal` | depth 12; 1.25 boundary types per item; 6.50 specs per item |
| 59 | `theory-cellular-sheaves` | depth 3; 1.27 boundary types per item; 7.77 specs per item |
| 60 | `surface-corpus` | depth 9; 1.33 boundary types per item; 11.22 specs per item |
| 61 | `surface-tui` | depth 16; 1.43 boundary types per item; 7.09 specs per item |
| 62 | `surface-pretty` | depth 10; 1.50 boundary types per item; 10.11 specs per item |
| 63 | `surface-format` | depth 12; 1.52 boundary types per item; 2.26 specs per item |
| 64 | `surface-repl` | depth 15; 1.59 boundary types per item; 6.21 specs per item |
| 65 | `storage-artifact` | depth 6; 1.64 boundary types per item; 9.82 specs per item |
| 66 | `surface-agentic` | depth 17; 1.64 boundary types per item; 5.14 specs per item |
| 67 | `core-unify` | depth 6; 1.80 boundary types per item; 3.70 specs per item |
| 68 | `surface-diagnostics` | depth 11; 1.85 boundary types per item; 6.44 specs per item |
| 69 | `core-incremental` | depth 9; 1.95 boundary types per item; 7.14 specs per item |
| 70 | `theory-graded-posets` | depth 1; 2.22 boundary types per item; 10.89 specs per item |
| 71 | `storage-store` | depth 2; 2.27 boundary types per item; 7.64 specs per item |
| 72 | `workflow-ledger-tasks` | depth 14; 2.40 boundary types per item; 9.60 specs per item |
| 73 | `surface-session` | depth 14; 2.79 boundary types per item; 10.96 specs per item |
| 74 | `theory-coherent-resolutions` | hotpath; depth 3; 0.89 boundary types per item; 4.14 specs per item |
| 75 | `storage-schema` | hotpath; depth 2; 0.96 boundary types per item; 6.35 specs per item |
| 76 | `surface-lowering-base` | hotpath; depth 6; 1.18 boundary types per item; 7.68 specs per item |
| 77 | `surface-dispatcher` | hotpath; depth 13; 1.34 boundary types per item; 6.45 specs per item |
| 78 | `core-checker` | hotpath; depth 8; 1.37 boundary types per item; 7.93 specs per item |
| 79 | `surface-lsp` | hotpath; depth 15; 1.58 boundary types per item; 9.81 specs per item |
| 80 | `surface-lowering` | hotpath; depth 7; 1.80 boundary types per item; 19.71 specs per item |

The table gives the top three's boundary types from other crates, each by the path rustdoc records for its definition.

| Crate | Boundary types | From other crates | Types from other crates |
| ----- | -------------- | ----------------- | ----------------------- |
| `theory-spec-combinators` | 2 | 0 | none |
| `runtime-stencils` | 18 | 2 | `core::option::Option`, `core::result::Result` |
| `kernel-conversion-trace` | 5 | 0 | none |
<!-- census:end -->

## Candidates

The top three of this census, each with the specification its twin is written to, the oracle that holds the twin to the Rust, and the types that cross the boundary (#2901). The counts measure a surface, not what crossing it takes; each paragraph names what reading the crate adds. The paragraphs are rewritten when the top three change.

### `theory-spec-combinators`

- **Specification:** the four combinators' `ensures:` clauses and `# Clause cost` bounds in `sequence.rs`: `Mark::of` reads the length, `appended` returns the suffix past a mark and reads no element, `pushed` compares at most one element, `sorted_around` at most two. `Holds` converts to and from `bool`.
- **Oracle:** the crate's witnesses under `sequence::tests`, run on the twin with the same inputs; `pushed_compares_at_most_one_element` and `sorted_around_compares_at_most_two_elements` count comparisons through a tallying element, so they hold the twin to the bound as well as the answer.
- **Boundary:** no type from another crate. Its own `Mark` and `Holds` cross as a `usize` and a `bool`.
- **What the counts miss:** every combinator is generic over `&[T]`, and 11 crates call them inside `#[spec]` clauses. A generic signature does not cross an extern boundary, so the twin fixes the element types its callers instantiate or takes the comparison as an argument, and an enforcing build pays the crossing on every checked call.

### `runtime-stencils`

- **Specification:** the L machine's transitions as the crate's root states them: one stencil per transition under the five-register `Stencil` convention, the holes, the host call, and the authoring rules (no hole a valid pointer, no two stencils with one body, no call but the host, fuel spent at every unbounded jump).
- **Oracle:** `tests/agreement.rs`, the differential between emitted native code and the portable executor, and the reading each corpus `runs` item reaches.
- **Boundary:** `core::option::Option` and `core::result::Result`, then its own `Word` (`#[repr(transparent)]` over `usize`), `Runtime` and `Instruction` (`#[repr(C)]`), and the function-pointer types `Stencil` (`extern "rust-preserve-none"`) and `Host` (`extern "C"`).
- **What the counts miss:** the stencils are Rust compiled under `preserve_none` with `become`, into the object `gandr-runtime-emitter`'s build script patches. A twin produces that object or it replaces nothing, so it waits on a gandr lowering to that convention; each `#[repr(C)]` record is an ABI-realizability obligation of the kind #2900 states.

### `kernel-conversion-trace`

- **Specification:** the decision vocabulary `ConversionDecision<Id>`, the side of every reduction and the branch at every choice point, `ReturnEta` and `Reassociate` among them; `ConversionDecision::map`'s reanchoring; and the `TraceSink` contract: `NullSink` retains nothing and counts zero, `TraceLog` appends one decision per record and counts its length, and `ACTIVITY` is known at compile time.
- **Oracle:** `tests/differential.rs`, which asserts the recording paths a suite exercised, and the witnesses `sink::tests::a_trace_log_retains_every_decision_in_order`, `sink::tests::the_null_sink_retains_nothing` and `decision::tests::reanchoring_keeps_every_branch`.
- **Boundary:** no type from another crate. Its own decision, side, position, activity and count types cross as data, the enums as tagged sums.
- **What the counts miss:** the identifier parameter `Id` and the trait `TraceSink` with its associated constant are generic, and six crates (`core-checker`, `core-nbe`, `kernel-core`, `kernel-term`, `surface-corpus`, and `theory-coherent-resolutions`' tests) instantiate them at their own identifiers. The static-dispatch discipline, recording compiled away at `NullSink`, does not survive a call through an extern boundary, and the kernel replays what this vocabulary records.
