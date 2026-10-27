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
| Crate | Public items | Boundary types | Specs per item | Hotpath | Depth | Lines |
| ----- | ------------ | -------------- | -------------- | ------- | ----- | ----- |
| `core-checker` | 211 | 283 | 7.45 | yes | 7 | 82731 |
| `core-incremental` | 87 | 166 | 7.90 | no | 8 | 26867 |
| `core-nbe` | 160 | 176 | 8.81 | no | 6 | 48316 |
| `core-sequent` | 72 | 88 | 6.33 | no | 5 | 16013 |
| `core-session` | 35 | 43 | 3.26 | no | 5 | 2223 |
| `core-term` | 262 | 211 | 7.37 | no | 4 | 39821 |
| `core-unify` | 10 | 18 | 3.70 | no | 5 | 2329 |
| `kernel-check-memo` | 19 | 15 | 9.16 | no | 0 | 2885 |
| `kernel-conversion-trace` | 8 | 5 | 13.25 | no | 0 | 1156 |
| `kernel-core` | 190 | 211 | 7.72 | no | 2 | 73295 |
| `kernel-strata` | 50 | 42 | 7.94 | no | 0 | 9298 |
| `kernel-term` | 330 | 176 | 4.81 | no | 1 | 41114 |
| `runtime-emitter` | 52 | 68 | 0.73 | no | 6 | 12258 |
| `runtime-stencils` | 29 | 18 | 2.24 | no | 0 | 4884 |
| `storage-artifact` | 28 | 46 | 9.29 | no | 5 | 4167 |
| `storage-chunker` | 35 | 32 | 8.03 | no | 0 | 4327 |
| `storage-records` | 85 | 56 | 13.58 | no | 1 | 13970 |
| `storage-schema` | 55 | 53 | 6.35 | yes | 2 | 9502 |
| `storage-values` | 61 | 47 | 9.74 | no | 1 | 10171 |
| `surface-corpus` | 35 | 53 | 13.37 | no | 8 | 14473 |
| `surface-diagnostics` | 40 | 87 | 7.60 | no | 10 | 14409 |
| `surface-dispatcher` | 165 | 224 | 7.73 | yes | 12 | 49048 |
| `surface-format` | 31 | 47 | 2.35 | no | 11 | 10614 |
| `surface-grammar` | 78 | 74 | 7.74 | no | 2 | 26505 |
| `surface-layout` | 73 | 74 | 10.38 | no | 0 | 14871 |
| `surface-lowering` | 293 | 368 | 10.50 | yes | 5 | 147785 |
| `surface-lsp` | 176 | 184 | 3.07 | yes | 14 | 53355 |
| `surface-mcp` | 7 | 9 | 4.86 | no | 15 | 2926 |
| `surface-parser` | 69 | 71 | 12.86 | no | 3 | 28677 |
| `surface-pretty` | 46 | 72 | 10.39 | no | 9 | 21773 |
| `surface-render-remote` | 35 | 30 | 5.46 | no | 0 | 4032 |
| `surface-render-terminal` | 4 | 5 | 6.50 | no | 11 | 528 |
| `surface-repl` | 34 | 52 | 6.00 | no | 14 | 4192 |
| `surface-session` | 44 | 142 | 11.84 | no | 13 | 12920 |
| `surface-syntax` | 28 | 28 | 11.68 | no | 0 | 6182 |
| `surface-tui` | 20 | 25 | 6.10 | no | 15 | 2712 |
| `theory-cell-complexes` | 73 | 70 | 6.84 | no | 1 | 12231 |
| `theory-cell-complexes-tools` | 18 | 12 | 7.00 | no | 2 | 2733 |
| `theory-circuit-algebras` | 55 | 65 | 4.73 | no | 2 | 8194 |
| `theory-coherent-resolutions` | 49 | 42 | 5.33 | yes | 2 | 5408 |
| `theory-computads` | 46 | 54 | 6.28 | no | 4 | 10424 |
| `theory-decomposition-spaces` | 25 | 30 | 2.40 | no | 4 | 2225 |
| `theory-deep-inference` | 110 | 110 | 4.94 | no | 3 | 12639 |
| `theory-dynamic-graphs` | 24 | 29 | 3.21 | no | 2 | 3452 |
| `theory-graphs` | 56 | 50 | 6.64 | no | 1 | 6490 |
| `theory-levitation` | 158 | 138 | 3.68 | no | 1 | 22304 |
| `theory-nominal-automata` | 31 | 31 | 3.13 | no | 0 | 2196 |
| `theory-order-maintenance` | 10 | 12 | 21.90 | no | 0 | 3113 |
| `theory-path-orders` | 23 | 19 | 2.26 | no | 0 | 1815 |
| `theory-shapes` | 21 | 20 | 5.71 | no | 0 | 2221 |
| `theory-sites` | 84 | 76 | 3.70 | no | 3 | 8246 |
| `theory-spec-combinators` | 5 | 2 | 4.40 | no | 0 | 524 |
| `theory-virtual-doctrines` | 80 | 88 | 3.48 | no | 5 | 5432 |
| `workflow-build-state` | 8 | 10 | 5.38 | no | 0 | 1341 |
| `workflow-coverage-guard` | 30 | 28 | 4.50 | no | 0 | 2407 |
| `workflow-hotpath-guard` | 76 | 58 | 4.00 | no | 0 | 7047 |
| `workflow-lane-budget` | 24 | 20 | 5.08 | no | 0 | 2310 |
| `workflow-spec-cost` | 35 | 40 | 4.86 | no | 1 | 3693 |
| `workflow-sweep` | 27 | 26 | 4.96 | no | 12 | 2681 |
| `workflow-test-timing` | 31 | 29 | 5.71 | no | 0 | 2554 |

| Rank | Crate | Why |
| ---- | ----- | --- |
| 1 | `theory-spec-combinators` | leaf; 0.40 boundary types per item; 4.40 specs per item |
| 2 | `runtime-stencils` | leaf; 0.62 boundary types per item; 2.24 specs per item |
| 3 | `kernel-conversion-trace` | leaf; 0.63 boundary types per item; 13.25 specs per item |
| 4 | `workflow-hotpath-guard` | leaf; 0.76 boundary types per item; 4.00 specs per item |
| 5 | `kernel-check-memo` | leaf; 0.79 boundary types per item; 9.16 specs per item |
| 6 | `theory-path-orders` | leaf; 0.83 boundary types per item; 2.26 specs per item |
| 7 | `workflow-lane-budget` | leaf; 0.83 boundary types per item; 5.08 specs per item |
| 8 | `kernel-strata` | leaf; 0.84 boundary types per item; 7.94 specs per item |
| 9 | `surface-render-remote` | leaf; 0.86 boundary types per item; 5.46 specs per item |
| 10 | `storage-chunker` | leaf; 0.91 boundary types per item; 8.03 specs per item |
| 11 | `workflow-coverage-guard` | leaf; 0.93 boundary types per item; 4.50 specs per item |
| 12 | `workflow-test-timing` | leaf; 0.94 boundary types per item; 5.71 specs per item |
| 13 | `theory-shapes` | leaf; 0.95 boundary types per item; 5.71 specs per item |
| 14 | `surface-syntax` | leaf; 1.00 boundary types per item; 11.68 specs per item |
| 15 | `theory-nominal-automata` | leaf; 1.00 boundary types per item; 3.13 specs per item |
| 16 | `surface-layout` | leaf; 1.01 boundary types per item; 10.38 specs per item |
| 17 | `theory-order-maintenance` | leaf; 1.20 boundary types per item; 21.90 specs per item |
| 18 | `workflow-build-state` | leaf; 1.25 boundary types per item; 5.38 specs per item |
| 19 | `kernel-term` | depth 1; 0.53 boundary types per item; 4.81 specs per item |
| 20 | `storage-records` | depth 1; 0.66 boundary types per item; 13.58 specs per item |
| 21 | `theory-cell-complexes-tools` | depth 2; 0.67 boundary types per item; 7.00 specs per item |
| 22 | `storage-values` | depth 1; 0.77 boundary types per item; 9.74 specs per item |
| 23 | `core-term` | depth 4; 0.81 boundary types per item; 7.37 specs per item |
| 24 | `theory-levitation` | depth 1; 0.87 boundary types per item; 3.68 specs per item |
| 25 | `theory-graphs` | depth 1; 0.89 boundary types per item; 6.64 specs per item |
| 26 | `theory-sites` | depth 3; 0.90 boundary types per item; 3.70 specs per item |
| 27 | `surface-grammar` | depth 2; 0.95 boundary types per item; 7.74 specs per item |
| 28 | `theory-cell-complexes` | depth 1; 0.96 boundary types per item; 6.84 specs per item |
| 29 | `workflow-sweep` | depth 12; 0.96 boundary types per item; 4.96 specs per item |
| 30 | `theory-deep-inference` | depth 3; 1.00 boundary types per item; 4.94 specs per item |
| 31 | `surface-parser` | depth 3; 1.03 boundary types per item; 12.86 specs per item |
| 32 | `core-nbe` | depth 6; 1.10 boundary types per item; 8.81 specs per item |
| 33 | `theory-virtual-doctrines` | depth 5; 1.10 boundary types per item; 3.48 specs per item |
| 34 | `kernel-core` | depth 2; 1.11 boundary types per item; 7.72 specs per item |
| 35 | `workflow-spec-cost` | depth 1; 1.14 boundary types per item; 4.86 specs per item |
| 36 | `theory-computads` | depth 4; 1.17 boundary types per item; 6.28 specs per item |
| 37 | `theory-circuit-algebras` | depth 2; 1.18 boundary types per item; 4.73 specs per item |
| 38 | `theory-decomposition-spaces` | depth 4; 1.20 boundary types per item; 2.40 specs per item |
| 39 | `theory-dynamic-graphs` | depth 2; 1.21 boundary types per item; 3.21 specs per item |
| 40 | `core-sequent` | depth 5; 1.22 boundary types per item; 6.33 specs per item |
| 41 | `core-session` | depth 5; 1.23 boundary types per item; 3.26 specs per item |
| 42 | `surface-render-terminal` | depth 11; 1.25 boundary types per item; 6.50 specs per item |
| 43 | `surface-tui` | depth 15; 1.25 boundary types per item; 6.10 specs per item |
| 44 | `surface-mcp` | depth 15; 1.29 boundary types per item; 4.86 specs per item |
| 45 | `runtime-emitter` | depth 6; 1.31 boundary types per item; 0.73 specs per item |
| 46 | `surface-corpus` | depth 8; 1.51 boundary types per item; 13.37 specs per item |
| 47 | `surface-format` | depth 11; 1.52 boundary types per item; 2.35 specs per item |
| 48 | `surface-repl` | depth 14; 1.53 boundary types per item; 6.00 specs per item |
| 49 | `surface-pretty` | depth 9; 1.57 boundary types per item; 10.39 specs per item |
| 50 | `storage-artifact` | depth 5; 1.64 boundary types per item; 9.29 specs per item |
| 51 | `core-unify` | depth 5; 1.80 boundary types per item; 3.70 specs per item |
| 52 | `core-incremental` | depth 8; 1.91 boundary types per item; 7.90 specs per item |
| 53 | `surface-diagnostics` | depth 10; 2.17 boundary types per item; 7.60 specs per item |
| 54 | `surface-session` | depth 13; 3.23 boundary types per item; 11.84 specs per item |
| 55 | `theory-coherent-resolutions` | hotpath; depth 2; 0.86 boundary types per item; 5.33 specs per item |
| 56 | `storage-schema` | hotpath; depth 2; 0.96 boundary types per item; 6.35 specs per item |
| 57 | `surface-lsp` | hotpath; depth 14; 1.05 boundary types per item; 3.07 specs per item |
| 58 | `surface-lowering` | hotpath; depth 5; 1.26 boundary types per item; 10.50 specs per item |
| 59 | `core-checker` | hotpath; depth 7; 1.34 boundary types per item; 7.45 specs per item |
| 60 | `surface-dispatcher` | hotpath; depth 12; 1.36 boundary types per item; 7.73 specs per item |

The top three's boundary types from other crates, each by the path rustdoc records for its definition:

- `theory-spec-combinators`: 2 boundary types, none from another crate
- `runtime-stencils`: 18 boundary types, 2 from other crates: `core::option::Option`, `core::result::Result`
- `kernel-conversion-trace`: 5 boundary types, none from another crate
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
