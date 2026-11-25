# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

An export carries a function that is not generic, whose operands are fixed-width integers or addresses, and whose result is one of the two. A fixed-width integer is `u8` to `u64`, `i8` to `i64`, `usize` or `isize`. An address is a reference or a raw pointer to a sized type. The column gives the count of such public functions and methods, of the count of all, and its share.

`twin-census --write` writes this file from `cargo metadata` and from the JSON that rustdoc writes for each library. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter | Generic items | Export fragment |
| ----- | ----------------- | ------------- | --------------- |
| `boot-alloc` | yes | 0 | 0 of 16 (0 %) |
| `boot-core` | no | 0 | 0 of 8 (0 %) |
| `boot-io` | no | 0 | 0 of 8 (0 %) |
| `core-checker` | no | 1 | 1 of 8 (12 %) |
| `core-checker-base` | no | 123 | 84 of 529 (15 %) |
| `core-checker-bridge` | no | 15 | 4 of 66 (6 %) |
| `core-content` | yes | 34 | 2 of 108 (1 %) |
| `core-fork` | yes | 4 | 0 of 9 (0 %) |
| `core-incremental` | no | 37 | 12 of 131 (9 %) |
| `core-nbe` | no | 14 | 1 of 73 (1 %) |
| `core-nbe-base` | no | 12 | 5 of 121 (4 %) |
| `core-publish` | no | 1 | 0 of 2 (0 %) |
| `core-sequent` | yes | 4 | 4 of 94 (4 %) |
| `core-session` | yes | 2 | 0 of 16 (0 %) |
| `core-term` | yes | 151 | 6 of 588 (1 %) |
| `core-unify` | no | 3 | 0 of 17 (0 %) |
| `kernel-check-memo` | yes | 29 | 0 of 30 (0 %) |
| `kernel-conversion-trace` | yes | 6 | 0 of 3 (0 %) |
| `kernel-core` | yes | 8 | 4 of 147 (2 %) |
| `kernel-core-base` | yes | 63 | 18 of 330 (5 %) |
| `kernel-data` | yes | 75 | 0 of 68 (0 %) |
| `kernel-strata` | yes | 0 | 8 of 75 (10 %) |
| `kernel-term` | yes | 55 | 15 of 373 (4 %) |
| `runtime-emitter` | the emitter | 12 | 1 of 71 (1 %) |
| `runtime-net` | no | 0 | 4 of 45 (8 %) |
| `runtime-rust-record` | no | 0 | 0 of 7 (0 %) |
| `runtime-stencils` | yes | 2 | 10 of 46 (21 %) |
| `storage-artifact` | no | 5 | 2 of 45 (4 %) |
| `storage-chunker` | yes | 0 | 0 of 57 (0 %) |
| `storage-records` | no | 15 | 2 of 145 (1 %) |
| `storage-schema` | no | 17 | 11 of 108 (10 %) |
| `storage-store` | no | 4 | 3 of 32 (9 %) |
| `storage-values` | yes | 17 | 2 of 64 (3 %) |
| `surface-agentic` | no | 3 | 0 of 12 (0 %) |
| `surface-build-identity` | no | 0 | 0 of 2 (0 %) |
| `surface-corpus` | no | 18 | 3 of 60 (5 %) |
| `surface-diagnostics` | no | 26 | 1 of 62 (1 %) |
| `surface-dispatcher` | no | 89 | 22 of 366 (6 %) |
| `surface-driver` | no | no library | no library |
| `surface-evaluate` | no | 1 | 0 of 17 (0 %) |
| `surface-features` | no | 0 | 0 of 8 (0 %) |
| `surface-format` | no | 0 | 0 of 12 (0 %) |
| `surface-grammar` | no | 3 | 5 of 104 (4 %) |
| `surface-layout` | no | 2 | 0 of 37 (0 %) |
| `surface-lowering` | no | 1 | 3 of 11 (27 %) |
| `surface-lowering-base` | no | 260 | 18 of 743 (2 %) |
| `surface-lowering-capability` | no | 56 | 0 of 52 (0 %) |
| `surface-lowering-exits` | no | 32 | 0 of 30 (0 %) |
| `surface-lowering-expression` | no | 136 | 0 of 134 (0 %) |
| `surface-lowering-identity` | no | 34 | 0 of 31 (0 %) |
| `surface-lowering-model` | no | 93 | 0 of 94 (0 %) |
| `surface-lowering-native` | no | 47 | 0 of 65 (0 %) |
| `surface-lsp` | no | 3 | 1 of 53 (1 %) |
| `surface-lsp-base` | no | 18 | 1 of 173 (0 %) |
| `surface-lsp-core` | no | 11 | 4 of 80 (5 %) |
| `surface-lsp-diagnostics` | no | 12 | 0 of 23 (0 %) |
| `surface-lsp-navigation` | no | 8 | 0 of 37 (0 %) |
| `surface-parser` | no | 0 | 4 of 114 (3 %) |
| `surface-pretty` | no | 38 | 1 of 68 (1 %) |
| `surface-render-remote` | no | 0 | 2 of 51 (3 %) |
| `surface-render-terminal` | no | 0 | 0 of 2 (0 %) |
| `surface-repl` | no | 8 | 0 of 25 (0 %) |
| `surface-session` | no | 61 | 14 of 126 (11 %) |
| `surface-syntax` | no | 0 | 0 of 62 (0 %) |
| `surface-tui` | no | 5 | 0 of 21 (0 %) |
| `theory-cell-complexes` | yes | 42 | 6 of 115 (5 %) |
| `theory-cell-complexes-tools` | no | 6 | 0 of 8 (0 %) |
| `theory-cellular-sheaves` | no | 26 | 1 of 30 (3 %) |
| `theory-circuit-algebras` | yes | 16 | 20 of 98 (20 %) |
| `theory-coherent-resolutions` | yes | 93 | 2 of 90 (2 %) |
| `theory-computads` | no | 14 | 1 of 22 (4 %) |
| `theory-decomposition-spaces` | no | 13 | 0 of 9 (0 %) |
| `theory-deep-inference` | yes | 112 | 0 of 121 (0 %) |
| `theory-discrete-morse` | yes | 56 | 0 of 35 (0 %) |
| `theory-dynamic-graphs` | yes | 0 | 0 of 16 (0 %) |
| `theory-e-graphs` | no | 19 | 0 of 19 (0 %) |
| `theory-exact-reals` | yes | 17 | 6 of 138 (4 %) |
| `theory-graded-posets` | yes | 12 | 4 of 22 (18 %) |
| `theory-graphs` | yes | 47 | 0 of 69 (0 %) |
| `theory-levitation` | yes | 165 | 3 of 197 (1 %) |
| `theory-nominal-automata` | no | 53 | 0 of 60 (0 %) |
| `theory-order-maintenance` | yes | 20 | 0 of 19 (0 %) |
| `theory-ordered-algebras` | yes | 22 | 2 of 56 (3 %) |
| `theory-path-orders` | yes | 4 | 0 of 10 (0 %) |
| `theory-probability` | no | 37 | 0 of 39 (0 %) |
| `theory-shapes` | no | 10 | 1 of 28 (3 %) |
| `theory-sites` | yes | 81 | 3 of 162 (1 %) |
| `theory-spec-combinators` | yes | 4 | 0 of 4 (0 %) |
| `theory-stone-duality` | yes | 0 | 2 of 72 (2 %) |
| `theory-virtual-doctrines` | no | 15 | 1 of 118 (0 %) |
| `workflow-build-state` | no | 0 | 1 of 6 (16 %) |
| `workflow-coverage-guard` | no | 0 | 0 of 20 (0 %) |
| `workflow-debt-ledger` | no | 6 | 0 of 4 (0 %) |
| `workflow-gate` | no | 0 | 3 of 18 (16 %) |
| `workflow-github` | no | 0 | 0 of 7 (0 %) |
| `workflow-host-tools` | no | 5 | 0 of 27 (0 %) |
| `workflow-hotpath-guard` | no | 0 | 3 of 40 (7 %) |
| `workflow-lane-budget` | no | 1 | 0 of 21 (0 %) |
| `workflow-ledger-tasks` | no | 0 | 2 of 10 (20 %) |
| `workflow-parser-report` | no | no library | no library |
| `workflow-prose` | no | 2 | 0 of 32 (0 %) |
| `workflow-spec-cost` | no | 6 | 0 of 14 (0 %) |
| `workflow-sweep` | no | 0 | 0 of 26 (0 %) |
| `workflow-test-timing` | no | 1 | 0 of 14 (0 %) |
| `workflow-twin-census` | no | 0 | 0 of 8 (0 %) |

Crates under the emitter: 32 of 105.

Generic public items: 2579.

Public functions in the export fragment: 339 of 7919 (4 %).
