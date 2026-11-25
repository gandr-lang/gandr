# Twin census

A twin is a function of a crate that gandr source states. A crate is under the emitter when `gandr-runtime-emitter` depends on it by a normal or a build dependency, directly or through other crates. A twin of such a crate runs as an object, and not as a record that the runtime loads.

An item is generic when it has a type parameter or a trait bound. An entry under the C convention carries neither, so a generic item has no twin without a wrapper. The column counts the public functions, methods, types, traits and type aliases of the crate's library that are generic.

`twin-census --write` writes this file from `cargo metadata` and from the JSON that rustdoc writes for each library. `twin-census --check` refuses it when it is not the census of the workspace.

| Crate | Under the emitter | Generic items |
| ----- | ----------------- | ------------- |
| `boot-alloc` | yes | 0 |
| `boot-core` | no | 0 |
| `boot-io` | no | 0 |
| `core-checker` | no | 1 |
| `core-checker-base` | no | 123 |
| `core-checker-bridge` | no | 15 |
| `core-content` | yes | 34 |
| `core-fork` | yes | 4 |
| `core-incremental` | no | 37 |
| `core-nbe` | no | 14 |
| `core-nbe-base` | no | 12 |
| `core-publish` | no | 1 |
| `core-sequent` | yes | 4 |
| `core-session` | yes | 2 |
| `core-term` | yes | 151 |
| `core-unify` | no | 3 |
| `kernel-check-memo` | yes | 29 |
| `kernel-conversion-trace` | yes | 6 |
| `kernel-core` | yes | 8 |
| `kernel-core-base` | yes | 63 |
| `kernel-data` | yes | 75 |
| `kernel-strata` | yes | 0 |
| `kernel-term` | yes | 55 |
| `runtime-emitter` | the emitter | 12 |
| `runtime-net` | no | 0 |
| `runtime-rust-record` | no | 0 |
| `runtime-stencils` | yes | 2 |
| `storage-artifact` | no | 5 |
| `storage-chunker` | yes | 0 |
| `storage-records` | no | 15 |
| `storage-schema` | no | 17 |
| `storage-store` | no | 4 |
| `storage-values` | yes | 17 |
| `surface-agentic` | no | 3 |
| `surface-build-identity` | no | 0 |
| `surface-corpus` | no | 18 |
| `surface-diagnostics` | no | 26 |
| `surface-dispatcher` | no | 89 |
| `surface-driver` | no | no library |
| `surface-evaluate` | no | 1 |
| `surface-features` | no | 0 |
| `surface-format` | no | 0 |
| `surface-grammar` | no | 3 |
| `surface-layout` | no | 2 |
| `surface-lowering` | no | 1 |
| `surface-lowering-base` | no | 260 |
| `surface-lowering-capability` | no | 56 |
| `surface-lowering-exits` | no | 32 |
| `surface-lowering-expression` | no | 136 |
| `surface-lowering-identity` | no | 34 |
| `surface-lowering-model` | no | 93 |
| `surface-lowering-native` | no | 47 |
| `surface-lsp` | no | 3 |
| `surface-lsp-base` | no | 18 |
| `surface-lsp-core` | no | 11 |
| `surface-lsp-diagnostics` | no | 12 |
| `surface-lsp-navigation` | no | 8 |
| `surface-parser` | no | 0 |
| `surface-pretty` | no | 38 |
| `surface-render-remote` | no | 0 |
| `surface-render-terminal` | no | 0 |
| `surface-repl` | no | 8 |
| `surface-session` | no | 61 |
| `surface-syntax` | no | 0 |
| `surface-tui` | no | 5 |
| `theory-cell-complexes` | yes | 42 |
| `theory-cell-complexes-tools` | no | 6 |
| `theory-cellular-sheaves` | no | 26 |
| `theory-circuit-algebras` | yes | 16 |
| `theory-coherent-resolutions` | yes | 93 |
| `theory-computads` | no | 14 |
| `theory-decomposition-spaces` | no | 13 |
| `theory-deep-inference` | yes | 112 |
| `theory-discrete-morse` | yes | 56 |
| `theory-dynamic-graphs` | yes | 0 |
| `theory-e-graphs` | no | 19 |
| `theory-exact-reals` | yes | 17 |
| `theory-graded-posets` | yes | 12 |
| `theory-graphs` | yes | 47 |
| `theory-levitation` | yes | 165 |
| `theory-nominal-automata` | no | 53 |
| `theory-order-maintenance` | yes | 20 |
| `theory-ordered-algebras` | yes | 22 |
| `theory-path-orders` | yes | 4 |
| `theory-probability` | no | 37 |
| `theory-shapes` | no | 10 |
| `theory-sites` | yes | 81 |
| `theory-spec-combinators` | yes | 4 |
| `theory-stone-duality` | yes | 0 |
| `theory-virtual-doctrines` | no | 15 |
| `workflow-build-state` | no | 0 |
| `workflow-coverage-guard` | no | 0 |
| `workflow-debt-ledger` | no | 6 |
| `workflow-gate` | no | 0 |
| `workflow-github` | no | 0 |
| `workflow-host-tools` | no | 5 |
| `workflow-hotpath-guard` | no | 0 |
| `workflow-lane-budget` | no | 1 |
| `workflow-ledger-tasks` | no | 0 |
| `workflow-parser-report` | no | no library |
| `workflow-prose` | no | 2 |
| `workflow-spec-cost` | no | 6 |
| `workflow-sweep` | no | 0 |
| `workflow-test-timing` | no | 1 |
| `workflow-twin-census` | no | 0 |

Crates under the emitter: 32 of 105.

Generic public items: 2579.
