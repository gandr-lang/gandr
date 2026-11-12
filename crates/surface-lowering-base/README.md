# gandr-surface-lowering-base

The base of gandr's lowering: the parts of `gandr-surface-lowering` that read nothing of the lowering itself. The lowering compiles over this crate, so the two crates' code generation runs at the same time.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The namespace engine, the per-node table, the form stretches of a tree and the circuit readings of a rule's body. `gandr-surface-lowering` re-exports `namespace` and `circuit` at their old paths.

**Why.** The lowering is the longest crate in the build of the driver. A part that reads nothing of the lowering compiles in a crate of its own, before the lowering and beside its code generation. Each later split of the lowering adds its parts here or in a family crate over this one.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are tests of this crate. The integration target takes `gandr-surface-lowering` as a dev-dependency, so a case can lower a unit over this crate's items.

## Provided features

- `namespace`: the trie, the scope, the events, their handlers and `Recognition` ([`namespace`](src/namespace.rs)).
- `NodeTable`: a per-node table whose cells a suspended lowering shares with each lowering resumed from it ([`table`](src/table.rs)).
- `ByForm`, `FormStretch`, `FormPlace` and `At`: the stretch of each top-level form among a tree's positions ([`by_form`](src/by_form.rs)).
- `CircuitReading`, `circuit_wiring`, `circuit_canon` and `embed_circuit_rule`: a rule's body as a wiring diagram, its spider canon and its embeddings ([`circuit::embed`](src/circuit/embed.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A tree from the parser.** The form stretches read a `SyntaxTree` that `gandr-surface-parser` builds.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The namespace engine, its trie and the outermost scope | [`namespace`](src/namespace.rs), [`namespace::trie`](src/namespace/trie.rs), [`namespace::recognition`](src/namespace/recognition.rs) |
| The per-node table and its shared cells | [`table`](src/table.rs) |
| The form stretches | [`by_form`](src/by_form.rs) |
| Circuit bodies as wiring diagrams | [`circuit`](src/circuit.rs), [`circuit::embed`](src/circuit/embed.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. A crate boundary encloses a strongly connected component of the module graph, so the base takes the four leaves whole.
- `vault:01a178aa-61bf-70f2-a24f-b3a69dfcd199` — newest: a merge on a marked wire is a spider.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
