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

**What.** The vocabulary the lowering states its answers in, the description route and the module pass. The refusals, their classes and the features not yet built; the forms, the names and the binder scope; the origin table, the attributes, the units, the prelude and the written imports; the description of `data`, `codata` and `theory` declarations, their cells, the coincidence of their rules, the rule certificate, the derived equations, `Model(S)` and the described types. Also the namespace engine, the per-node table, the form stretches of a tree and the circuit readings of a rule's body. The module pass collects the declarations of a module by name, reads its imports, plans its operations and reads its documentation, and the lowered module it fills is the record the checker reads. `gandr-surface-lowering` names each module at its old path.

**Why.** The lowering is the longest crate in the build of the driver. A part that reads nothing of the lowering compiles in a crate of its own, before the lowering and beside its code generation. Each later split of the lowering adds its parts here or in a family crate over this one.

**How.** Each module states its mechanism and its decisions in its rustdoc. A witness of an item is a test of this crate, or a test of `gandr-surface-lowering` spelled with that package's name, where the case lowers a source. The integration target takes `gandr-surface-lowering` as a dev-dependency, its `fixture` feature on, so a case can lower a unit over this crate's items. The `fixture` feature opens the test fixtures to the tests of `gandr-surface-lowering`.

## Provided features

- `LoweringRefusal`, `FormFault`, `FragmentBoundary` and the other refusal payloads ([`error`](src/error.rs)); `FailureClass` for each refusal ([`classify`](src/classify.rs)); `Unbuilt` ([`unbuilt`](src/unbuilt.rs)).
- `LoweringBudget` and `Fuel`: the allowance of one lowering and the tank each charged pass spends from ([`budget`](src/budget.rs)).
- `FormName`, `Former` and the named-kind dispatch ([`form`](src/form.rs)); `SurfaceName`, the type-head tables and the binder `Scope` ([`resolve`](src/resolve.rs)).
- `Origin`, `OriginToken` and `OriginTable` ([`origin`](src/origin.rs)); `AttributeRegistry` and `AttributeTable` ([`attribute`](src/attribute.rs)).
- `Unit` ([`unit`](src/unit.rs)), the prelude's text ([`prelude`](src/prelude.rs)), `WrittenImport` and `ImportUri` ([`written_import`](src/written_import.rs)), `Role` and `Visibility` ([`slot`](src/slot.rs)), `Layered` and `LayeredList` ([`layered`](src/layered.rs)).
- `elaborate_descriptions` ([`description`](src/description.rs)), `elaborate_desc_cells` ([`desc_cells`](src/desc_cells.rs)), the coincidence check ([`coincide`](src/coincide.rs)), `rule_certificate` ([`certify`](src/certify.rs)), the derived equations ([`derive`](src/derive.rs)), `Presentation` and `Model(S)` ([`model`](src/model.rs)), and `described_types` ([`described`](src/described.rs)).
- `namespace`: the trie, the scope, the events, their handlers and `Recognition` ([`namespace`](src/namespace.rs)).
- `NodeTable`: a per-node table whose cells a suspended lowering shares with each lowering resumed from it ([`table`](src/table.rs)).
- `ByForm`, `FormStretch`, `FormPlace` and `At`: the stretch of each top-level form among a tree's positions ([`by_form`](src/by_form.rs)).
- `CircuitReading`, `circuit_wiring`, `circuit_canon` and `embed_circuit_rule`: a rule's body as a wiring diagram, its spider canon and its embeddings ([`circuit::embed`](src/circuit/embed.rs)).
- `LoweredModule`, `LoweredDeclaration`, `DeclarationOutcome` and the collection pass that fills them ([`module`](src/module.rs)); `ModuleImports` and `ImportDeclaration` ([`import`](src/import.rs)); `plan_operation` and `mint_operation` ([`operation`](src/operation.rs)); `Documentation` and `read_doc` ([`doc`](src/doc.rs)); the brackets a block's layout misplaces ([`layout`](src/layout.rs)).
- `Exit`, `InferredExit`, `InferredRun` and the other records the module pass and the lowering share, and `parse_literal` ([`lower`](src/lower.rs)).
- With the `fixture` feature, the test fixtures: parsed and hand-built trees over the built-in grammar ([`fixture`](src/fixture.rs)).

## Expected features

- **`alloc`.** The crate is `no_std` with `alloc`.
- **A tree from the parser.** The description route and the form stretches read a `SyntaxTree` that `gandr-surface-parser` builds.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The refusals, their classes and the features not built | [`error`](src/error.rs), [`classify`](src/classify.rs), [`unbuilt`](src/unbuilt.rs) |
| The forms, the names and the binder scope | [`form`](src/form.rs), [`resolve`](src/resolve.rs) |
| The origin table and the attributes | [`origin`](src/origin.rs), [`attribute`](src/attribute.rs) |
| The units, the prelude and the written imports | [`unit`](src/unit.rs), [`prelude`](src/prelude.rs), [`written_import`](src/written_import.rs) |
| The description route | [`description`](src/description.rs), [`desc_cells`](src/desc_cells.rs), [`coincide`](src/coincide.rs), [`certify`](src/certify.rs) |
| A theory's models and its derived equations | [`model`](src/model.rs), [`derive`](src/derive.rs) |
| The types a described node states | [`described`](src/described.rs) |
| The namespace engine, its trie and the outermost scope | [`namespace`](src/namespace.rs), [`namespace::trie`](src/namespace/trie.rs), [`namespace::recognition`](src/namespace/recognition.rs) |
| The per-node table and its shared cells | [`table`](src/table.rs) |
| The form stretches | [`by_form`](src/by_form.rs) |
| Circuit bodies as wiring diagrams | [`circuit`](src/circuit.rs), [`circuit::embed`](src/circuit/embed.rs) |
| The module pass: collection by name, module declarations, sealing, `Model(S)` members, worlds and foreign blocks | [`module`](src/module.rs), [`module::sealing`](src/module/sealing.rs), [`module::model`](src/module/model.rs), [`module::world`](src/module/world.rs), [`module::foreign`](src/module/foreign.rs) |
| Imports, operations, documentation and layout | [`import`](src/import.rs), [`operation`](src/operation.rs), [`doc`](src/doc.rs), [`layout`](src/layout.rs) |
| The records the module pass and the lowering share | [`lower::exits`](src/lower/exits.rs), [`lower::runs`](src/lower/runs.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. A crate boundary encloses a strongly connected component of the module graph, so the base takes the lowering's tables, refusals, descriptions and module pass whole.
- `vault:01a178aa-61bf-70f2-a24f-b3a69dfcd199` — newest: a merge on a marked wire is a spider.
- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: the quantities design (§ quant-counts) — a finite grade and a cell's hole count are one count.
- `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the effect-modalities design (§ the four laws) — which laws are rules.
- `vault:01a178aa-e578-7e31-8903-9f223de2dd91` — anchor: the ornaments design — a mutual block reads as one description.
- `vault:01a178aa-aa31-70c2-bdff-7d4f48020c0a` — anchor: the data design — a sibling field is a recursive occurrence.
- `vault:01a178aa-b5ea-75c1-8677-c85c447790b4` — anchor: the implicit-arguments design — a telescope on no function is malformed source.
- `vault:01a178aa-a7bd-7d03-a728-feae5af9d1a8` — background: the foreign-calls design — an extern block is an effect interface.
- `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — lineage: a flow is a functor, and `via` its application.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — lineage: a flow is named, never found.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — lineage: a renaming mints no constant.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: the presented-spaces plan (§ presented-spaces-crates) — the face cover reads the meet of two faces from a graded poset of the faces of a record type.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
