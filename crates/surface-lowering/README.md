# gandr-surface-lowering

Lowering the gandr surface into the core language: the molded syntax tree the parser builds in, call-by-push-value core terms, their origins and the module's attribute table out, or a located refusal that says why a form has no core reading.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `lower_module` reads a `gandr-surface-syntax` tree molded under a `gandr-surface-grammar` grammar and mints its declarations into a `gandr-core-term` arena. Each declared name becomes one `LoweredDeclaration` carrying its admission position, the cross-tree keys (`NodeKey`) of its signature and definition forms, an origin token, and a `DeclarationOutcome`: a completed signature and definition, an uncompleted signature, a bodiless definition, a shared native `DataSignature`, a sealed abstract type, or the declaration's `LoweringRefusal`. The module's attributes are resolved against a closed `AttributeRegistry` into an `AttributeTable` keyed by each declaration's `NodeKey`, and every minted core node's syntax origin is recorded in an `OriginTable`. Imports are kept and their aliases bound by the `namespace` engine, and every declared name is declared over an outermost `Recognition` scope. `FailureClass` sorts every refusal into the class a consumer acts on.

**Why.** A checker reads core terms, a diagnostic reads source spans, and an obligation ledger reads which declarations are still owed. The lowering is the one place all three are decided together: what the source means in the core fragment, where each core node came from, and whether a declaration that failed to lower failed because the author erred, because the fragment cannot represent it, or because the engine was misused — so no failure the engine refuses is mistaken for an obligation the author owes.

**How.** Every node is dispatched on the named kind the grammar resolves its mold to (`Pbg::named_kind`), and a form's children are split into its own tiles — the tiles of its own grammar rule, read by label — and the forms standing in its holes. A collection pass pairs each name's signature and definition and records which declaration owns every node. An ascending sweep over the level-order arena fixes each node's sort and binder frame from its parent, resolves names and literals, and decides every refusal; a descending sweep then mints each planned node over its already-minted children. Neither sweep recurses, and both spend one caller-set `LoweringBudget`.

## Provided features

- `lower_module`, `LoweringBudget` and `Fuel`: the whole surface-to-core step under one allowance.
- The static formers, the eager product with its pair, the `=>` alias and the dependent arrow `(x : A) -> C` it abbreviates, as `lower_module` writes them.
- `LoweredModule`, `LoweredDeclaration`, `DeclarationOutcome` and `DeclarationCount`: one declaration per name, in admission order.
- `DataIndex`, `DeclarationOutcome::Data` and `LoweredModule::data`: a data declaration lowered to its native signature, its constructors applied to their fields and its values matched by a decision tree of native eliminations.
- `CaseOrigin`, `ArmOrigin`, `OriginTable::case` and `OriginTable::cases`: per match, the core pattern table its arms are written in and the syntax nodes of its scrutinee, patterns and bodies; a pattern hole's identity is its syntax node.
- `def rec` and the descent claim `f[<]`: a recursive function lowered to one fixpoint over its last parameter, its evidence the claim the source writes, and `Insertion::Fixpoint` marking the inserted fixpoint.
- `type_atom`, `type_former`, `TypeAtom`, `TypeFormer`, `HeadArity` and `OperandCount`: the type-head tables by arity.
- `Scope`, `ScopeId`, `Frame`, `Bound`, `Mentioned`, `SurfaceName` and `binder_site::Absent`: the flat binder chain names resolve through, each frame carrying the type its binder was written with, whether a type names it, and the span it was written at.
- `OriginTable::binding` and `OriginTable::bindings`: the use-to-binder map, each core variable the lowering minted with the span of the binder it resolves to.
- `former_of`, `Former`, `FormName` and `Repair`: the named-kind dispatch and the names a diagnostic writes forms as.
- `LoweringRefusal`, `FragmentSort`, `FragmentBoundary` and `FormFault`: every refusal, located.
- `LoweringRefusal::classify` and `FailureClass`, the latter re-exported from `gandr-core-term`, which every producer of refusals in the core pipeline classifies into: the classifier.
- `AttributeRegistry`, `AttributeSchema`, `RegisteredAttribute`, `EditDistance`, `PayloadForm`, `PayloadVerdict`, `payload_form`, `payload_verdict`, `AttributeEntry`, `AttributeTable` and `AttributedCount`: the closed registry, its five diagnostics and the side table, filed for refused declarations too.
- `Documentation`, `DocumentationText`, `DocLink`, `LoweredModule::documentation` and `LoweredModule::documentations`: a declaration's documentation read from both spellings into one text, filed under its declaration's `NodeKey`, its links resolved; the whole filing, for a consumer that keeps it past the lowering.
- `Origin`, `OriginTable`, `OriginToken` and `OriginCount`: the origin of every minted node and every declaration.
- Source `?` and `?name` lower to core value or computation holes according to their term position. Occurrences have distinct `HoleId`s derived from their syntax nodes, and retain the usual written origins. The grammar already admits both spellings; no grammar artifact changes.
- `Provenance` and `Insertion`: whether a minted node was written by the author or inserted by the lowering, and which bridge an insertion is.
- `InferredExit`, `Exit`, `Explicitness` and `LoweredModule::inferred_exits`: a tail written without `return` or `become` takes the exit its polarity names — a value returned, a computation run in tail position — lowered to the term the keyword would have written, `Insertion::Return` marking an inferred return; each is listed at the tail's bytes, for a face to show the keyword the source left out and for the `explicit-exits` lint, which an `explicit_exits` attribute on a declaration or a top-level module asks for.
- `AskedRuns`, `NestedSite`, `RunSpelling`, `RunOperand`, `InferredRun` and `LoweredModule::inferred_runs`: a computation written where a value is read, held for the checker to run or suspend, and each run it inferred, listed for the `explicit-runs` lint.
- `namespace`: `Trie`, `Modifier`, `Scope`, the events and their handlers, and `Recognition` with its ordered `SeedTable`s and `ShadowPolicy`.
- `ImportDeclaration`, `ImportIndex`, `ImportUri` and `ModuleImports`: imports kept in source order with their aliases bound.
- `LoweredStructure`, `ValueComponent`, `ManifestComponent`, `manifest_type`, `Coerced`, `Container`, `Role`, `StructureIndex`, `AscriptionForm`, `LoweredModule::structures`, `LoweredModule::path_of` and `LoweredModule::structured_names`: modules flattened to named members, their stratum items and their structured names.
- Type members `type T = τ ;`, type paths `M.T`, abstract components `type T` and `type T : κ`, and `Recognized::ModuleType`: a module's types, named inside it and through its namespace.
- `DeclarationOutcome::Abstract`, `Sealing` and `SealedComponent`: an opaque ascription `:>` declaring one abstract type per abstract component, keyed by its site, and the atoms a sealed module exports.
- `model::derive`, `ModelSignature`, `LoweredModule::signs` and `LoweredSign`: `Model(S)` derived from a `sign` block's presentation, a module ascribed `: Model(S)` checked against it, and a sign's description and presentation handed to later passes; type members with parameters, `type Hom(a : Ob, b : Ob) = τ`, expanding where they are applied.

## Expected features

- **The grammar the tree was molded under.** `lower_module` takes the `Pbg` whose fingerprint the tree records; a tree of another grammar is refused before any mold is read.
- **A tree from the parser.** Any `SyntaxTree` is admissible, a repaired one included; the lowering refuses what the parser repaired rather than assuming a clean parse.
- **The source outlives the result.** A `LoweredModule` borrows the declared names from the source text the tree spans.
- **One arena per lowering.** Every id in a `LoweredModule` is read against the `CoreArena` that lowering wrote into.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Examples

```rust
use gandr_core_term::CoreArena;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

fn main() -> Result<(), Box<dyn core::error::Error>> {
    let pbg = built_in()?;
    let tree = parse(&pbg, SourceText::from("def x : Integer ; def x = 3 ;"))?.into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(&pbg, &tree, &mut arena, LoweringBudget::DEFAULT, Recognition::default())?;

    let [declaration] = module.declarations() else {
        unreachable!("one name is declared");
    };
    assert!(matches!(declaration.outcome(), DeclarationOutcome::Completed { .. }));
    Ok(())
}
```

The same example is the crate-level doctest. `cargo nextest run -p gandr-surface-lowering` runs the crate's tests; every fragment row a witness exercises is parsed from source by `gandr-surface-parser` and lowered in the same test, and a hand-built tree is used only for a shape the parser never emits.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The named-kind dispatch | [`form`](src/form.rs) |
| Repairs refused in place, the four boundaries out of the fragment | [`error`](src/error.rs) |
| Name resolution through tables | [`resolve`](src/resolve.rs) |
| Module collection, one refusal per declaration, module declarations | [`module`](src/module.rs) |
| Type members, abstract components and opaque ascription | [`module::sealing`](src/module/sealing.rs), [`lower::sealing`](src/lower/sealing.rs) |
| `Model(S)`: the derivation, sort inference over index terms, type families, and the instance check | [`model`](src/model.rs), [`module::model`](src/module/model.rs), [`lower::model`](src/lower/model.rs) |
| Descriptions, one producer for a data form, signature blocks, cells and circuit wiring | [`description`](src/description.rs), [`description::sign`](src/description/sign.rs), [`desc_cells`](src/desc_cells.rs) |
| The namespace engine, its trie and the outermost scope | [`namespace`](src/namespace.rs), [`namespace::trie`](src/namespace/trie.rs), [`namespace::recognition`](src/namespace/recognition.rs) |
| Imports | [`import`](src/import.rs) |
| Sorts, function tails, blocks, insertions, universes, type operators, products, literals, the two sweeps | [`lower`](src/lower.rs) |
| Native data, the match and recursive functions | [`lower::native`](src/lower/native.rs) |
| Early exits: the survey, the commuting, the cut and the exit a tail's polarity infers; the decisions and their alternatives | [`lower::exits`](src/lower/exits.rs), [`src/lib.rs`](src/lib.rs), [`lower`](src/lower.rs) |
| Nested computations: the lowering's record of each inferred run, the attribute's ask and how its `run` is spelled | [`lower::runs`](src/lower/runs.rs), [`lower`](src/lower.rs) |
| The failure classifier | [`classify`](src/classify.rs) |
| Attributes and documentation | [`attribute`](src/attribute.rs), [`doc`](src/doc.rs) |
| Origins | [`origin`](src/origin.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

The behavioural floor — the description suites, and the module and namespace tests held until their readers exist — is tracked in [#212](https://github.com/gandr-lang/gandr/issues/212).

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
