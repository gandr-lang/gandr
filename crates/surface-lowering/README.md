# gandr-surface-lowering

Lowering the gandr surface into the core language: the molded syntax tree the parser builds in, call-by-push-value core terms, their origins and the module's attribute table out, or a located refusal that says why a form has no core reading.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `lower_module` reads a `gandr-surface-syntax` tree molded under a `gandr-surface-grammar` grammar and mints its declarations into a `gandr-core-term` arena. Each declared name becomes one `LoweredDeclaration`, whose `DeclarationOutcome` ([`module`](src/module.rs)) names what became of it. The module's attributes are resolved against a closed `AttributeRegistry` into an `AttributeTable` keyed by each declaration's `NodeKey`, and every minted core node's syntax origin is recorded in an `OriginTable`. Imports bring a sibling source's declarations in, and every declared name is declared over an outermost `Recognition` scope. `FailureClass` sorts every refusal into the class a consumer acts on.

**Why.** A checker reads core terms, a diagnostic reads source spans, and an obligation ledger reads which declarations are still owed. The lowering is the one place all three are decided together: what the source means in the core fragment, where each core node came from, and whether a declaration that failed to lower failed because the author erred, because the fragment cannot represent it, or because the engine was misused — so no failure the engine refuses is mistaken for an obligation the author owes.

**How.** Each node is dispatched on the named kind its mold resolves to (`Pbg::named_kind`); a collection pass pairs signatures with definitions, and two sweeps over the level-order tree, neither recursive and both under one `LoweringBudget`, plan every node and then mint it. The crate rustdoc's _The grammar names every form_ and _Two sweeps, no recursion_ hold the mechanism.

## Provided features

- `lower_module`, `LoweringBudget` and `Fuel`: the whole surface-to-core step under one allowance.
- The static formers, the eager product with its pair, the infix sum, the `=>` alias and the dependent arrow `(x : A) -> C` it abbreviates, as `lower_module` writes them.
- `LoweredModule`, `LoweredDeclaration`, `DeclarationOutcome` and `DeclarationCount`: one declaration per name, in admission order.
- `DataIndex`, `DeclarationOutcome::Data` and `LoweredModule::data`: a data declaration lowered to its native signature, constructors and matches (`lower::native`).
- `CaseOrigin`, `ArmOrigin`, `PatternSpan`, `OriginTable::case` and `OriginTable::cases`: per match, its pattern table, the syntax nodes of its scrutinee, patterns and bodies, and each pattern's span.
- `def rec` and the descent claim `f[<]`: a recursive function lowered to one fixpoint (`lower::native`), `Insertion::Fixpoint` marking it.
- `type_atom`, `type_former`, `TypeAtom`, `TypeFormer`, `HeadArity` and `OperandCount`: the type-head tables by arity.
- `Scope`, `ScopeId`, `Frame`, `Bound`, `Mentioned`, `SurfaceName` and `binder_site::Absent`: the flat binder chain names resolve through, each frame carrying the type its binder was written with, whether a type names it, the span it was written at and the zone it binds in.
- `OriginTable::binding` and `OriginTable::bindings`: the use-to-binder map, each core variable the lowering minted with the span of the binder it resolves to.
- `former_of`, `Former`, `FormName` and `Repair`: the named-kind dispatch and the names a diagnostic writes forms as.
- `LoweringRefusal`, `FragmentSort`, `FragmentBoundary` and `FormFault`: every refusal, located.
- `LoweringRefusal::classify` and `FailureClass`, the latter re-exported from `gandr-core-term`, which every producer of refusals in the core pipeline classifies into: the classifier.
- The closed attribute registry, its five diagnostics and the side table, filed for refused declarations too; [`attribute`](src/attribute.rs) names its types.
- `Documentation`, `DocumentationText`, `DocLink`, `LoweredModule::documentation` and `LoweredModule::documentations`: a declaration's or a module's documentation read from both spellings into one text, filed under its form's `NodeKey`, its links resolved; the whole filing, for a consumer that keeps it past the lowering.
- `Origin`, `OriginTable`, `OriginToken` and `OriginCount`: the origin of every minted node and every declaration.
- Source `?`, `?name` and the splice `~t` lower to core holes by their term position (`lower`).
- `Provenance` and `Insertion`: whether a minted node was written by the author or inserted by the lowering, and which bridge an insertion is.
- `InferredExit`, `Exit`, `Explicitness` and `LoweredModule::inferred_exits`: the exit a tail written without `return` or `become` takes by its polarity, listed at the tail's bytes for a face and the `explicit-exits` lint.
- `AskedRuns`, `NestedSite`, `RunSpelling`, `RunOperand`, `InferredRun` and `LoweredModule::inferred_runs`: a computation written where a value is read, held for the checker to run or suspend, and each run it inferred, listed for the `explicit-runs` lint.
- `namespace`: `Trie`, `Modifier`, `Scope`, the events and their handlers, and `Recognition` with its ordered `SeedTable`s and `ShadowPolicy`.
- `lower_unit`, `Unit`, `SourceIndex`, `ImportTarget` and the `Import*` types: sources lowered into one arena, each reading its siblings through its imports; `ClosureLowering`: a closure lowered once, resumed per document; its `alone`, `resume_onto` and `Onto`: its own module, and a document lowered onto the arena it was judged over.
- `LoweredStructure`, `LoweredModule::structures`, `LoweredModule::path_of` and `LoweredModule::structured_names`: modules flattened to named members, their stratum items and their structured names; [`module`](src/module.rs) names the types they are read through.
- Type members `type T = τ ;`, type paths `M.T`, abstract components `type T` and `type T : κ`, and `Recognized::ModuleType`: a module's types, named inside it and through its namespace.
- `DeclarationOutcome::Abstract`, `Sealing` and `SealedComponent`: an opaque ascription `:>` declaring one abstract type per abstract component, keyed by its site, and the atoms a sealed module exports.
- `model::derive`, `ModelSignature`, `LoweredModule::theories` and `LoweredTheory`: `Model(S)` derived from the `Theory` value `theory S` defines, a module ascribed `: Model(S)` checked against it, packed by `pack M at Model(S)`, and a theory's description and presentation handed to later passes; type members with parameters (`module::model`).
- Binary sessions: a session type read whole into one protocol; `send`, `select`, `offer` and `close`, and the statements `recv(c) as x ;` and `fork (c : S) t as d ;`, lowered to core session actions; `fork !`, `dup`, `acquire` and `release` reserved by name.
- Worlds: `world w ;` as `DeclarationOutcome::World`, `A at w`, `hold`, `leta`, `migrate [w]`, `mobile type T` as `Mark`, `@[ entry(…) ]` as `LoweredModule::worlds`.

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

The same example is the crate-level doctest. `cargo nextest run -p gandr-surface-lowering` runs the crate's tests; how their witnesses build their trees is in the crate rustdoc.

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
| Descriptions, one producer for a data form, signature blocks, cells and circuit wiring | [`description`](src/description.rs), [`description::theory`](src/description/theory.rs), [`desc_cells`](src/desc_cells.rs) |
| The namespace engine, its trie and the outermost scope | [`namespace`](src/namespace.rs), [`namespace::trie`](src/namespace/trie.rs), [`namespace::recognition`](src/namespace/recognition.rs) |
| Imports | [`import`](src/import.rs) |
| Sorts, function tails, blocks, insertions, universes, type operators, products, literals, the two sweeps | [`lower`](src/lower.rs) |
| Native data, the match and recursive functions | [`lower::native`](src/lower/native.rs) |
| Early exits and loops: the survey, the commuting, the cut, inferred exits and a loop's fixpoint | [`lower::exits`](src/lower/exits.rs), [`lower::loops`](src/lower/loops.rs), [`src/lib.rs`](src/lib.rs), [`lower`](src/lower.rs) |
| Nested computations: the lowering's record of each inferred run, the attribute's ask and how its `run` is spelled | [`lower::runs`](src/lower/runs.rs), [`lower`](src/lower.rs) |
| Binary sessions: protocols, endpoints, actions and the statements binding them | [`lower::session`](src/lower/session.rs) |
| Worlds | [`module::world`](src/module/world.rs), [`lower::world`](src/lower/world.rs) |
| The failure classifier | [`classify`](src/classify.rs) |
| Attributes and documentation | [`attribute`](src/attribute.rs), [`doc`](src/doc.rs) |
| Origins | [`origin`](src/origin.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

## References

- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: the quantities design (§ quant-counts) — a finite grade and a cell's hole count are one count.
- `vault:01a16b8f-6aec-7282-b400-974aedeaa341` — lineage: the rows design (§ rows-rule-effects-are-theories) — a scope's subject normalises by its theory's laws.
- `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the effect-modalities design (§ the four laws) — which laws are rules.
- `vault:01a14daa-a317-7d92-bd17-3f20e87634cd` — background: the theories design — what `with sort x = A` fixes.
- `vault:01a15620-7fbe-7030-a3af-07ffa620eed2` — background: the syntax bikeshed — the row entry's spelling.
- `vault:01a178aa-a7bd-7d03-a728-feae5af9d1a8` — background: the foreign-calls design — an extern block is an effect interface.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
