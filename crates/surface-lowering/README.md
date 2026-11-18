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

**What.** `lower_module` reads a `gandr-surface-syntax` tree molded under a `gandr-surface-grammar` grammar and mints its declarations into a `gandr-core-term` arena. Each declared name becomes one `LoweredDeclaration`, whose `DeclarationOutcome` ([`module`](../surface-lowering-base/src/module.rs)) names what became of it. The crate rustdoc's _Side tables_ holds the attributes, the origins and the imports. `FailureClass` sorts every refusal into the class a consumer acts on.

**Why.** A checker reads core terms, a diagnostic reads source spans, and an obligation ledger reads which declarations are still owed. The lowering is the one place all three are decided together: what the source means in the core fragment, where each core node came from, and the class of each failure, which [`classify`](../surface-lowering-base/src/classify.rs) states.

**How.** The crate rustdoc holds the mechanism: the dispatch on each mold's named kind (_The grammar names every form_), and the two sweeps that plan and mint every node under one `LoweringBudget` (_Two sweeps, no recursion_). The sweeps compile in `gandr-surface-lowering-expression`. This crate is their host: it holds the context, the closure, the dispatch of the families and the entry points.

## Provided features

- `lower_module`, `LoweringBudget` and `Fuel`: the whole surface-to-core step under one allowance.
- The static formers, the eager product with its pair, the infix sum, the `=>` alias, the dependent arrow `(x : A) -> C` it abbreviates and the linear `⊸`.
- `LoweredModule`, `LoweredDeclaration`, `DeclarationOutcome` and `DeclarationCount`: one declaration per name, in admission order.
- `DataIndex`, `DeclarationOutcome::Data` and `LoweredModule::data`: a data declaration lowered to its native signature, constructors and matches (`lower::native`).
- `CaseOrigin`, `ArmOrigin`, `PatternSpan`, `OriginTable::case` and `OriginTable::cases`: each match's syntax origins ([`origin`](../surface-lowering-base/src/origin.rs)).
- `def rec` and the descent claim `f[<]`: a recursive function lowered to one fixpoint ([`lower::native`](src/lower/native.rs)).
- `type_atom`, `type_former`, `TypeAtom`, `TypeFormer`, `HeadArity` and `OperandCount`: the type-head tables by arity.
- `Scope`, `ScopeId`, `Frame`, `Bound`, `Mentioned`, `SurfaceName` and `binder_site::Absent`: the flat binder chain names resolve through ([`resolve`](../surface-lowering-base/src/resolve.rs)).
- `OriginTable::binding` and `OriginTable::bindings`: the use-to-binder map ([`origin`](../surface-lowering-base/src/origin.rs)).
- `Shadow` and `LoweredModule::shadows`: each binder that hides a binding, and the binding it hides.
- `former_of`, `Former`, `FormName` and `Repair`: the named-kind dispatch and the names a diagnostic writes forms as.
- `LoweringRefusal`, `FragmentSort`, `FragmentBoundary` and `FormFault`: every refusal, located.
- `LoweringRefusal::classify` and `FailureClass`, re-exported from `gandr-core-term`: the classifier every producer of refusals in the core pipeline classifies into.
- The closed attribute registry, its five diagnostics and the side table, filed for refused declarations too; [`attribute`](../surface-lowering-base/src/attribute.rs) names its types.
- `Documentation`, `DocumentationText`, `DocLink`, `LoweredModule::documentation` and `LoweredModule::documentations`: a declaration's, a module's or a source's documentation as one text, its links resolved ([`doc`](../surface-lowering-base/src/doc.rs)).
- `Origin`, `OriginTable`, `OriginToken` and `OriginCount`: the origin of every minted node and every declaration.
- Source `?`, `?name` and the splice `~t` lower to core holes by their term position (`lower`).
- `Provenance` and `Insertion`: whether a minted node was written by the author or inserted by the lowering, and which bridge an insertion is.
- `InferredExit`, `Exit`, `Explicitness` and `LoweredModule::inferred_exits`: the exit each tail written without `return` or `become` takes.
- `InferredRun`, `LoweredModule::inferred_runs` and the types [`lower::runs`](../surface-lowering-base/src/lower/runs.rs) names: each run inferred where a value is read.
- The tables, the refusals, the descriptions and the module pass, from `gandr-surface-lowering-base` and named at their old paths: `namespace`, `description`, `model`, `module` and the rest of the base's modules.
- `lower_unit` and the types [`unit`](../surface-lowering-base/src/unit.rs) names: sources lowered into one arena; `ClosureLowering` and the calls [`lower::closure`](src/lower/closure.rs) names: a closure lowered once.
- `LoweredStructure` and `LoweredModule::structures`: modules flattened to named members, their stratum items and their structured names, read through the types [`module`](../surface-lowering-base/src/module.rs) names.
- Type members `type T = τ ;`, type paths `M.T`, abstract components `type T` and `type T : κ`, and `Recognized::ModuleType`: a module's types, named inside it and through its namespace.
- `DeclarationOutcome::Abstract`, `Sealing` and `SealedComponent`: an opaque ascription `:>`, its abstract types and the atoms a sealed module exports.
- `model::derive`, `ModelSignature`, `LoweredModule::theories` and `LoweredTheory`: `Model(S)` derived, checked and packed, type members with parameters, and a `path`'s functions and round trips.
- Binary sessions: session types, actions and the statements binding them, lowered to core session actions ([`lower::session`](src/lower/session.rs)).
- Worlds: `world`, `requires`, `offers`, `at`, `hold`, `migrate`, `mobile` and `@[ entry(…) ]` ([`module::world`](../surface-lowering-base/src/module/world.rs)).

## Expected features

- **The grammar the tree was molded under.** `lower_module` refuses a tree whose fingerprint is not its `Pbg`'s.
- **A tree from the parser.** Any `SyntaxTree` is admissible, and the lowering refuses what the parser repaired.
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

    let [declaration] = *module.declarations().iter().collect::<Vec<_>>() else {
        unreachable!("one name is declared");
    };
    assert!(matches!(declaration.outcome(), DeclarationOutcome::Completed { .. }));
    Ok(())
}
```

The same example is the crate-level doctest.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The named-kind dispatch | [`form`](../surface-lowering-base/src/form.rs) |
| Repairs refused in place, the four boundaries out of the fragment | [`error`](../surface-lowering-base/src/error.rs) |
| Name resolution through tables | [`resolve`](../surface-lowering-base/src/resolve.rs) |
| The module pass: collection, one refusal per declaration, module declarations, imports, documentation, and the collected halves of sealing, `Model(S)` and worlds | the base's [README](../surface-lowering-base/README.md) |
| Type members, abstract components and opaque ascription | [`lower::sealing`](../surface-lowering-expression/src/lower/sealing.rs) |
| `Model(S)`: the derivation, sort inference over index terms, type families, and the instance check | [`model`](../surface-lowering-base/src/model.rs), [`lower::model`](src/lower/model.rs) |
| Descriptions, one producer for a data form, signature blocks, cells and circuit wiring | [`description`](../surface-lowering-base/src/description.rs), [`description::theory`](../surface-lowering-base/src/description/theory.rs), [`desc_cells`](../surface-lowering-base/src/desc_cells.rs) |
| The namespace engine, the per-node table, the form stretches and the circuit readings | `gandr-surface-lowering-base` |
| Sorts, function tails, blocks, insertions, universes, type operators, products, literals, the two sweeps | `gandr-surface-lowering-expression`'s [`lower`](../surface-lowering-expression/src/lower.rs) |
| Native data, the match and recursive functions | [`lower::native`](src/lower/native.rs) |
| Early exits and loops: the survey, the commuting, the cut, inferred exits and a loop's fixpoint | [`lower::exits`](src/lower/exits.rs), [`lower::loops`](src/lower/loops.rs), [`src/lib.rs`](src/lib.rs), `gandr-surface-lowering-expression`'s [`lower`](../surface-lowering-expression/src/lower.rs) |
| Nested computations: the lowering's record of each inferred run, the attribute's ask and how its `run` is spelled | [`lower::runs`](../surface-lowering-base/src/lower/runs.rs), `gandr-surface-lowering-expression`'s [`lower`](../surface-lowering-expression/src/lower.rs) |
| Binary sessions: protocols, endpoints, actions and the statements binding them | [`lower::session`](src/lower/session.rs) |
| Worlds | [`lower::world`](../surface-lowering-expression/src/lower/world.rs) |
| The failure classifier | [`classify`](../surface-lowering-base/src/classify.rs) |
| Attributes | [`attribute`](../surface-lowering-base/src/attribute.rs) |
| Origins | [`origin`](../surface-lowering-base/src/origin.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. The module pass reads nothing of the lowering's context, so it compiles in the base, and this crate reads it there.
- `vault:01a178ab-2ecf-7893-afda-f14010a8acbe` — exemplar: the namespace design — a shadow is an event, never a prohibition.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
