# gandr-core-checker

The core checking judgement: call-by-push-value core terms and a module of name-free declarations in, one verdict per declaration and the obligations the module owes out, every refusal classified by whose fact it is, and every acceptance re-derived by the kernel and exported under the producer's names.

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

**What.** `check_module` judges name-free `Declaration`s in a `CheckingContext` over a core arena. Its `Verdict` records an admitted data signature, a checked body, a synthesised type, an owed hole, a suspension or a refusal. The ledger collects holes; refusal classification separates malformed source, unimplemented features and engine faults. The kernel independently checks the exportable pure fragment.

**Why.** A frontend needs stable per-declaration verdicts that distinguish what the author owes from what is wrong. A mode per former and comparison only at mode changes are enforced by lint and module visibility, not review.

**How.** One goal-and-frame machine charges each transition to `CheckBudget`; [`src/lib.rs`](src/lib.rs) states the decisions that shape it, and each module the boundary it owns.

## Provided features

- `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp`, `Synthesised` and `Checked`: the four directed faces.
- Pairs, static lambdas and static applications in the faces, by the rules [`judgement`](src/judgement.rs) tabulates.
- Native list introductions against `List A` and the pure fold, by the rules [`judgement`](src/judgement.rs) states.
- `ConversionCount`: the declared projection of the conversion boundary, returned by every face.
- `form_value_type`, `form_comp_type`, `FormedValueType` and `FormedCompType`: formation as a judgement, and the types the check faces take.
- `type_value`, `type_module`, `Typing`, `Formed`, `Typings` and `Formations`: the typed run, keeping the type of every term it judged, refused ones too, and the level of each type it formed or `Formations` names.
- `classify_value_type`, `classify_comp_type` and `level_of`: the unique classifier of each formed type.
- `CodeDefinitions`, `Certificate`, `Unfolded`, `unfolding::Absent` and `Lift`: static definitions, certified reductions and recorded universe lifts.
- `Declaration`, `DeclarationContent` and `OriginToken`: name-free value/data input.
- `check_declaration`, `check_module`, `Verdict`, `Judged` and `ModuleReport`: one verdict per declaration, retaining accepted value definitions, native data signatures and recorded lifts.
- `Nesting`, `NestedElaboration` and `ModuleReport::nested_elaborations`: each computation written where a value is read, run or suspended by the type expected there, and the body rebuilt with every run bound.
- `Funext`, `FunextStep`, `Evaluation`, `Reading`, `Stalled`, `evaluated::Absent`, `ModuleReport::funexts`, `Equivalence`, `ModuleReport::equivalences`, `Reflexivity`, `converted::Absent`, `ModuleReport::reflexivities`, `EndpointRelation` and `ModuleReport::relations`: function extensionality, `equiv(f, g)`, reflexivity and the path endpoints a type conversion relates decided by computation, each with the traces the kernel replays; `ua::derive` and `ModuleReport::natives`: `ua_n` at every certified stratum, and the native paths it and `pathProduct` cross as.
- `check_declaration_supported`, `Supported`, `Support`, `Consulted` and `CheckingContext::adopt`: query-specific value/data answers and adoption into the new prefix.
- `CheckingContext`, `CheckBudget` and `signature_table::Absent`: context, admission tables and judgment allowance.
- `ModuleRun`, `Checkpoint`, `CheckingContext::checkpoint` and `CheckingContext::resume`: a module judged in stretches, each continuing the last one's state.
- `Absence`, `ObligationEntry`, `ObligationLedger` and `ObligationCount`: the absence-only ledger.
- `CheckRefusal`, `Mismatch`, `CheckingForm`, `ExpectedShape`, `UnadmittedFormer`, `TermNode`, `TypeNode` and `CoreNode`: named refusals and responsible nodes.
- `StaticArity`, `ArgumentPosition` and family refusals preserve the failing argument or arity.
- `CheckRefusal::classify` assigns producer-failure classes ([`refusal`](src/refusal.rs)).
- `CheckRefusal::compared`, `Compared` and `compared::Absent`: the types a refusal sets against each other, the one its rule expected and the one it found, as nodes a face spells.
- `Failure`, `Obligation`, `FrameRole`, `FoldPremise`, `Pursuit`, `Stage`, `judged` and `ModuleReport::failures`: what the checking machine held when it refused, kept per refused body by position ([`failure`](src/failure.rs)).
- `bridge`: independent readmission of accepted declarations into a fresh kernel environment — `readmit`, `Readmission` and its canonical `export`; `readmit_resuming`, `Crossed` and `export_resuming`, a prefix resumed from a record; `Readmitted`, `Outcome`, `ArtifactAudit`, `Replayed` and `Refusal`: what became of each origin, what it rests on, what was replayed, why it did not cross.
- `Retirement`, `Demand`, `Polled`, `Unretired` and `bridge::readmit_retiring`: a run polled between its steps ([`retire`](src/retire.rs)).
- The hole surface: term holes, marks and the unknown type in the faces; `elaborate_value`, `elaborate_comp`, `Elaboration`, `MarkEntry` and `Direction`; `cover`, `Coverage`, `Exhaustiveness`, `Redundancy` and `CoverageFault`; `bridge::Refusal::Hole` and `bridge::Refusal::Unknown`.
- `Verdict::Suspended` and `ModuleReport::suspensions`: a judgement held on an owed code hole ([`elaboration`](src/elaboration.rs)).
- `CheckRefusal::TacticRefused`, `TacticFault`: a splice's tactic run at its goal ([`tactic`](src/tactic.rs)).
- `staging::check`, `staging::Program`, `staging::Allowance`, `staging::Checked`, `staging::Readmission`, `staging::Stages`, `staging::ProgramError` and `staging::SourceIndex`: a staged program checked end to end on the caller's fork.
- `stage::compile`, `stage::Program::admit` and `stage::Program::execute`: certified first-order residual readmission for the experimental stage universe.
- `template`: guarded families of staging equations with ordinary replay as authority, the `template::Memo` that drafts a family from its key's last template, and the adapter into the kernel's guarded admission.

## Expected features

- **One arena per context.** Every id a declaration carries resolves in the `CoreArena` the `CheckingContext` was built over; an id that does not is refused as a dangling node, never read.
- **One arena per report.** `bridge::readmit` takes, mutably, the arena the report was judged over: it reads every id there, refusing one that does not resolve as a dangling node, and mints there the reduct of each static step it takes.
- **One writer per arena.** `CheckingContext::new` holds the arena mutably for the context's life, and the judgement mints into it; a caller reads it through `CheckingContext::arena` while the context lives.
- **Ascending admission positions.** Declarations are offered in admission order; a position not above every one admitted before it is refused.
- **Closed bodies.** A body is closed over the context's binders, which are empty between judgements; a producer that resolves every binder, as a lowering does, never trips the unbound-index refusal.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Examples

```rust
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

// def owed : Integer ;
let mut arena = CoreArena::new();
let integer = arena.value_type_base(BaseType::Integer);
let declarations = [Declaration::new(
    ConstantIndex::from(0_usize),
    Maybe::Present(integer),
    Maybe::Absent(body::Absent::Hole),
    OriginToken::from(7_usize),
)];

let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
let report = check_module(&mut context, &declarations);

let [entry] = report.ledger().entries()
else {
    unreachable!("one hole is owed");
};
assert_eq!(entry.absence().origin(), OriginToken::from(7_usize));
assert!(matches!(report.judged()[0].verdict(), Verdict::Owed(_)));

// The kernel assumes the owed hole as an axiom, and the artifact rests on it.
let readmission = bridge::readmit(&mut arena, &report);
assert!(matches!(
    readmission.readmitted()[0].outcome(),
    &bridge::Outcome::Assumed { .. }
));
assert_eq!(readmission.audit().axioms().len(), 1_usize);
```

## Where the detail lives

Mechanism, rules, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Modes, static operators, the dependent arrow and the bind, splits, holes in the faces, effects and control, native universe paths, element identity | [`judgement`](src/judgement.rs) |
| Function extensionality, universe equivalence, the product of universe paths, `ua_n` | [`funext`](src/funext.rs), [`equiv`](src/equiv.rs), [`product`](src/product.rs), [`ua`](src/ua.rs) |
| Total elaboration and the typed run | [`judgement::elaboration`](src/judgement/elaboration.rs) |
| Records | [`judgement::native`](src/judgement/native.rs) |
| Temporary access | [`access`](src/access.rs), [`judgement::access`](src/judgement/access.rs) |
| The three bridges, consistency, smallness and variance; the fourth, a nested computation run or suspended | [`conversion`](src/conversion.rs), [`nested`](src/nested.rs) |
| Formation, the classifier, universes, quotes and decodes | [`formation`](src/formation.rs) |
| Code unfolding, `El` as unquote, and their certificates | [`code`](src/code.rs) |
| The fragment's type views | [`view`](src/view.rs) |
| The context, resolution by admission position, adoption | [`context`](src/context.rs) |
| Declaration input | [`declaration`](src/declaration.rs) |
| Verdicts, holes at the declaration grain, definitions, refused-body failures | [`module`](src/module.rs) |
| The machine's failure and its frame roles | [`failure`](src/failure.rs) |
| The ledger | [`ledger`](src/ledger.rs) |
| Refusal classes | [`refusal`](src/refusal.rs) |
| Support | [`support`](src/support.rs) |
| Coverage | [`coverage`](src/coverage.rs) |
| Nominal data | [`former`](src/former.rs) |
| Accessibility, stage typing, derived eliminators, divergence | [`occurrence`](src/occurrence.rs), [`recursion`](src/recursion.rs), [`eliminator`](src/eliminator.rs), [`divergence`](src/divergence.rs) |
| Readmission, erasure, lifts and unfoldings, static operators, holes and marks, the audit, splits, deep handlers and export | [`bridge`](src/bridge.rs) |
| Staged programs and their forks | [`staging`](src/staging.rs), [`stage`](src/stage.rs) |
| Guarded staging families, drafts and their controller | [`template`](src/template.rs), [`template::memo`](src/template/memo.rs), [`template::draft`](src/template/draft.rs) |
| Measurement dependencies and the admission observer | [`examples/staging_templates.rs`](examples/staging_templates.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

## References

- `Cockx-2018-elaborating_dependent_copattern_matching` — exemplar: Cockx and Abel, _ICFP_, 2018 — the solution step.
- `Plotkin-2013-handling_algebraic_effects` — background: Plotkin and Pretnar, "Handling Algebraic Effects", _LMCS_, 2013 — handlers as free-model folds.
- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: separation at a fork, its halves sharing an interface only to read it.
- `vault:01a178aa-a2df-7df1-b34d-3a0211d0b6cb` — exemplar: one transport per solved equation.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: § kernel-verdict-reuse — a resumed readmission signs only its own checks.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
