# gandr-core-checker

The core checking judgement: call-by-push-value core terms and a module of name-free declarations in, one verdict per declaration and the obligations the module owes out, every refusal classified by whose fact it is, and every acceptance re-derived by the kernel and exported under the producer's names.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `check_module` judges name-free `Declaration`s in a `CheckingContext` over a core arena. Each input carries an admission position, an echoed `OriginToken`, and either optional value signature/body halves or a complete nominal data signature. Its `Verdict` records an admitted data signature, a checked body, a synthesised type, an owed hole or a refusal. Four public faces judge individual values and computations. The ledger collects holes; refusal classification separates malformed source, unrepresentable syntax and engine faults. The kernel independently checks the exportable pure fragment.

**Holes.** A hole inside a body synthesises the unknown type, which conversion treats as consistent with every type; `elaborate_value` and `elaborate_comp` mark each refusal where it stands and go on; `cover` answers coverage in three values; the bridge refuses a hole and erases a mark.

**Why.** A frontend needs stable per-declaration verdicts that distinguish what the author owes from what is wrong. A mode per former and comparison only at mode changes are enforced by lint and module visibility, not review. Kernel readmission independently checks pure acceptances.

**How.** One goal-and-frame machine charges each transition to `CheckBudget`. Checking receives formed types and dispatches on the term former. Synthesis crosses a private conversion bridge when checking needs it. Formation computes the natural classifier. Code unfolding is certified before comparison; readmission replays those certificates. The module documentation specifies each boundary.

## Provided features

- `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp`, `Synthesised` and `Checked`: the four directed faces.
- Pairs, static lambdas and static applications in the faces: a pair synthesises the eager product of its components or checks against one; a static lambda checks only against a static Pi; a static application synthesises its head's last codomain.
- Native list introductions check against `List A`; the pure fold synthesises `F B` from explicit element and result annotations. Nil and cons branches are checked in their zero- and two-binder contexts, and readmission preserves the native kernel syntax without assumptions.
- `ConversionCount`: the declared projection of the conversion boundary, returned by every face.
- `form_value_type`, `form_comp_type`, `FormedValueType` and `FormedCompType`: formation as a judgement, and the types the check faces take.
- `classify_value_type`, `classify_comp_type` and `level_of`: the unique classifier of each formed type.
- `CodeDefinitions`, `Certificate`, `Unfolded`, `unfolding::Absent` and `Lift`: static definitions, certified reductions and recorded universe lifts.
- `Declaration`, `DeclarationContent` and `OriginToken`: name-free value/data input. Values retain optional signature/body halves; data retain a `DataSignature`.
- `check_declaration`, `check_module`, `Verdict`, `Judged` and `ModuleReport`: one verdict per declaration, retaining accepted value definitions, native data signatures and recorded lifts.
- `Funext`, `FunextComponent`, `Evaluation`, `evaluated::Absent` and `ModuleReport::funexts`: function extensionality decided by computation, per covering input each side's returned value and trace.
- `check_declaration_supported`, `Supported`, `Support`, `Consulted` and `CheckingContext::adopt`: query-specific value/data answers and adoption into the new prefix.
- `CheckingContext`, `CheckBudget` and `signature_table::Absent`: context, admission tables and judgment allowance.
- `Absence`, `ObligationEntry`, `ObligationLedger` and `ObligationCount`: the absence-only ledger.
- `CheckRefusal`, `Mismatch`, `CheckingForm`, `ExpectedShape`, `UnadmittedFormer`, `TermNode`, `TypeNode` and `CoreNode`: named refusals and responsible nodes.
- `StaticArity`, `ArgumentPosition` and family refusals preserve the failing argument or arity.
- `CheckRefusal::classify` assigns producer-failure classes; actual judgments, rather than a duplicate variant-to-class table, witness their refusals.
- `CheckRefusal::compared`, `Compared` and `compared::Absent`: the types a refusal sets against each other, the one its rule expected and the one it found, as nodes a face spells.
- `Failure`, `Obligation`, `FrameRole`, `FoldPremise`, `Pursuit`, `Stage`, `judged` and `ModuleReport::failures`: what the checking machine held when it refused, read off the one run that refused — the refusal, the frames it stood inside, outermost first, each a closed rule role with the term and type it judged and the binders it opened, and the goal under way — kept per refused body by position.
- `bridge::readmit` and `bridge::Readmission`: independent admission of accepted declarations into a fresh kernel environment.
- `bridge::Readmitted` and `bridge::Outcome`: each origin and its defined-value, admitted-data, assumed-hole, static-definition, marked, refused or rejected outcome.
- `bridge::ArtifactAudit`: owed-hole and native-runtime assumptions used by admitted declarations.
- `bridge::Replayed` and `bridge::Readmitted::certificates`: kernel replay results for distinct reduction instances.
- `bridge::Readmission::export`: canonical artifacts with crossed declarations and producer names.
- `bridge::Refusal` and its classification retain why an accepted declaration did not cross.
- The hole surface: term holes, marks and the unknown type in the faces; `elaborate_value`, `elaborate_comp`, `Elaboration`, `MarkEntry` and `Direction`; `cover`, `Coverage`, `Exhaustiveness`, `Redundancy` and `CoverageFault`; `bridge::Refusal::Hole` and `bridge::Refusal::Unknown`.
- `fork::Fork` and `fork::Serial`: the shape a program check forks by, and the serial reference.
- `staging::check`, `staging::Program`, `staging::Allowance`, `staging::Checked`, `staging::Readmission`, `staging::Stages`, `staging::ProgramError` and `staging::SourceIndex`: a staged program checked end to end on the caller's fork.
- `stage::compile`, `stage::Program::admit` and `stage::Program::execute`: certified first-order residual readmission for the experimental stage universe.
- `template`: guarded families of staging equations with ordinary replay as authority, the `template::Memo` that drafts a family from its key's last template, and the adapter into the kernel's guarded admission.

## Expected features

- **One arena per context.** Every id a declaration carries resolves in the `CoreArena` the `CheckingContext` was built over; an id that does not is refused as a dangling node, never read.
- **One arena per report.** `bridge::readmit` takes, mutably, the arena the report was judged over: it reads every id there, refusing one that does not resolve as a dangling node, and mints there the reduct of each static step it takes.
- **One writer per arena.** `CheckingContext::new` holds the arena mutably for the context's life: it mints the unit, integer and string atoms the leaf rules hand out, and the judgement mints the types it rewrites — a codomain shifted under a binder, instantiated at an argument, or decoded from a quote — into the same arena. A caller reads the arena through `CheckingContext::arena` while the context lives.
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
| Function extensionality | [`funext`](src/funext.rs) |
| Total elaboration and the traced run | [`judgement::elaboration`](src/judgement/elaboration.rs) |
| Records | [`judgement::native`](src/judgement/native.rs) |
| The three bridges, consistency, smallness and variance | [`conversion`](src/conversion.rs) |
| Formation, the classifier, universes, quotes and decodes | [`formation`](src/formation.rs) |
| Code unfolding and its certificates | [`code`](src/code.rs) |
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
| Strict positivity, structural descent, derived eliminators | [`occurrence`](src/occurrence.rs), [`descent`](src/descent.rs), [`eliminator`](src/eliminator.rs) |
| Readmission, erasure, lifts and unfoldings, static operators, holes and marks, the audit, splits and export | [`bridge`](src/bridge.rs) |
| Staged programs and their forks | [`staging`](src/staging.rs), [`fork`](src/fork.rs), [`stage`](src/stage.rs) |
| Guarded staging families, drafts and their controller | [`template`](src/template.rs), [`template::memo`](src/template/memo.rs), [`template::draft`](src/template/draft.rs) |
| Measurement dependencies and the admission observer | [`examples/staging_templates.rs`](examples/staging_templates.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

The behavioural floor — each conformance row this crate holds, its witness, and the rows still deferred — is tracked in [#199](https://github.com/gandr-lang/gandr/issues/199).

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
