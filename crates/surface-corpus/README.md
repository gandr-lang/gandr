# gandr-surface-corpus

The expectation language over a lowered module and its verdicts — the `checks`, `owes`, `refuses`, `runs` and `normalizes` schemas, the strict and fixture corpus roots, the settle comparison, and the report a corpus runner reads its counts from — and the language's corpus itself, under `strict/` and `fixture/`.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `settle` takes a `CorpusRoot`, the `CoreArena` a module was lowered into, the `LoweredModule` from `gandr-surface-lowering`, and the `ModuleReport` `gandr-core-checker` returned for it, and answers a `SettleReport`: one `DeclarationReport` per declared name, stating what the name's attributes assert (`Stated`), what the name produced (`Produced`: the checker's verdict, the lowering's refusal, or the root's own refusal), and the obligations its verdict owes; plus the module's ledger size. `SettleReport::tally` sums a run into a `Tally` — declarations and fixtures by `Settlement`, the ledger size, the surviving obligations, the refusals by failure class, the run's settlement and its `Seal` — which a driver absorbs across sources, gates on, and prints.

**Why.** A corpus that only says pass or fail cannot tell a run that owes nothing from one that signed for a hole, and a corpus whose sources describe their own expected failures can describe a regression as expected. The expectation language here makes both visible: the strict root admits only `checks` and its `runs` and `normalizes` refinements, every declaration states a verdict whether it writes one or not, and every report carries the ledger size.

**How.** Attributes are read off the lowering's side table under each declared name's form keys; the five schemas are matched by their registered names, and their payloads are read as literals out of the arena. The declarations are walked in admission order in lockstep with the checker's verdicts, a lowering-refused declaration consuming none. A declaration stating a run outcome that the checker accepted is run through the `Runner` the caller hands in; a data block stating a normal form has its call read under its rules by `LoweredModule::normal_form`. One equality decides each declaration; the tally counts it once.

## Provided features

- `CorpusRoot` and `CorpusRoot::admit`: the two roots and the strict root's refusal of `owes` and `refuses`.
- `ExpectationSchema` and `expectation_schema::Absent`: the five schemas, matched by the registry's names.
- `Runner`, `RunSpelling` and `ran::Absent`: the run a `runs` outcome is compared against, asked of the caller, and the line a `normalizes` outcome is compared against.
- `normalized_call`, `normalized_call::Absent` and `NORMAL_FORM_ARROW`: the call a `normalizes` line reads, why a line reads none, and what separates a call from its normal form.
- `Stated`, `Outcome`, `ExpectationFault` and `Membership`: what a declaration states, and why an expectation states nothing.
- `RefusalName`, `RefusalSpelling`, `refusal_name::Absent`, `Refusal` and `CorpusRefusal`: the closed refusal vocabulary and producer refusal views.
- `settle`, `SettleFault`, `Produced`, `produced_refusal::Absent`, `DeclarationReport`, `Settlement` and `Surviving`: the settle comparison.
- `SettleReport`, `Tally`, `SettleCounts`, `ClassCounts` and `Seal`: the report and its counts.

## Expected features

- **One arena.** The caller supplies the arena the lowering minted the module into. Payload lookup rejects absent or unsuitable literals, but arena-local identifiers do not establish provenance: an unrelated arena can reuse an identifier.
- **The module's own verdicts.** The caller supplies the checker's report for exactly the declarations the lowering did not refuse, in admission order. Missing, shifted and surplus verdicts are refused by position; matching positions alone do not establish that a report came from this module.
- **`alloc`.** The crate is `no_std` with `alloc`, and does no I/O, no file walking and no process exit.

## Examples

```rust
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::RunSpelling;
use gandr_surface_corpus::Seal;
use gandr_surface_corpus::Settlement;
use gandr_surface_corpus::settle;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

let source = SourceText::from(
    r#"@[ owes(1) ] def owed : Integer ;
@[ refuses("UnresolvedName") ] def broken = missing ;"#,
);
let pbg = built_in()?;
let tree = parse(&pbg, source)?.into_tree();
let mut arena = CoreArena::new();
let module = lower_module(&pbg, &tree, &mut arena, LoweringBudget::DEFAULT, Recognition::default())?;

// The driver's adaptation: every declaration the lowering did not refuse.
let declarations: Vec<Declaration> = module
    .declarations()
    .iter()
    .filter_map(|lowered| {
        let (declared, defined) = match lowered.outcome() {
            DeclarationOutcome::Completed { declared_type, body } => {
                (Maybe::Present(declared_type), Maybe::Present(body))
            },
            DeclarationOutcome::Uncompleted { declared_type } => {
                (Maybe::Present(declared_type), Maybe::Absent(body::Absent::Hole))
            },
            DeclarationOutcome::Bodied { body } => {
                (Maybe::Absent(signature::Absent::Unsigned), Maybe::Present(body))
            },
            DeclarationOutcome::Refused(_) => return None,
        };
        let origin = OriginToken::from(usize::from(lowered.origin()));
        Some(Declaration::new(lowered.constant(), declared, defined, origin))
    })
    .collect();
let verdicts = check_module(
    &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
    &declarations,
);

// No declaration states a run outcome, so the runner is never asked.
let mut runner = |_constant: ConstantIndex| RunSpelling::from(String::new());
let report = settle(CorpusRoot::Fixture, &arena, &module, &verdicts, &mut runner)?;
let tally = report.tally();
assert_eq!(tally.settlement(), Settlement::Settled);
assert_eq!(usize::from(tally.ledger()), 1_usize);
assert_eq!(tally.seal(), Seal::Unsealed);
```

The same example is the crate-level doctest. `cargo nextest run -p gandr-surface-corpus` runs the crate's tests. Source-level settlement witnesses parse, lower and check their modules; counter and formatter boundary witnesses also construct values directly to reach saturation and sink failures.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Specification and adequacy, inputs not a pipeline, references | [`src/lib.rs`](src/lib.rs) |
| One predicate: settled; lockstep with the checker | [`settle`](src/settle.rs) |
| Run outcomes, the strict root, one expectation per name | [`expectation`](src/expectation.rs) |
| Sealed and the ledger size | [`report`](src/report.rs) |
| The closed refusal vocabulary, native universe-path refusals | [`refusal`](src/refusal.rs) |
| Membership, the corpus directories, one walk, the pending set | [`root`](src/root.rs) |
| The kernel export suite | [`kernel_export`](src/kernel_export.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
