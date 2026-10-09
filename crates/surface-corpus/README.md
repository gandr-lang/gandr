# gandr-surface-corpus

The expectation language over a lowered module and its verdicts — the `checks`, `owes`, `refuses` and `runs` schemas, the strict and fixture corpus roots, the settle comparison, and the report a corpus runner reads its counts from — and the language's corpus itself, under `strict/` and `fixture/`.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [One predicate: settled](#one-predicate-settled)
- [A run outcome refines checks](#a-run-outcome-refines-checks)
- [Membership is location](#membership-is-location)
- [The strict root refuses self-description](#the-strict-root-refuses-self-description)
- [Sealed is reported, never gated](#sealed-is-reported-never-gated)
- [The ledger size is always printed](#the-ledger-size-is-always-printed)
- [A closed vocabulary, named by variant](#a-closed-vocabulary-named-by-variant)
- [One expectation per name](#one-expectation-per-name)
- [Lockstep with the checker](#lockstep-with-the-checker)
- [Inputs, not a pipeline](#inputs-not-a-pipeline)
- [The corpus](#the-corpus)
- [One walk registers every source](#one-walk-registers-every-source)
- [The pending set](#the-pending-set)
- [The kernel export suite](#the-kernel-export-suite)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `settle` takes a `CorpusRoot`, the `CoreArena` a module was lowered into, the `LoweredModule` from `gandr-surface-lowering`, and the `ModuleReport` `gandr-core-checker` returned for it, and answers a `SettleReport`: one `DeclarationReport` per declared name, stating what the name's attributes assert (`Stated`), what the name produced (`Produced`: the checker's verdict, the lowering's refusal, or the root's own refusal), and the obligations its verdict owes; plus the module's ledger size. `SettleReport::tally` sums a run into a `Tally` — declarations and fixtures by `Settlement`, the ledger size, the surviving obligations, the refusals by failure class, the run's settlement and its `Seal` — which a driver absorbs across sources, gates on, and prints.

**Why.** A corpus that only says pass or fail cannot tell a run that owes nothing from one that signed for a hole, and a corpus whose sources describe their own expected failures can describe a regression as expected. The expectation language here makes both visible: the strict root admits no self-description but `checks`, every declaration states a verdict whether it writes one or not, and every report carries the ledger size.

**How.** Attributes are read off the lowering's side table under each declared name's digests; the four schemas are matched by their registered names, and their payloads are read as literals out of the arena. The declarations are walked in admission order in lockstep with the checker's verdicts, a lowering-refused declaration consuming none. A declaration stating a run outcome that the checker accepted is run through the `Runner` the caller hands in. One equality decides each declaration; the tally counts it once.

## References

- The Agda test suite, `test/Succeed` and `test/Fail` in <https://github.com/agda/agda> — a test's expected outcome decided by the directory it sits in, the arrangement the two corpus roots follow.
- The Rust compiler development guide, "UI tests". <https://rustc-dev-guide.rust-lang.org/tests/ui.html> — expected diagnostics written in the source they are about, with an unexpected diagnostic and a missing expected one both failing the test; the two directions in which a stated verdict here fails.

## Provided features

- `CorpusRoot` and `CorpusRoot::admit`: the two roots and the strict root's refusal of `owes` and `refuses`. Witnesses: `root::tests::the_admission_table_is_pinned`, `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`.
- `ExpectationSchema` and `expectation_schema::Absent`: the four schemas, matched by the registry's names. Witnesses: `expectation::tests::every_registered_attribute_is_an_expectation_schema`.
- `Runner`, `RunSpelling` and `ran::Absent`: the run a `runs` outcome is compared against, asked of the caller. Witnesses: `settle::tests::a_run_outcome_settles_under_either_root`.
- `Stated`, `Outcome`, `ExpectationFault` and `Membership`: what a declaration states, and why an expectation states nothing. Witnesses: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`, `expectation::tests::a_payload_the_arena_does_not_hold_is_unreadable`, `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`, `settle::tests::a_name_carrying_two_expectations_states_none`.
- `RefusalName`, `RefusalSpelling`, `refusal_name::Absent`, `Refusal` and `CorpusRefusal`: the closed refusal vocabulary, one view over every producer's refusals, and this crate's own refusal. Witnesses: `refusal::tests::every_refusal_is_named_by_its_variant`, `refusal::tests::a_near_miss_names_no_refusal`, `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`.
- `settle`, `SettleFault`, `Produced`, `produced_refusal::Absent`, `DeclarationReport`, `Settlement` and `Surviving`: the settle comparison. Witnesses: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`, `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`, `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`, and the witnesses above.
- `SettleReport`, `Tally`, `SettleCounts`, `ClassCounts` and `Seal`: the report and its counts. Witnesses: `report::tests::the_run_is_settled_only_when_every_declaration_is`, `report::tests::sealed_is_reported_never_gated`, `report::tests::the_ledger_size_is_printed_settled_or_not`, `report::tests::every_fixture_and_every_unsettled_declaration_has_a_line`, `report::tests::the_tally_counts_every_declaration_once`, `report::tests::absorbing_a_tally_sums_every_count`.

## Expected features

- **One arena.** `settle` reads payloads out of the arena the lowering minted the module into; any other arena is refused as an unreadable payload, never read.
- **The module's own verdicts.** The report passed is the checker's report for exactly the declarations the lowering did not refuse, in admission order; any other is refused by admission position.
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

The same example is the crate-level doctest. `cargo nextest run -p gandr-surface-corpus` runs the crate's tests; every module a witness settles is parsed from source, lowered and checked in the same test, so the suite settles exactly what a driver hands this crate.

## One predicate: settled

A declaration is settled when the verdict it produced equals the verdict it states. A verdict is one of three shapes: _checks, owing n_ — checked, synthesised, or owed, with n the obligations its verdict left in the ledger — _runs to_ a spelled value, or _refuses_ a named refusal. `checks` states _checks, owing 0_; `owes(n)` states _checks, owing n_; `runs("spelling")` states _runs to_ the spelling; `refuses("Name")` states the named refusal; a declaration carrying none of the four states _checks, owing 0_. A run is settled when every declaration in it is, which is the predicate a corpus run is gated on.

An obligation survives when it is unsettled, in either direction: produced with nothing declaring it (an unannotated hole), or declared with nothing producing it (an `owes` on a declaration that completes). Each declaration reports both counts and the tally sums them. A wrong stated verdict therefore fails both ways: a refusal stated and not produced, a refusal produced and not stated, another refusal produced than the one stated, more obligations than stated and fewer.

The alternative was a pass/fail bit per fixture with the obligation count as an informative extra; it lets an `owes(2)` over a single hole pass. The choice reverses if an expectation needs a looser relation than equality — an obligation count bounded rather than exact — which would arrive as a fifth schema rather than a change to this one.

## A run outcome refines checks

`runs("spelling")` states that the declaration checks, owing nothing, and that running it comes to `spelling`: the one spelling `gandr run` prints, compared byte for byte. A declaration the checker accepted is run through the `Runner` the caller passes to `settle`, and its outcome is _runs to_ what the runner spelled; one the checker did not accept keeps its produced verdict — a refusal, or an obligation — so a `runs` stated over it is unsettled against that verdict. Nothing is run for a declaration that states no run outcome. The runner is a trait so this crate stays free of the machine: the dispatcher's program implements it, and the suite here spells runs by position.

The alternative was the prior implementation's outcome snapshots: one sidecar file per source, recording each item's outcome under a digest of the source's bytes, rewritten by a generator behind an environment switch. The expectation here rides the declaration it is about, as `refuses` does: there is no digest to refresh and no generator to run, an outcome changed by a change to the language shows in the diff of the source it changes, and one name carries one expectation. The choice reverses if an outcome outgrows one spelled line — a structured value compared up to sharing, say — when a file of outcomes beside the source would return with its own comparison.

## Membership is location

A source is a fixture or a gate by the root it sits under, never by what it says about itself. `CorpusRoot::Strict` is the gating root: every declaration is held to _checks, owing 0_, or to the stricter _runs to_ a spelling it states. `CorpusRoot::Fixture` is the root where the checker's refusals and obligations are asserted, and all four schemas are admitted there. Inside a root, a declaration carrying an expectation attribute is a fixture (`Membership::Fixture`) and gets its own line in the report; one carrying none is counted.

The alternative was an attribute or a file header marking a source as a fixture, which hands the classification to the source being classified. The choice reverses only together with the guard below: if self-description were made safe some other way, membership could move into the source.

## The strict root refuses self-description

Under the strict root an `owes` or `refuses` attribute is itself a refusal: `CorpusRefusal::ExpectationOutsideFixtureRoot`, classed `MalformedSource`, naming the schema and the bytes it covers. The first such attribute in reading order — the signature's attributes, then the definition's — stands in place of whatever the declaration produced, and the declaration still states _checks, owing 0_, so it is unsettled. Naming the guard's own refusal in a `refuses` payload therefore settles nothing under the strict root: the stated verdict there is never read from an attribute. The verdict's obligations are kept, so the ledger size is unchanged by the guard.

The refusal is owned here because this crate sits below the driver and the dispatcher and is the first that knows what a root is. The alternatives were reading strict-root expectations like fixture ones, which lets a regression migrate into the gate by describing itself as expected, and ignoring them, which leaves a misleading annotation in a gating source. The choice reverses if the strict root grows an expectation that asserts something stricter than _checks, owing 0_; that schema is admitted beside `checks`, as `runs` is.

## Sealed is reported, never gated

A run is `Seal::Sealed` when it is settled and its ledger is empty. `Tally::seal` reports it and nothing here makes it a condition: a settled run that owes is a successful run whose obligations are signed for. The alternative — failing a run that owes — makes every owed hole a failure, which is the strict root's job for unannotated holes and would forbid the annotated ones the fixture root exists to assert. The choice reverses for a release gate that requires an empty ledger, which would gate on the reported seal rather than change it.

## The ledger size is always printed

The rendered `Tally` opens with `ledger size: N`, whether the run is settled or not, then the declaration and fixture counts, the surviving obligations, the refusals by failure class, the run's settlement and its seal. The rendered `SettleReport` precedes it with one line for every fixture, settled or not, and for every unsettled declaration, fixture or not: the settlement, the name and its span, what it states, what it produced with the refusal's class, and the obligations that survive when any do. A settled declaration with no expectation — the strict root's ordinary case — is only counted.

The alternative was a report of failures alone, a list of mismatches per fixture; it renders a run owing three holes exactly as one owing none, so an assumption could ship unreviewed. The counts the driver reads are the `Tally` accessors, never the rendered text. The choice reverses if a consumer needs the report in a machine format, which would be a second rendering of the same `Tally`, not a change to what it counts.

## A closed vocabulary, named by variant

A `refuses` payload names a refusal by its variant: `RefusalName` holds one name per refusal the lowering, the checker and this crate raise, spelled as the variant is, and a payload is matched byte for byte — no case folding, trimming or prefix match — so a near miss names nothing and the fixture fails with `ExpectationFault::UnknownRefusal` rather than settling on a guess. The maps from each producer's refusal type to its name are exhaustive matches without a fallback arm, so a refusal added upstream fails to compile here until it is named. The lowering's `OutOfFragment` and the checker's `OutOfFragment` are one name, as are the two `BudgetExceeded`: an expectation states which refusal a declaration carries, not which pass noticed it, and the produced class distinguishes nothing the name would need to.

The alternatives were free text matched against a refusal's rendering, which breaks whenever a message is reworded, and a name per producer and variant, which makes a fixture restate the pipeline's pass order. The choice reverses if two producers' same-named refusals come to mean different things, at which point the names split.

## One expectation per name

A declared name carries at most one expectation. Two on one name — `checks` beside `owes`, or one on the signature and another on the definition — state no verdict: `ExpectationFault::ConflictingExpectations` names the first two, and the name is unsettled even when one of them would hold. A form that writes both halves, a signed function tail, is one form with one set of attributes, read once. A payload outside its schema's range — a negative `owes`, or one past every ledger size — likewise states nothing, with the bytes it covers. The lowering already refuses one attribute written twice; this crate refuses two different expectations. The alternative was a precedence among schemas, which makes a contradiction pass silently on whichever side wins. The choice reverses if a schema is added that refines another rather than contradicting it.

## Lockstep with the checker

The checker judges the declarations a driver hands it — every declaration the lowering did not refuse, in admission order — and returns one verdict for each, in the same order. `settle` walks the module's declarations in that order, pairs each unrefused declaration with the next verdict, and checks the pairing by admission position: a verdict missing, a verdict for another position, or a verdict left over is `SettleFault`, a caller fault rather than a verdict, as is a payload the arena given does not hold. A declaration's own obligations are read off its verdict — one for an owed verdict, none otherwise — because the checker records exactly one ledger entry per owed verdict; the run's ledger size is read off the ledger.

The alternative was pairing by origin token, which the driver issues and could issue in any scheme; the admission position is the one index both the lowering and the checker define. The choice reverses if the checker ever returns verdicts out of admission order, at which point the pairing becomes a lookup by position.

## Inputs, not a pipeline

This crate reads a lowered module and its verdicts and depends on neither the parser nor the dispatcher; adapting the lowering's declarations to the checker's input and walking the roots belong to the dispatcher, and the exit codes to the driver. The suite depends on the parser and the grammar, and for its kernel export suite on the two storage crates, as development dependencies only: a `LoweredModule` and a `ModuleReport` have no public constructor that would let a test build one by hand, so each witness parses, lowers and checks a source the way the dispatcher does, and adapts the declarations in the fixture exactly as the example above. The alternative was taking the source text and running the pipeline here, which would make this crate the driver. The choice reverses if the lowering and the checker gain a shared declaration type, at which point the adaptation, and with it the fixture's copy, goes away.

## The corpus

The language's sources live beside the library that settles them, under the two roots `settle` names. `gandr check crates/surface-corpus/strict` and `gandr test crates/surface-corpus/fixture` run them, and `mise run check:corpus` runs both as a gate; a red root fails it.

| Directory | Holds | Expectations |
| --------- | ----- | ------------ |
| `strict/` | sources in the fragment: signatures and definitions, literals and the unit value, thunks, lambdas, returns, forces and applications; under `classifier/`, both universes, quotes, a code constant unfolding and a polymorphic function at several instances; under `pathological/`, the dependent instantiations whose codomains could capture | none, or `runs` on each declaration the fragment runs: every declaration checks, owing nothing |
| `fixture/fragment/` | one source per refusal the fragment's checker and lowering can raise at a declaration, one owed signature, and a run blamed on the goal it reaches | `refuses`, `owes` or `runs` on each declaration |
| `fixture/classifier/` | the universe families' refusals: a level too large, a sort mismatch, a graded bridge, and a bind whose body's type needs its binder | `refuses` on each refused declaration, `runs` on each run |
| `fixture/model/`, `fixture/pathological/`, `fixture/surface/` | the language's earlier sources whose declarations the lowering reads, each verdict stated | `refuses`, `checks` or `runs` on each declaration |
| `fixture/pending/` | the language's earlier sources the fragment does not yet cover | none: membership by location ([below](#the-pending-set)) |

The earlier sources are the language's own surface programs: the model programs, the pathological cases and the surface families, kept in their own subdirectories with their commentary removed. The parser reads every source here as its zero-obligation gate, and the highlighter's role golden in `gandr-surface-grammar` mirrors every source: a source added, moved between roots or removed is followed by `UPDATE_EXPECT=1 cargo nextest run -p gandr-surface-grammar`, which rewrites the golden to match.

No count is pinned. The runner's report says how many sources each root holds, how many declarations settled, the ledger size and the seal, and its tests assert that each root holds declarations and that every row of the fragment's exercised table is carried. Adding a source changes a count and reddens no root; a source that stops settling reddens its root.

A bind written in a block is always checked, because a block stands only in a thunk, a lambda or a function's tail, and each of those is checked against its declared type. The expected type is read outside the binder, so a body whose type needs the binder fails to convert with it and the fixture states `TypeMismatch`; the checker's `DependentBind` names the same mistake only where a bind synthesises its type, which no surface form reaches yet. The alternative was spelling the fixture around a synthesising bind, which the surface has no form for. The fixture's expectation changes to `DependentBind` when an ascription or a synthesising block lets a bind's type come from its body.

A `runs` outcome is written on every declaration the fragment runs to a value or to blame: the literals, copies, functions and applications of `strict/`, the classifier's values and polymorphic functions, the pathological compositions, the model's unit, every module member whose body checks, and the blamed run. A declaration the machine carries no image of — a code, or a value that reaches one — states no run, because nothing runs it; the run verb reports it as never reaching the machine.

`pathological/module-forward-member-reference` names a later member inside `second + 1`. The fragment does not read the infix operator, and a form is refused before any name under it is read, so the fixture states `OutOfFragment`; the forward-member refusal itself is witnessed by `gandr-surface-lowering`'s module tests. The expectation becomes `ForwardMemberReference` when the fragment reads infix operators.

## One walk registers every source

A source is registered by where it sits: the dispatcher's one walk over `strict/` and `fixture/` reaches it, and nothing else decides what the corpus holds. The kernel export suite here lists the two roots by the walk's own rule — `.gandr` files, links not followed — because this crate does not depend on the dispatcher; it reads what the walk reaches and registers nothing of its own. An orphan is a `.gandr` file the walk does not reach — one outside both roots, or behind a symbolic link, which the walk does not follow — and the registration witness finds every such file by listing the crate's directories, links followed, and fails naming each one: `corpus::corpus::every_corpus_source_is_registered` in `gandr-surface-dispatcher`, its positive control `corpus::corpus::a_planted_orphan_is_not_registered`, which plants an orphan outside the roots and one behind a link and expects exactly those two. No count is pinned, so a source added where the walk reaches it moves a count and reddens nothing, and one added where it does not reddens the witness, which names the file.

The prior implementation had two registration mechanisms failing in opposite directions: a test file not named in the test target's module list was never compiled, silently, and a source added to the corpus moved a pinned count in a test the author had not opened. Neither is here: this crate's suite is its modules' own `cfg(test)` modules, compiled with the library, and the corpus has the one walk and no pinned count.

## The pending set

A source under `fixture/pending/` carries a refusal no expectation can state: the lowering refuses it as a whole — its root is not a list of declarations — or refuses one of its declarations at the declaration's own form, which files no half for an attribute to be read off. The runner counts such a source as pending and settles none of its declarations; `test` prints each such refusal, naming the form the fragment lacks — a call or an operator, a record, a data declaration, a module, an effect — which is the former the source waits for, and its run outcomes are written when it moves. A pending source that carries none — the fragment grew, and every expectation it needs can now be stated — is unsettled, and moves to the fixture root with its expectations written.

Three module sources stay pending for the second reason. `pathological/module-malformed-recovery` writes a member whose definition leaves its operand unwritten, refused at the member's own form; `pathological/modules/module-missing-component` and `pathological/modules/module-abstract-type-component` write a signature component the body does not supply and one only opaque ascription gives a meaning, each refused at the component, which declares nothing. A refusal at the declaration form itself has no half to carry an expectation.

The alternatives were leaving these sources out, which loses them, and stating each one's refusal in an attribute, which the lowering cannot read for either kind of refusal. The choice reverses when the lowering files an attribute for a declaration refused at its form and a refusal of the whole module can carry an expectation; the pending set then empties into the fixture root.

## The kernel export suite

`kernel_export` takes every source of both roots the lowering reads through the composition a driver runs — parse, lower, check, readmit through the checker's bridge, export — and holds each export to the storage tier's contract. `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`: two independent sweeps export the same bytes and mint the same artifact identity for every source; each export decodes and re-encodes byte for byte; its records, committed through `gandr-storage-artifact`, read back through the record plane and the kernel's decoder as the export; and each root exports a declaration. `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest` classifies every declaration once by what became of it at the kernel boundary — defined, assumed, marked by the checker's refusal, withheld for naming a declaration that did not cross, or never offered because the lowering refused it — fails on any verdict the readmission disagrees with, checks that a withheld declaration names one that did not cross, and holds the artifact's manifest to the partition: a record per crossed declaration beside the header, and the declarations read back exactly the crossed ones, in admission order, under their names. `kernel_export::kernel_corpus_partition::corpus_exercises_multiple_exclusion_classes` asks that at least four kinds of declaration stay out of the kernel.

The three are the prior implementation's, which ran in the sequent crate's suite and made it declare development dependencies across the kernel, storage and surface tiers; here they sit with the corpus they sweep, and the sequent crate takes no such edge. The prior gate pinned each item's size, table entries, expanded work and identity in a checked-in record, the partition pinned its classification in a checked-in manifest, a generator behind an environment switch rewrote both, a framed digest bound them to the corpus bytes, and the gate pinned the corpus's cardinality. No count is pinned here, as [above](#the-corpus): the gate asserts what is a function of the source — the bytes and the identity, reproduced by an independent sweep — and the decoder enforces the work budgets on every read. The prior gate also drove six kernel-native goldens built by hand, a universe and its lifts; `strict/classifier/` reaches both through the surface, and `gandr-kernel-term`'s suite holds the format's goldens, so they are not carried. The alternative was porting the records and their generator, which re-pins every count the corpus decided not to pin. The choice reverses if a quantity the gate should watch can change while the source does not, which a record beside the source would then catch.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
