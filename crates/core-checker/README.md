# gandr-core-checker

The core checking judgement: call-by-push-value core terms and a module of name-free declarations in, one verdict per declaration and the obligations the module owes out, every refusal classified by whose fact it is, and every acceptance re-derived by the kernel.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The former decides the mode](#the-former-decides-the-mode)
- [Types meet at two bridges](#types-meet-at-two-bridges)
- [Structural agreement, behind the bridges](#structural-agreement-behind-the-bridges)
- [Holes are directional, and no type is unknown](#holes-are-directional-and-no-type-is-unknown)
- [Only an absence is owed](#only-an-absence-is-owed)
- [A declaration input owned here](#a-declaration-input-owned-here)
- [Resolution by admission position](#resolution-by-admission-position)
- [Every declaration gets a verdict](#every-declaration-gets-a-verdict)
- [Out of the fragment, by name](#out-of-the-fragment-by-name)
- [Whose fact a refusal is](#whose-fact-a-refusal-is)
- [The checker owns its context](#the-checker-owns-its-context)
- [The support is what the judgement read](#the-support-is-what-the-judgement-read)
- [One machine, one allowance, no memo](#one-machine-one-allowance-no-memo)
- [The kernel re-derives what the judgement accepted](#the-kernel-re-derives-what-the-judgement-accepted)
- [Erasure is a remapping of ids](#erasure-is-a-remapping-of-ids)
- [An uncompleted signature crosses as an axiom](#an-uncompleted-signature-crosses-as-an-axiom)
- [A mark crosses as nothing](#a-mark-crosses-as-nothing)
- [The ledger and the kernel's audit agree](#the-ledger-and-the-kernels-audit-agree)
- [The bridge owns its rollback](#the-bridge-owns-its-rollback)
- [One erasure machine, guarded against cycles](#one-erasure-machine-guarded-against-cycles)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `check_module` judges a slice of `Declaration`s in a `CheckingContext` over a `gandr-core-term` arena. A declaration is an admission position, a declared type or the reason there is none, a body or the reason there is none, and an `OriginToken` echoed back untouched. Each gets a `Verdict`: its body checked against its declared type, its unsigned body's synthesised type, the obligation its hole owes, or the `CheckRefusal` that stopped it. The four faces underneath — `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp` — are public on their own, each returning the number of conversions it made. The `ObligationLedger` collects the owed holes; `CheckRefusal::classify` sorts every refusal into the `FailureClass` that `gandr-core-term` defines for the whole pipeline. `bridge::readmit` then has the kernel re-derive the module: each accepted declaration is erased into `gandr-kernel-term` and offered to `gandr-kernel-core` — a definition for a checked or synthesised body, an axiom for an owed hole — and the `bridge::ArtifactAudit` names the axioms the artifact rests on, empty exactly when the ledger is.

**Why.** A front end that parses and lowers needs a judgement the corpus can assert against: one verdict per declaration, stable under every refusal around it, with what the author still owes kept apart from what the author got wrong. The judgement here is that one, over the fragment the surface lowers today, built so its two structural promises — a mode per former, a comparison only where the mode changes — are enforced by a lint and a module boundary rather than by review. The judgement is not trusted for its acceptances: the kernel, a separate checker over a separate vocabulary, repeats each one.

**How.** Every face runs one explicit machine: a goal, a stack of frames, one step per transition against a `CheckBudget`. A rule dispatches on the term's former; a synthesising term in checking position synthesises and then crosses the value or computation bridge, the only two calls into the private conversion decision. Types reach the check faces only as `FormedValueType` and `FormedCompType`, so every type the judgement reads has already been read through the fragment's views, and a former outside the fragment is refused by name wherever it stands. The kernel bridge erases with a second machine of the same shape, reading types through the same views, and offers each declaration in a staging session of its own.

## References

- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." _Typed Lambda Calculi and Applications (TLCA 1999)_, LNCS 1581, Springer (1999). <https://doi.org/10.1007/3-540-48959-2_17> — the value and computation sorts, the thunk and returner shifts `U` and `F`, and the arrow as a computation type, which fix every rule's premises.
- Jana Dunfield and Neel Krishnaswami. "Bidirectional Typing." _ACM Computing Surveys_ 54(5) (2021). <https://doi.org/10.1145/3450952> — the discipline the rules follow: introductions check, eliminations synthesise, and the subsumption rule is the one place a synthesised type meets an expected one.
- Zanzi Mihejevs and Jules Hedges. "Canonical bidirectional typechecking." arXiv:2512.07511 (2025). <https://arxiv.org/abs/2512.07511> — the checkable/synthesisable split read as a polarity duality whose seams are the shifts, the background for confining type comparison to the change of direction.
- Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich and Matthew A. Hammer. "Hazelnut: A Bidirectionally Typed Structure Editor Calculus." _POPL 2017_. <https://doi.org/10.1145/3009837.3009900> — the unknown-type posture for holes, consistency in place of equality, which this crate declines; see [Holes are directional](#holes-are-directional-and-no-type-is-unknown).
- N. G. de Bruijn. "Lambda calculus notation with nameless dummies." _Indagationes Mathematicae_ 75(5) (1972). <https://doi.org/10.1016/1385-7258(72)90034-0> — the binder indices a variable is resolved by.
- Henk Barendregt and Freek Wiedijk. "The challenge of computer mathematics." _Philosophical Transactions of the Royal Society A_ 363(1835) (2005). <https://doi.org/10.1098/rsta.2005.1650> — the de Bruijn criterion: a result is trusted when a small independent checker re-derives it, the posture of the kernel bridge.

## Provided features

- `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp`, `Synthesised` and `Checked`: the four directed faces. Witnesses: `judgement::tests::every_value_former_is_answered_in_both_modes`, `judgement::tests::every_comp_former_is_answered_in_both_modes`, `judgement::tests::the_faces_agree_on_free_terms`, `judgement::tests::well_typed_terms_synthesise_and_check_their_type`, `judgement::tests::a_bind_synthesises_its_continuations_type`, `judgement::tests::a_bind_checks_against_the_expected_computation`, `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`.
- `ConversionCount`: the declared projection of the conversion boundary, returned by every face. Witnesses: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`, `judgement::tests::the_faces_agree_on_free_terms`.
- `form_value_type`, `form_comp_type`, `FormedValueType` and `FormedCompType`: formation, and the types the check faces take. Witnesses: `formation::tests::the_fragment_atoms_form`, `formation::tests::every_value_type_former_is_answered_by_a_rule`, `formation::tests::every_comp_type_former_is_answered_by_a_rule`, `formation::tests::the_dependent_arrow_is_refused_and_the_arrow_forms`, `formation::tests::an_unadmitted_former_beneath_an_arrow_is_found`.
- `Declaration`, `OriginToken`, `signature::Absent` and `body::Absent`: the name-free declaration input. Witnesses: `module::tests::each_combination_of_halves_gets_its_verdict`.
- `check_declaration`, `check_module`, `Verdict`, `Judged` and `ModuleReport`: declaration checking, one verdict per declaration, an accepted one carrying the body it judged. Witnesses: `module::tests::each_combination_of_halves_gets_its_verdict`, `module::tests::a_refusal_does_not_stop_the_run`, `module::tests::a_declaration_cannot_read_its_own_type`, `module::tests::a_refused_signed_body_still_supplies_its_type`, `module::tests::a_body_that_synthesised_nothing_supplies_no_type`, `module::tests::a_later_declaration_reads_an_earlier_type`, `module::tests::an_admission_out_of_order_is_refused`.
- `check_declaration_supported`, `Supported`, `Support`, `Consulted` and `CheckingContext::adopt`: one declaration's verdict beside the signature answers its judgement consulted, ascending by position and each once, and the seat that admits a declaration with an earlier verdict's type instead of judging it again. Witnesses: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`, `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`, `module::tests::an_adopted_answer_is_read_as_if_judged`.
- `CheckingContext`, `CheckBudget` and `signature_table::Absent`: the context wrapper, its signature table, its allowance, and the shared view of the arena it reads, through which a caller encodes the types a verdict names while the context lives. Witnesses: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`, `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`, `module::tests::a_later_declaration_reads_an_earlier_type`.
- `Absence`, `ObligationEntry`, `ObligationLedger` and `ObligationCount`: the absence-only ledger. Witnesses: `module::tests::every_owed_hole_enters_the_ledger_in_order`, `module::tests::a_refusal_never_enters_the_ledger`; the type-level half — no refusal converts to an entry, no caller forges an absence — is held by the compile-fail blocks in `ObligationEntry`'s documentation, exercised by the doc-test lane rather than named as witnesses.
- `CheckRefusal`, `Mismatch`, `CheckingForm`, `ExpectedShape`, `UnadmittedFormer`, `TermNode`, `TypeNode` and `CoreNode`: every refusal, naming its node. Witnesses: one witness per variant, each asserting the exact refusal and its class — `judgement::tests::a_mismatched_literal_is_refused_with_both_types`, `judgement::tests::a_mismatched_application_is_refused_at_the_computation_bridge`, `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`, `judgement::tests::an_elimination_of_the_wrong_former_is_a_shape_mismatch`, `module::tests::each_combination_of_halves_gets_its_verdict`, `module::tests::a_declaration_cannot_read_its_own_type`, `judgement::tests::every_value_former_is_answered_in_both_modes`, `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`, `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`, `judgement::tests::a_dangling_term_is_refused_as_a_fault`, `module::tests::an_admission_out_of_order_is_refused`, `judgement::tests::a_result_of_the_wrong_kind_is_a_machine_fault`.
- `CheckRefusal::classify`: the classifier. Witnesses: `refusal::tests::every_refusal_carries_its_pinned_class`, `refusal::tests::the_classification_ignores_the_payload`, `refusal::tests::the_absence_class_has_no_inhabitant`.
- `bridge::readmit` and `bridge::Readmission`: readmission of a judged module into a fresh kernel environment, erasing each accepted declaration and offering it through the kernel's one checked entry. Witnesses: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`, `bridge::tests::every_checked_function_definition_is_readmitted`, `bridge::tests::a_lowered_value_definition_admits`, `bridge::tests::a_lowered_computation_definition_admits`, `bridge::tests::a_constant_reference_across_declarations_admits`, `bridge::tests::a_constant_resolves_to_its_readmitted_position`, `bridge::tests::a_refused_declaration_leaves_the_environment_unchanged`; the erasure underneath — `bridge::tests::returning_a_literal_lowers`, `bridge::tests::returner_type_lowers`, `bridge::tests::a_bound_variable_resolves_to_a_de_bruijn_index`, `bridge::tests::a_shared_subterm_is_erased_once`.
- `bridge::Readmitted` and `bridge::Outcome`: each declaration's outcome at its origin — defined, assumed, marked with the judgement's refusal, refused by the bridge, or rejected by the kernel. Witnesses: `bridge::tests::marks_and_holes_are_refused_beside_their_positive_controls`, `bridge::tests::hole_unknown_class_rejects_exactly`, `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`.
- `bridge::ArtifactAudit`: the axioms the artifact rests on, one per owed hole in ledger order, so empty exactly when the ledger is. Witnesses: `bridge::tests::every_fixture_the_checker_accepts_is_readmitted`, `bridge::tests::an_empty_ledger_readmits_an_artifact_resting_on_no_axiom`, `bridge::tests::each_owed_hole_is_an_axiom_of_the_artifact`, `bridge::tests::marks_and_holes_are_refused_beside_their_positive_controls`.
- `bridge::Refusal` and `bridge::Refusal::classify`: why an accepted declaration did not cross, classed into the same `FailureClass`. Witnesses: `bridge::tests::every_refusal_carries_its_pinned_class`, `bridge::tests::a_body_naming_a_withheld_declaration_is_refused`, `bridge::tests::every_former_outside_the_fragment_is_refused_by_name`, `bridge::tests::value_universe_rejects_with_universe_type`, `bridge::tests::an_unbound_sealed_atom_is_refused`, `bridge::tests::the_machine_faults_are_refused_exactly`.

## Expected features

- **One arena per context.** Every id a declaration carries resolves in the `CoreArena` the `CheckingContext` was built over; an id that does not is refused as a dangling node, never read.
- **One arena per report.** `bridge::readmit` takes the arena the report was judged over; an id that does not resolve there is refused as a dangling node.
- **Mint first, then check.** `CheckingContext::new` takes the arena mutably once, to mint the unit, integer and string atoms the leaf rules hand out, and reads it immutably from then on.
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
let readmission = bridge::readmit(&arena, &report);
assert!(matches!(
    readmission.readmitted()[0].outcome(),
    &bridge::Outcome::Assumed { .. }
));
assert_eq!(readmission.audit().axioms().len(), 1_usize);
```

## The former decides the mode

Every former but the bind has one direction. Variables, constants, the unit value and integer and string literals synthesise; a force synthesises the body of its value's thunk type; an application synthesises the codomain of its head's arrow, after checking its argument against the domain. A thunk checks against `U C`, a lambda against `A → C`, a return against `F A`. A bind takes the direction it is met in: its bound computation synthesises a returner `F A`, a binder of `A` opens, and the body is judged in the bind's own direction, so the bind synthesises what its body synthesises and checks against what it is checked against. A synthesising term in checking position synthesises and then crosses a bridge; a checking form in synthesis position is refused, naming the form. The direction is a crate-local type declared as the judgement's direction, and the `mode_dispatch_wildcard` lint from the workspace's policy library refuses any match on it, or on a parameter declared to carry the expected type, that answers a case through a fallback arm. A rule added in one direction and forgotten in the other does not compile.

The alternatives were a mode register with a type-directed default, which is what the earlier implementation had; the same constraint as a review convention; and a workflow gate matching source text, which cannot tell a match on a direction from any other match. The choice reverses when the judgement is restated so that a term's syntactic class is itself a type, at which point the arm the lint looks for cannot be written.

The bind is answered in both directions because its type is its body's: a bind fixed to synthesis would refuse every block that ends in a return, which only checks, and a bind fixed to checking would refuse a block standing where a type is wanted from it, as the head of an application. Its bound computation must synthesise, so a bare return as a statement is refused as a checking form; this reverses when a statement can state its returner, by an annotation or a metavariable, and the bound computation then checks against it.

## Types meet at two bridges

The judgement compares types in exactly two places: a synthesising value in checking position crosses the value bridge, a synthesising computation in checking position crosses the computation bridge. Both bridges live in one module beside the private decision they call, and nothing else in the crate can reach that decision, so the two sites are a visibility fact rather than a count someone asserts. Each crossing adds one to the run's `ConversionCount`, which every face returns: the projection through which a test observes that a check converted where it should and nowhere else. The fixture `def f : U (Integer → F Integer) = thunk { λx. (force g) x }`, with `g` of the same type, crosses each bridge once and reports two.

The alternatives were rebuilding and comparing a synthesised type at every rule, which is how the earlier implementation came to compare types at three dozen sites; and a counting lint, which needs a whole-crate pass and a declared expected number where a visibility rule needs neither. The choice reverses when a former brings a cover merge — a sum elimination whose branches synthesise — at which point the merge joins the module and the projection's expected values change with it.

## Structural agreement, behind the bridges

The fragment's types embed no term, so no type reduces, and two formed types convert exactly when they are the same tree. The decision walks both trees with a worklist, accepts a pair of equal ids without reading the node, and compares each distinct pair once, so shared subtrees cost their distinct pairs rather than their expansion. The recorded design routes conversion to the core normaliser's machine in `gandr-core-nbe`; for this fragment that machine would decide the same trees by a longer road, so the structural decision stands behind the bridges until a type former that embeds a term — the dependent arrow, the type a code denotes — enters the fragment, and the bridges then call the normaliser's conversion instead. Nothing outside the conversion module changes when they do.

## Holes are directional, and no type is unknown

A declaration with a declared type and no body is a hole in checking position: it absorbs the declared type and owes it, and its verdict carries the `ObligationEntry` so a caller judging one declaration needs no ledger. A declaration with neither half is a hole in synthesis position and is refused as a checking form: nothing hands it a type, and the judgement does not invent one. No unknown type exists in any sort, so a mismatch is never absorbed by a hole somewhere else in the term.

This supersedes the earlier posture in which a hole carried an unknown type and checking used consistency rather than equality around it — the posture of Hazelnut's local consistency at the hole, and of a matched-type operation that gives every incomplete program a type. The alternatives were that posture, which is symmetric consistency under another name, and a fresh metavariable per hole. The choice reverses when an inference feature needs a hole's type to drive a solution, or an editor face shows that a typed incomplete program cannot be delivered by a ledger plus per-declaration verdicts; the hole then gets a metavariable, and the metavariable gets provenance.

## Only an absence is owed

An `ObligationEntry` is built from an `Absence` and from nothing else, and an `Absence` has no public constructor: the hole rule makes one when a hole meets a declared type, and only then. A refusal therefore cannot be spelled as an obligation, by the checker or by a caller, and the ledger's count is the number of holes owed. The alternatives were a runtime assertion, a lint, and an audit of construction sites; each is weaker than the type, and none would survive a caller outside the crate. There is no reversal: a weaker enforcement is what the choice replaced.

The producer of an obligation is a signature no definition completes, which is the shape a lowering hands over as an uncompleted declaration. Term-level holes, when the core vocabulary gains one, join this producer rather than replacing it.

## A declaration input owned here

`Declaration` is defined in this crate and carries no name, span or syntax node, so the checker depends on no surface crate. A producer adapts its own declaration shape in a short function downstream of both: a lowering's completed declaration becomes a declared type and a body, its uncompleted one a declared type and a hole, its bodied one a body with no declared type, and its refused one is not offered. The `OriginToken` is the producer's index, echoed back beside the verdict for the driver to resolve. The alternative was reading the lowering's outcome type directly, which would make the judgement depend on the surface; the choice reverses if that outcome type moves below both crates.

## Resolution by admission position

A declaration's type enters the signature table only after its own body was judged, and a declaration is admitted only above every position admitted before it, so a body sees exactly the declarations strictly before it: self-reference and mutual reference find no type, whatever the producer resolved. A declared type is the contract and enters the table whether or not the body met it, so one wrong body does not turn every later reference into an unknown constant; an unsigned body supplies a type only when it synthesised one. The alternative was withholding a signed declaration whose body was refused, which cascades a single mistake into every later reference. The order reverses with the `rec { … }` form and its guarded fixed point, which admits a body that refers to its own declaration.

## Every declaration gets a verdict

A declaration reports its first refusal, and the run continues with the next declaration: `check_module` returns one `Judged` per declaration, in the order given. This re-cuts total marking — every error of a declaration in one pass — down to the first refusal per declaration; total marking is the alternative, and it returns when an editor face needs every error from one pass.

## Out of the fragment, by name

The judgement has rules for the fragment the surface lowers: the integer and string atoms, the unit type, thunks, returners and the non-dependent arrow among types; variables, constants, unit, integer and string literals, thunks, forces, applications, lambdas, returns and binds among terms. Every other former of the core vocabulary — the pair, the injection, the value lift, the numeric literal, the case, the numeric atom, the product, the sum, the universe, the type lift, the element type, the abstract atom and the dependent arrow — is `OutOfFragment` naming the former, wherever it is met. No former falls through to an opaque or unknown reading. The case stays out in particular because the fragment has no sum to eliminate and because its synthesising form adds a merge of its branches' types, a third comparison site. A former leaves this list when its rule enters, with its witnesses.

## Whose fact a refusal is

`CheckRefusal::classify` is a `const`, wildcard-free match that binds no payload. A type mismatch, a shape mismatch, a checking form in synthesis position and an unknown constant are malformed source, the author's mistake. A former outside the fragment is unrepresentable. An unbound index, an exhausted allowance, a dangling id, an admission out of order and a machine invariant are engine faults: a producer that resolves binders and positions never hands the checker an unbound index or an out-of-order admission, so either one is the producer's fault, not the author's; the machine invariant reports a miscount of the machine's own frames instead of asserting it. The absence class has no refusal, because obligations come from a declaration's shape. The alternative for the unbound index — classing it as the author's — would hide a resolution bug in the producer behind a source diagnostic; it reverses if a producer ever hands over unresolved author text.

## The checker owns its context

`CheckingContext` wraps `gandr-core-term`'s flat, de Bruijn binder stack rather than extending it: the signature table, the highest admission position, the atoms and the allowance live here, and the binder stack is empty between judgements and restored to where it stood whenever a run is refused. The alternative was adding the signature table to the core crate; the wrapper moves down when a second consumer needs the same one.

## The support is what the judgement read

An incremental caller reuses a verdict only when it can show the judgement would read the same answers again. The judgement reads one thing outside its declaration — the signature table, in the constant rule — so that rule reads through the context, which logs each answer while `check_declaration_supported` runs. The support is the run's own record, ascending by position and each position once; a refusal stops the log where it stops the run, so a constant behind the refusal is not in it. The alternative was a scan of the declaration's terms for constants, which names constants the run never reached and has to be kept in step with the rules by hand; that scan is the incremental checker's conservative footprint, and it answers a different question. `CheckingContext::adopt` admits a declaration with the type it supplied before: the caller vouches for the reuse, and admission order binds an adopted declaration as it binds a judged one. Logging is off outside the supported entry, so `check_module` pays one branch per constant read. This reverses when the judgement gains a second read of shared state — unfolding a definition once universe families enter — and that read logs through the same seam.

## One machine, one allowance, no memo

Every face runs one machine of goals and frames, charged one step per transition against the context's `CheckBudget`, so a term as deep as memory holds is judged without a native stack and every run is bounded whatever its sharing. A subterm reached twice is judged twice: the fragment's terms come from source text, whose sharing is the author's repetition, and the allowance bounds the rest. The alternative is a check memo keyed by node and context, the seam `gandr-kernel-check-memo` already provides; it becomes worth its bookkeeping when a producer starts sharing aggressively, which an elaborator's output will.

## The kernel re-derives what the judgement accepted

`bridge::readmit` offers every declaration the judgement accepted to `gandr-kernel-core` through `Environment::add_decl`, the kernel's one checked entry, in a fresh environment per module. The kernel re-derives every typing obligation from the erased terms and takes nothing on the bridge's word: the judgement and the bridge both sit outside the trusted base, and the kernel is their oracle. A judgement that agrees only with itself is blind to a fault it shares with its own reference; the kernel is a separate checker over a separate vocabulary, so an acceptance it does not repeat surfaces as `Outcome::Rejected` at the declaration's origin instead of being trusted. The property `every_fixture_the_checker_accepts_is_readmitted` asks the kernel to repeat every acceptance over the checker's own fixture set, and `every_checked_function_definition_is_readmitted` over generated function definitions in the shape a lowered function tail takes: a thunked chain of lambdas over a chain of binds, declared at `U` over the arrows into a returner. The verdict carries the body it judged, so the bridge reads the report alone and never pairs a verdict with a declaration it could disagree with.

The alternatives were a second checker over the core vocabulary, which doubles what must be trusted instead of reducing it to the kernel, and differential testing against the earlier implementation, which shares the earlier design's mistakes. The choice reverses only in scope: when the fragment gains a former whose erasure needs machinery the bridge lacks — universe levels, the binding of a sealed atom — that erasure lands as its own change with its own witnesses, and the oracle stays.

## Erasure is a remapping of ids

The core vocabulary shares the kernel's leaves — literals, base types, de Bruijn indices, admission positions — so erasure mints, for each core node, the kernel node of the same former over its children's images. Two maps are kept: node to image, and module position to the kernel position the declaration took, which part ways as soon as an earlier declaration did not cross. Types are read through the fragment views the judgement reads them through, so the two cannot disagree about which formers exist, and every other former is `OutOfFragment` by name. Each distinct node is erased once per declaration, so the kernel arena receives the sharing the producer built and no more.

The earlier implementation lowered surface terms, erasing annotations and grades the core vocabulary does not have, and resolved a free name through a map its caller supplied. Here the bridge builds the position map from the admissions themselves, the only map that cannot disagree with the environment it indexes. The alternative to remapping was keeping module positions verbatim and admitting a placeholder axiom for each declaration that did not cross, which puts assumptions in the audit that the ledger never owed. The choice reverses when declarations are admitted into an environment shared across modules, where the environment assigns positions and the map becomes its own.

## An uncompleted signature crosses as an axiom

An owed hole is a declared type with no body, which is the kernel's bodiless declaration: the bridge stages it through `Staging::axiom`, and the hole never becomes a term. The kernel then reports the assumption in the audit of the hole and of every declaration that reads it. The earlier implementation refused holes at the bridge as a class, because its holes carried an unknown type the kernel cannot state; a hole here owes a formed type, so the kernel can assume it. A hole in synthesis position has no type to assume, and the judgement has refused it already.

The alternatives were refusing a module until its ledger is empty, which withholds the kernel's verdict on every complete declaration until the last hole is filled, and a placeholder term in the hole, which the kernel would check as if the author had written it. The choice reverses when term-level holes enter the core vocabulary: a hole inside a body then needs an axiom of its own, abstracted over its context, decided with that former.

## A mark crosses as nothing

A refused declaration carries its refusal as its mark, and the bridge offers the kernel nothing for it: not its body, which the kernel may accept where the judgement did not — a pair at a product type is in the kernel's vocabulary and outside the judgement's fragment — and not its signature as an axiom, which would add an assumption the ledger never owed. A refused verdict carries neither half, so there is nothing to offer by mistake. A later declaration reading a marked one is `Refusal::Withheld` at the reference, though the judgement accepted it through the declared contract. `marks_and_holes_are_refused_beside_their_positive_controls` asserts each refusal beside a positive control in the same module, with its origin and node, and has a scratch kernel admit the marked content on its own, so the refusals are the bridge's and not the kernel's.

The alternative was offering a marked declaration's signature as an axiom so its dependents cross, which makes the audit disagree with the ledger. The choice reverses only together with the next one.

## The ledger and the kernel's audit agree

The kernel audits each admitted declaration with the axioms it transitively rests on, an axiom's own position included. `ArtifactAudit` is the union of those audits over the module, so its axioms are exactly the kernel positions the owed holes took, in ledger order, and it is empty exactly when the ledger is: the kernel's witness that the artifact is sealed. Sealedness is reported and gates nothing: a module with owed holes is readmitted all the same, and its audit says what it rests on. The kernel has no artifact-level audit, and the bridge adds none to it; the union is folded from the per-declaration reports the kernel already returns.

The alternatives were gating readmission on an empty ledger, which hides the kernel's verdict on complete declarations behind incomplete ones, and an artifact audit inside the kernel, which widens the trusted surface for a fold any caller can compute. The choice reverses when a publishing or dependency boundary arrives: a module offered to another then needs its audit empty, and that boundary gates on this report.

## The bridge owns its rollback

Each declaration is erased into a staging session the bridge opened, so the bridge is the owner that rolls it back: a refused erasure discards the session, and a rejected admission is truncated by the kernel's choke point. Either way the environment is as the declaration found it, which `a_refused_declaration_leaves_the_environment_unchanged` asserts by the kernel arena's watermark against the same module without the refused declaration. The alternative was leaving partially erased content in the arena as unreachable nodes, which every later reader of the arena would have to step over; there is no reversal while staging has an explicit discard.

## One erasure machine, guarded against cycles

Erasure runs one machine of goals and frames over an explicit stack, as the judgement does. A node is open while its frame waits for its children, so a node that is its own descendant — constructible only by minting ids of another arena — is `Refusal::Cyclic` rather than erased forever. Erasure charges no allowance: each distinct node is erased once and refused if revisited while open, so a run is bounded by the arena it reads. The alternative was charging the judgement's `CheckBudget`, which bounds work the memo bounds already; the choice reverses if erasure ever erases one node under two contexts, as a level instantiation would.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
