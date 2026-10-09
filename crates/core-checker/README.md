# gandr-core-checker

The core checking judgement: call-by-push-value core terms and a module of name-free declarations in, one verdict per declaration and the obligations the module owes out, every refusal classified by whose fact it is.

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
- [One machine, one allowance, no memo](#one-machine-one-allowance-no-memo)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `check_module` judges a slice of `Declaration`s in a `CheckingContext` over a `gandr-core-term` arena. A declaration is an admission position, a declared type or the reason there is none, a body or the reason there is none, and an `OriginToken` echoed back untouched. Each gets a `Verdict`: its body checked against its declared type, its unsigned body's synthesised type, the obligation its hole owes, or the `CheckRefusal` that stopped it. The four faces underneath — `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp` — are public on their own, each returning the number of conversions it made. The `ObligationLedger` collects the owed holes; `CheckRefusal::classify` sorts every refusal into the `FailureClass` that `gandr-core-term` defines for the whole pipeline.

**Why.** A front end that parses and lowers needs a judgement the corpus can assert against: one verdict per declaration, stable under every refusal around it, with what the author still owes kept apart from what the author got wrong. The judgement here is that one, over the fragment the surface lowers today, built so its two structural promises — a mode per former, a comparison only where the mode changes — are enforced by a lint and a module boundary rather than by review.

**How.** Every face runs one explicit machine: a goal, a stack of frames, one step per transition against a `CheckBudget`. A rule dispatches on the term's former; a synthesising term in checking position synthesises and then crosses the value or computation bridge, the only two calls into the private conversion decision. Types reach the check faces only as `FormedValueType` and `FormedCompType`, so every type the judgement reads has already been read through the fragment's views, and a former outside the fragment is refused by name wherever it stands.

## References

- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." _Typed Lambda Calculi and Applications (TLCA 1999)_, LNCS 1581, Springer (1999). <https://doi.org/10.1007/3-540-48959-2_17> — the value and computation sorts, the thunk and returner shifts `U` and `F`, and the arrow as a computation type, which fix every rule's premises.
- Jana Dunfield and Neel Krishnaswami. "Bidirectional Typing." _ACM Computing Surveys_ 54(5) (2021). <https://doi.org/10.1145/3450952> — the discipline the rules follow: introductions check, eliminations synthesise, and the subsumption rule is the one place a synthesised type meets an expected one.
- Zanzi Mihejevs and Jules Hedges. "Canonical bidirectional typechecking." arXiv:2512.07511 (2025). <https://arxiv.org/abs/2512.07511> — the checkable/synthesisable split read as a polarity duality whose seams are the shifts, the background for confining type comparison to the change of direction.
- Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich and Matthew A. Hammer. "Hazelnut: A Bidirectionally Typed Structure Editor Calculus." _POPL 2017_. <https://doi.org/10.1145/3009837.3009900> — the unknown-type posture for holes, consistency in place of equality, which this crate declines; see [Holes are directional](#holes-are-directional-and-no-type-is-unknown).
- N. G. de Bruijn. "Lambda calculus notation with nameless dummies." _Indagationes Mathematicae_ 75(5) (1972). <https://doi.org/10.1016/1385-7258(72)90034-0> — the binder indices a variable is resolved by.

## Provided features

- `synthesise_value`, `check_value`, `synthesise_comp`, `check_comp`, `Synthesised` and `Checked`: the four directed faces. Witnesses: `judgement::tests::every_value_former_is_answered_in_both_modes`, `judgement::tests::every_comp_former_is_answered_in_both_modes`, `judgement::tests::the_faces_agree_on_free_terms`, `judgement::tests::well_typed_terms_synthesise_and_check_their_type`.
- `ConversionCount`: the declared projection of the conversion boundary, returned by every face. Witnesses: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`, `judgement::tests::the_faces_agree_on_free_terms`.
- `form_value_type`, `form_comp_type`, `FormedValueType` and `FormedCompType`: formation, and the types the check faces take. Witnesses: `formation::tests::the_fragment_atoms_form`, `formation::tests::every_value_type_former_is_answered_by_a_rule`, `formation::tests::every_comp_type_former_is_answered_by_a_rule`, `formation::tests::the_dependent_arrow_is_refused_and_the_arrow_forms`, `formation::tests::an_unadmitted_former_beneath_an_arrow_is_found`.
- `Declaration`, `OriginToken`, `signature::Absent` and `body::Absent`: the name-free declaration input. Witnesses: `module::tests::each_combination_of_halves_gets_its_verdict`.
- `check_declaration`, `check_module`, `Verdict`, `Judged` and `ModuleReport`: declaration checking, one verdict per declaration. Witnesses: `module::tests::each_combination_of_halves_gets_its_verdict`, `module::tests::a_refusal_does_not_stop_the_run`, `module::tests::a_declaration_cannot_read_its_own_type`, `module::tests::a_refused_signed_body_still_supplies_its_type`, `module::tests::a_body_that_synthesised_nothing_supplies_no_type`, `module::tests::a_later_declaration_reads_an_earlier_type`, `module::tests::an_admission_out_of_order_is_refused`.
- `CheckingContext`, `CheckBudget` and `signature_table::Absent`: the context wrapper, its signature table and its allowance. Witnesses: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`, `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`, `module::tests::a_later_declaration_reads_an_earlier_type`.
- `Absence`, `ObligationEntry`, `ObligationLedger` and `ObligationCount`: the absence-only ledger. Witnesses: `module::tests::every_owed_hole_enters_the_ledger_in_order`, `module::tests::a_refusal_never_enters_the_ledger`; the type-level half — no refusal converts to an entry, no caller forges an absence — is held by the compile-fail blocks in `ObligationEntry`'s documentation, exercised by the doc-test lane rather than named as witnesses.
- `CheckRefusal`, `Mismatch`, `CheckingForm`, `ExpectedShape`, `UnadmittedFormer`, `TermNode`, `TypeNode` and `CoreNode`: every refusal, naming its node. Witnesses: one witness per variant, each asserting the exact refusal and its class — `judgement::tests::a_mismatched_literal_is_refused_with_both_types`, `judgement::tests::a_mismatched_application_is_refused_at_the_computation_bridge`, `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`, `judgement::tests::an_elimination_of_the_wrong_former_is_a_shape_mismatch`, `module::tests::each_combination_of_halves_gets_its_verdict`, `module::tests::a_declaration_cannot_read_its_own_type`, `judgement::tests::every_value_former_is_answered_in_both_modes`, `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`, `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`, `judgement::tests::a_dangling_term_is_refused_as_a_fault`, `module::tests::an_admission_out_of_order_is_refused`, `judgement::tests::a_result_of_the_wrong_kind_is_a_machine_fault`.
- `CheckRefusal::classify`: the classifier. Witnesses: `refusal::tests::every_refusal_carries_its_pinned_class`, `refusal::tests::the_classification_ignores_the_payload`, `refusal::tests::the_absence_class_has_no_inhabitant`.

## Expected features

- **One arena per context.** Every id a declaration carries resolves in the `CoreArena` the `CheckingContext` was built over; an id that does not is refused as a dangling node, never read.
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
```

## The former decides the mode

Every former has one direction. Variables, constants, the unit value and integer and string literals synthesise; a force synthesises the body of its value's thunk type; an application synthesises the codomain of its head's arrow, after checking its argument against the domain. A thunk checks against `U C`, a lambda against `A → C`, a return against `F A`. A synthesising term in checking position synthesises and then crosses a bridge; a checking form in synthesis position is refused, naming the form. The direction is a crate-local type declared as the judgement's direction, and the `mode_dispatch_wildcard` lint from the workspace's policy library refuses any match on it, or on a parameter declared to carry the expected type, that answers a case through a fallback arm. A rule added in one direction and forgotten in the other does not compile.

The alternatives were a mode register with a type-directed default, which is what the earlier implementation had; the same constraint as a review convention; and a workflow gate matching source text, which cannot tell a match on a direction from any other match. The choice reverses when the judgement is restated so that a term's syntactic class is itself a type, at which point the arm the lint looks for cannot be written.

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

The judgement has rules for the fragment the surface lowers: the integer and string atoms, the unit type, thunks, returners and the non-dependent arrow among types; variables, constants, unit, integer and string literals, thunks, forces, applications, lambdas and returns among terms. Every other former of the core vocabulary — the pair, the injection, the value lift, the numeric literal, the bind, the case, the numeric atom, the product, the sum, the universe, the type lift, the element type, the abstract atom and the dependent arrow — is `OutOfFragment` naming the former, wherever it is met. No former falls through to an opaque or unknown reading. The case stays out in particular because the fragment has no sum to eliminate and because its synthesising form adds a merge of its branches' types, a third comparison site. A former leaves this list when its rule enters, with its witnesses.

## Whose fact a refusal is

`CheckRefusal::classify` is a `const`, wildcard-free match that binds no payload. A type mismatch, a shape mismatch, a checking form in synthesis position and an unknown constant are malformed source, the author's mistake. A former outside the fragment is unrepresentable. An unbound index, an exhausted allowance, a dangling id, an admission out of order and a machine invariant are engine faults: a producer that resolves binders and positions never hands the checker an unbound index or an out-of-order admission, so either one is the producer's fault, not the author's; the machine invariant reports a miscount of the machine's own frames instead of asserting it. The absence class has no refusal, because obligations come from a declaration's shape. The alternative for the unbound index — classing it as the author's — would hide a resolution bug in the producer behind a source diagnostic; it reverses if a producer ever hands over unresolved author text.

## The checker owns its context

`CheckingContext` wraps `gandr-core-term`'s flat, de Bruijn binder stack rather than extending it: the signature table, the highest admission position, the atoms and the allowance live here, and the binder stack is empty between judgements and restored to where it stood whenever a run is refused. The alternative was adding the signature table to the core crate; the wrapper moves down when a second consumer needs the same one.

## One machine, one allowance, no memo

Every face runs one machine of goals and frames, charged one step per transition against the context's `CheckBudget`, so a term as deep as memory holds is judged without a native stack and every run is bounded whatever its sharing. A subterm reached twice is judged twice: the fragment's terms come from source text, whose sharing is the author's repetition, and the allowance bounds the rest. The alternative is a check memo keyed by node and context, the seam `gandr-kernel-check-memo` already provides; it becomes worth its bookkeeping when a producer starts sharing aggressively, which an elaborator's output will.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
