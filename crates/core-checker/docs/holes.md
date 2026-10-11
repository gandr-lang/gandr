# Holes, marks and coverage

The hole surface of `gandr-core-checker`: how the judgement reads a hole, a mark and the unknown type, the total elaboration that marks a refusal and goes on, three-valued match coverage, and what the kernel bridge does with a hole and a mark. The crate's [README](../README.md) states the rest of the crate and cites the papers this page follows.

<!-- toc -->
- [Holes come in two grains, and the unknown type is consistent with every type](#holes-come-in-two-grains-and-the-unknown-type-is-consistent-with-every-type)
- [A total elaboration marks and goes on](#a-total-elaboration-marks-and-goes-on)
- [Coverage is three-valued](#coverage-is-three-valued)
- [What the unknown type cannot do](#what-the-unknown-type-cannot-do)
- [A term hole is refused where it stands, and a mark erased](#a-term-hole-is-refused-where-it-stands-and-a-mark-erased)
- [Witnesses](#witnesses)
<!-- tocstop -->

## Holes come in two grains, and the unknown type is consistent with every type

A declaration with a declared type and no body is a hole at the declaration's grain, in checking position: it absorbs the declared type and owes it, and its verdict carries the `ObligationEntry` so a caller judging one declaration needs no ledger. A declaration with neither half is the same hole in synthesis position and is refused as a checking form: given the unknown type, it would enter the signature table as a type every later reader is consistent with, and one missing signature would travel silently through the module.

A hole written inside a body is a term hole of `gandr-core-term`, in either family. The judgement reads it, and a mark, without contents: in synthesis it has the unknown type, in checking position it checks against whatever type it is handed. A rule that demands a former of a type reads it through the matched-type operations, under which the unknown type matches every former with unknown components, so an introduction checks against the unknown type by checking its parts, and an elimination of a term of the unknown type goes on with unknown premises. Conversion treats the unknown type as consistent with every type: either side unknown agrees, at the root of a type, of a decoded code and of a data index. Consistency is not transitive, and nothing here composes it: each crossing compares one synthesised type with one expected type (Hazelnut, POPL 2017).

This replaces the earlier posture, in which no type was unknown and a mismatch was never absorbed by a hole elsewhere in the term. The alternatives were keeping that posture with a fresh metavariable per hole, which needs a solver the fragment does not have, and consistency with runtime casts, which the kernel would have to trust. The unknown type never reaches the kernel: [the bridge refuses it](#a-term-hole-is-refused-where-it-stands-and-a-mark-erased). The choice reverses when an inference feature needs a hole's type to drive a solution: the hole then gets a metavariable with provenance, and the unknown type becomes its unsolved state.

## A total elaboration marks and goes on

`elaborate_value` and `elaborate_comp` run the judgement's own machine totally. Each value or computation goal the run descends into is an anchor; a refusal other than an engine fault drops the frames, binders and field types the innermost anchor's term opened, records a `MarkEntry` at that term, and answers its goal as the judgement would have — checked in checking position, the unknown type in synthesis. A term that cannot synthesise is marked and then checked against the unknown type, so its parts are judged and their own errors located. The elaborated term wraps every marked node in a mark former naming its entry, and checks against the type the run produced. A strict run and a total run take the same steps until the strict run refuses, so the total run marks nothing exactly when the strict judgement accepts, and its first mark carries the strict refusal; a property test drives both over the free term generator (Zhao et al., POPL 2024).

A refusal raised on resuming a rule's own frame belongs to that rule's term, so the run marks the elimination that met a wrong former rather than its operand, where the marked lambda calculus marks the operand. A mark stands on a node, so a node shared by two positions is marked at both. Total elaboration is an entry beside the strict faces: `check_module` reports the strict verdicts. The alternative was a marking `check_module`, which changes every caller's verdicts; it is chosen when an editor face needs the marked declarations in the module report.

## Coverage is three-valued

`cover` answers a match's exhaustiveness and each arm's redundancy, each as one of three values: definite either way, or possibly when a pattern hole or a signature the program has not fixed decides. Both questions reduce to usefulness (Maranget, JFP 2007), run as a worklist of disjunctive problems charged against the context's allowance. A pattern hole is read at its two bounds — matching nothing, which makes its whole row match nothing, and a wildcard — and only agreement is definite: exhaustive when the wildcard is useless with the arms' holes matching nothing, inexhaustive when it is useful with them as wildcards, redundant when the arm is useless with its own holes as wildcards and the holes above matching nothing, irredundant in the opposite reading (Yuan et al., OOPSLA 2023). A column of the unknown type is read with constructors no arm names for the bound that grows usefulness and with the least signature its heads allow for the bound that shrinks it, and as inhabited in both.

The lower bound reads an arm's own hole as matching nothing, so an arm with a hole is never definitely irredundant; reading the hole as some single value of its type sharpens that, and is the reversal once an editor face reports irredundancy on unfinished arms. The core calculus has no match former, so `cover` takes a pattern table and a scrutinee type rather than a term; a core match former would bring the same answers into the judgement's own rule.

## What the unknown type cannot do

A path type's endpoints and a nominal type's constructors are read off the type itself, so a transport over the unknown type, and a native data case or a record projection whose scrutinee has the unknown type, is refused by the strict judgement and marked by a total one. A data index compares as consistent with a hole or a mark at its root; a hole deeper inside an index is compared as syntax. The unknown type forms at the lowest level: a judgement that asks its universe gets the value universe at level zero. Each limit reverses with the consumer that needs it — a typed transport, data case or projection over an unfinished scrutinee.

## A term hole is refused where it stands, and a mark erased

The kernel has no hole and no unknown type, so neither crosses. Erasure meets a term hole as a node of the term it walks and refuses the declaration with `Refusal::Hole`, naming the hole and the node it stands at; the unknown type, wherever erasure reads a type, is `Refusal::Unknown`. Both are the author's absence, classified `UserAbsence`. A mark former is erased to its body's image (Hazelnut's mark erasure): the kernel re-derives the body, so a mark never makes the kernel accept a body it would refuse, and a mark around a well-typed body costs nothing. The differential witness shows, in one artifact, the refusal, the same declaration with its hole filled admitted as a definition, a mark around a good body admitted, and a mark around a bad one rejected by the kernel. The kernel's input stays closed and hole-free.

The alternative was an axiom per hole, abstracted over the hole's context, so a declaration with a hole would cross and its audit would name the assumption; it is chosen when an artifact must cross before its holes are filled. The term mark former is not a [refused declaration](../README.md#a-mark-crosses-as-nothing), whose outcome is `Outcome::Marked` and which crosses as nothing.

## Witnesses

- Holes, marks and the unknown type in the faces: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`, `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`, `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`, `view::tests::the_unknown_type_and_the_decode_of_a_hole_view_alike`.
- Total elaboration: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`, `judgement::elaboration::tests::a_term_that_cannot_synthesise_is_checked_against_the_unknown_type`, `judgement::elaboration::tests::an_unfilled_hole_elaborates_to_a_type_and_evaluates_indeterminate`, `judgement::elaboration::tests::the_strict_judgement_is_the_total_runs_oracle`.
- Coverage: `coverage::tests::usefulness_decides_exhaustiveness_and_redundancy`, `coverage::tests::literals_never_complete_and_nested_columns_specialise`, `coverage::tests::a_nominal_type_is_complete_when_every_constructor_stands`, `coverage::tests::a_pattern_hole_is_answered_possibly`, `coverage::tests::an_unknown_scrutinee_reads_the_least_and_the_widest_signature`.
- The bridge: `bridge::tests::a_hole_is_refused_where_it_stands_and_its_filling_is_admitted`.
