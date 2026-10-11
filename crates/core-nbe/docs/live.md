# Live evaluation

How `gandr-core-nbe` evaluates a program with holes, compares around them, resumes after a fill and matches against them. The crate's [README](../README.md) states the rest of the crate and lists every feature with its witnesses.

<!-- toc -->
- [References](#references)
- [A hole evaluates to a neutral](#a-hole-evaluates-to-a-neutral)
- [A comparison over a hole declines](#a-comparison-over-a-hole-declines)
- [Filling resumes rather than restarts](#filling-resumes-rather-than-restarts)
- [A match over a hole answers per arm](#a-match-over-a-hole-answers-per-arm)
- [Witnesses](#witnesses)
<!-- tocstop -->

## References

- Cyrus Omar, Ian Voysey, Ravi Chugh and Matthew A. Hammer. "Live Functional Programming with Typed Holes." _Proceedings of the ACM on Programming Languages_ 3 (POPL), 2019. <https://doi.org/10.1145/3290327> — evaluation around holes to indeterminate results, and fill-and-resume commuting with filling the program.
- Yongwei Yuan et al. "Live Pattern Matching with Typed Holes." _Proceedings of the ACM on Programming Languages_ 7 (OOPSLA1), 2023. <https://doi.org/10.1145/3586048> — matching a scrutinee that may hold a hole, against patterns that may hold one, in three values.

## A hole evaluates to a neutral

Evaluation meets a hole and does not stop: a hole evaluates to a neutral headed by `NeutralHead::Hole`, closed over the environment it was met in as a `Suspended` closure, and every elimination that could not fire because of it stacks on the neutral's spine. The result is indeterminate rather than an error, so an unfinished program still has a value to show; a mark is suspended the same way under `NeutralHead::Mark`, its body never run because it was not well typed (Omar et al., POPL 2019). Readback writes a suspended hole back as the hole, and a suspended mark as the mark over its body with the body's free variables replaced by the read-back entries of its environment.

## A comparison over a hole declines

A comparison that meets a hole or a mark on either side answers `Deferral::Indeterminate` from the search-free steps and `DeclineReason::Indeterminate` from the machine: a fill may still make the sides agree or differ, so no verdict is the comparison's to give, and no refutation rests on a hole. A neutral headed by a hole or a mark carries a closure, so its cached word is flexible and the guard decides nothing about it either.

## Filling resumes rather than restarts

`fill_and_resume` writes every hole of one name in a result: each hole closure reads back as the fill, its free variables replaced by the read-back entries of its environment, a hole kept inside a retained source face is filled where it stands, and the written term is evaluated, so an elimination stuck on the hole fires and what was already reduced stays reduced. Filling the result agrees with evaluating the filled program, the commutation the paper proves and the witnesses check. The alternative was re-evaluating the filled program from the start, which repeats every reduction the hole did not block; it remains the reference the fill is compared against.

## A match over a hole answers per arm

`match_pattern` classifies one arm against a scrutinee as satisfied with its bindings, refuted, or possibly when a pattern hole or a scrutinee stuck on a hole decides. `select_arm` stops at the first arm not refuted, and is indeterminate when that arm only possibly matches, because a later arm the fill might still reach is not the one the finished program takes (Yuan et al., OOPSLA 2023). A `Matched` projects to `gandr_core_term::pattern::BranchStatus`, the vocabulary static coverage in `gandr-core-checker` answers in too.

## Witnesses

`live::tests::a_hole_evaluates_to_a_neutral_carrying_its_environment`, `live::tests::a_computation_hole_keeps_the_eliminations_that_could_not_fire`, `live::tests::a_mark_reads_back_through_its_environment`, `live::tests::a_comparison_that_meets_a_hole_declines`, `live::tests::filling_resumes_where_the_hole_stood`, `live::tests::a_fill_leaves_other_holes_standing`, `live::tests::a_match_over_a_hole_answers_per_arm`, `live::tests::a_determinate_match_binds_left_to_right`.
