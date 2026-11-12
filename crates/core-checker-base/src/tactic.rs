//! A splice's tactic, run at the goal its hole holds.
//!
//! A hole a splice `~t` writes ([`HoleOrigin::Spliced`]) is met where a value
//! is checked against a type. Its goal is the binders open there, each at its
//! declared type, and that type. The tactic its name carries answers a term
//! over the goal's binders: `assumption` the innermost binder whose type
//! converts with the goal's, and `intro(t)` a thunk of a lambda whose body is
//! `t`'s answer at the goal of the function type's codomain, the lambda's
//! binder open. The judgement takes the answer as its next goal, checked
//! against the splice's goal, and refuses a refused answer naming the tactic,
//! so no tactic is trusted; the answer then fills the hole as a metavariable's
//! solution does, and the body judged again with it is the one the kernel
//! replays.
//!
//! A goal is the checker's own: its binders are the context's slots and its
//! type a core type, read in place, so `intro`'s new goal is the context with
//! one more binder, the codomain read under it. Nothing in the goal is a code
//! the language holds; a tactic written in gandr would read one through codes
//! of terms over a context, which the language does not hold.
//!
//! [`HoleOrigin::Spliced`]: gandr_core_term::hole::HoleOrigin::Spliced

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::CodomainScope;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::matched_function;
use gandr_core_term::hole::matched_returner;
use gandr_core_term::hole::matched_thunk;
use gandr_core_term::shift_comp_type;
use gandr_core_term::shift_value_type;
use gandr_core_term::tactic::Tactic;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::conversion::Agreement;
use crate::refusal::CheckRefusal;
use crate::refusal::TacticFault;

/// The answer the tactic the splice hole `hole`, standing at `at`, carries
/// gives at the goal of `expected` over the binders open now.
///
/// # Specification
/// - requires: `hole`'s origin is a splice's; `expected` is formed, read under
///   the binders open now.
/// - ensures: the answer, a term over the binders open now, which the caller
///   judges against `expected`; the binders open as before.
/// - fails: [`CheckRefusal::TacticRefused`] at `at`, naming the tactic, with
///   [`TacticFault::NoHypothesis`] when `assumption` meets no binder of its
///   goal's type and [`TacticFault::NoFunction`] when `intro` meets a goal of
///   no function type; [`CheckRefusal::MachineInvariant`] for a hole that
///   carries no tactic or a binder count past any index; a conversion's or an
///   unfolding's own refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — `assumption` at a goal one binder answers fills the hole
///   with that binder, and `intro(assumption)` at a function goal with the
///   identity; a goal no binder answers and an `intro` at a value goal are
///   refused naming why.
/// - witness: `tactic::tests::assumption_answers_the_innermost_binder_of_the_goal_type_2762`
/// - witness: `tactic::tests::intro_states_its_new_goal_under_the_binder_it_opens_2762`
/// - witness: `tactic::tests::a_tactic_with_no_answer_names_why`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth,
)]
pub fn answer(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    hole: HoleId,
    expected: ValueTypeId,
) -> Result<ValueId, CheckRefusal>
{
    let tactic = hole.tactic().ok_or(CheckRefusal::MachineInvariant)?;
    let answered = if tactic.body().is_none() {
        assumption(context, expected)?
    }
    else {
        let head = context.whnf_value_type(expected)?;
        match matched_thunk(context.arena_mut(), head) {
            Maybe::Present(suspended) => {
                let mut opened = BinderDepth::default();
                let body = introduce(context, tactic, suspended, &mut opened);
                for _binder in 0 .. usize::from(opened) {
                    context
                        .binders()
                        .close(Zone::Intuitionistic)
                        .map_err(|_unopened| CheckRefusal::MachineInvariant)?;
                }
                body?.map(|inner| {
                    let arena = context.arena_mut();
                    let lambda = (0 .. usize::from(opened))
                        .fold(inner, |lambda, _binder| arena.computation_lambda(lambda));
                    arena.value_thunk(lambda)
                })
            },
            Maybe::Absent(_) => Err(TacticFault::NoFunction),
        }
    };
    answered.map_err(|fault| CheckRefusal::TacticRefused { at, tactic, fault })
}

/// The body of `tactic`'s lambdas at the computation goal `expected`: one
/// binder opened per introduction, at its function type's domain, the goal
/// read on at the codomain, and the return of `assumption`'s answer at the
/// last goal's returned type.
///
/// # Specification
/// - requires: `tactic` makes at least one introduction; `expected` is formed,
///   read under the binders open now.
/// - ensures: the body, a computation under the binders open now and those
///   opened, `opened` counting the binders it leaves open, each an introduction
///   made, failed or not.
/// - fails: [`TacticFault::NoFunction`], inside, when a goal an introduction
///   meets is no function type at its weak head, and
///   [`TacticFault::NoHypothesis`] when the last goal returns no value or no
///   binder answers it; outside, a conversion's or an unfolding's own refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two introductions at a polymorphic identity's type open
///   two binders, the second's type reading the first, and an introduction at a
///   value goal is refused.
/// - witness: `tactic::tests::intro_states_its_new_goal_under_the_binder_it_opens_2762`
/// - witness: `tactic::tests::a_tactic_with_no_answer_names_why`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| usize::from(context.depth(Zone::Intuitionistic))
        == usize::from(depth).saturating_add(usize::from(*opened)),
)]
fn introduce(
    context: &mut CheckingContext<'_>,
    tactic: Tactic,
    expected: CompTypeId,
    opened: &mut BinderDepth,
) -> Result<Result<ComputationId, TacticFault>, CheckRefusal>
{
    let mut goal = expected;
    let mut pending = tactic;
    while let Some(body) = pending.body() {
        let head = crate::codata::read(context, goal)?;
        let Maybe::Present(matched) = matched_function(context.arena_mut(), head)
        else {
            return Ok(Err(TacticFault::NoFunction));
        };
        goal = match matched.scope() {
            CodomainScope::Ambient => shift_comp_type(
                context.arena_mut(),
                matched.codomain(),
                Binders::from(1_u32),
            )
            .settle(context.arena_mut()),
            CodomainScope::UnderBinder => matched.codomain(),
        };
        context
            .binders()
            .open(Zone::Intuitionistic, matched.domain());
        *opened = BinderDepth::from(usize::from(*opened).saturating_add(1));
        pending = body;
    }
    let head = crate::codata::read(context, goal)?;
    let Maybe::Present(result) = matched_returner(context.arena_mut(), head)
    else {
        return Ok(Err(TacticFault::NoHypothesis));
    };
    Ok(assumption(context, result)?.map(|value| context.arena_mut().computation_return(value)))
}

/// `assumption`'s answer at the value goal `expected`: the innermost binder
/// open now whose declared type, read here, converts with it.
///
/// # Specification
/// - requires: `expected` is formed, read under the binders open now.
/// - ensures: the intuitionistic variable of the innermost such binder; the
///   binders open as before.
/// - fails: [`TacticFault::NoHypothesis`], inside, when no binder's type
///   converts with `expected`; outside, a conversion's own refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two binders of the goal's type answer the inner one, and
///   a goal neither answers is refused.
/// - witness: `tactic::tests::assumption_answers_the_innermost_binder_of_the_goal_type_2762`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth,
)]
fn assumption(
    context: &mut CheckingContext<'_>,
    expected: ValueTypeId,
) -> Result<Result<ValueId, TacticFault>, CheckRefusal>
{
    let depth = usize::from(context.depth(Zone::Intuitionistic));
    for place in 0 .. depth {
        let index = u32::try_from(place)
            .map(DeBruijnIndex::from)
            .map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let declared = context
            .binders()
            .declared(Zone::Intuitionistic, index)
            .map_err(|_unbound| CheckRefusal::MachineInvariant)?;
        let read = shift_value_type(context.arena_mut(), declared, Binders::past(index))
            .settle(context.arena_mut());
        if crate::conversion::equivalent(context, read, expected)? == Agreement::Convertible {
            return Ok(Ok(context
                .arena_mut()
                .value_variable(Zone::Intuitionistic, index)));
        }
    }
    Ok(Err(TacticFault::NoHypothesis))
}

#[cfg(test)]
mod tests;
