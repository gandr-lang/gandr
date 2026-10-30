//! A model's omitted law, discharged.
//!
//! A module ascribed `Model(T)` owes one component per law `T` states. One it
//! omits asks for a filler without naming its source, so the lowering states
//! the law's type and writes no body
//! ([`body::Absent::Discharged`](crate::body::Absent::Discharged)). The checker
//! answers the component from the sources of a filler, in order.
//!
//! # `here` comes first
//!
//! The law's type is `U(Π x₁ … xₙ. F Path(S, l, r))`, or `Path(S, l, r)` with
//! no telescope. [`here`] mints `thunk(λx₁ … λxₙ. return here(l))`, the
//! component a module writes by hand where the sides convert, and the checker
//! judges it at the declared type as any body. A binder the type reads with a
//! non-dependent arrow binds in the body too, so the endpoint is read one
//! binder deeper there.
//!
//! # A refusal names no other source yet
//!
//! A law whose `here` the judgement refuses is refused
//! [`CheckRefusal::UndischargedLaw`], `NoFiller.Omitted`, at its declared type.
//! The theory's derivation and the generator are the sources after `here`.
//! Each is a later unit's, and each runs before the refusal once it lands.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: discharge, a
//!   filler being the stratum's identification, completion's derivation or the
//!   generator's output, and a term asking for another refused `NoFiller`.

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ValueId;

use crate::context::CheckingContext;
use crate::formation::FormedValueType;
use crate::refusal::CheckRefusal;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// The `here` an omitted law's declared type `declared` asks for:
/// `thunk(λx₁ … λxₙ. return here(l))` over the law's telescope, or `here(l)`
/// for a law with none.
///
/// # Specification
/// - requires: `declared` is formed.
/// - ensures: the body minted is a thunk of one lambda per binder of the
///   telescope, a `Π` or an arrow, around the return of `here` at the left
///   endpoint of the path the telescope returns; a declared path with no
///   telescope gives `here` at its left endpoint. A binder an arrow reads
///   shifts the endpoint below it by one, so the endpoint names the binders the
///   lambdas bind.
/// - fails: [`CheckRefusal::UndischargedLaw`] at `declared` for a type that is
///   no law's: no path at the end of a pure telescope.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a model omitting a law whose sides convert checks with
///   the minted component, one whose sides stay apart is refused naming the
///   law, and a law over no binder discharges as `here` alone.
/// - witness: `discharge::tests::an_omitted_law_whose_sides_convert_is_here`
/// - witness: `discharge::tests::an_omitted_law_whose_sides_part_is_undischarged`
/// - witness: `discharge::tests::a_law_over_no_binder_is_here_alone`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&body| context.arena().value(body).is_some()))]
pub fn here(
    context: &mut CheckingContext<'_>,
    declared: FormedValueType,
) -> Result<ValueId, CheckRefusal>
{
    let undischarged = CheckRefusal::UndischargedLaw { at: declared.id() };
    let head = context.whnf_value_type(declared.id())?;
    let view = value_type_view(context.arena(), head)?;
    if let ValueTypeView::Path { left, .. } = view {
        return Ok(context.arena_mut().value_here(left));
    }
    let ValueTypeView::Thunk(mut current) = view
    else {
        return Err(undischarged);
    };
    let mut binders = 0_usize;
    let path = loop {
        current = match comp_type_view(context.arena(), current)? {
            CompTypeView::Pi { codomain, .. } => codomain,
            CompTypeView::Arrow { codomain, .. } => {
                let arena = context.arena_mut();
                gandr_core_term::shift_comp_type(arena, codomain, Binders::ONE).settle(arena)
            },
            CompTypeView::Returner { result, effects }
                if effects.purity() == gandr_core_term::effect::Purity::Pure =>
            {
                break result;
            },
            CompTypeView::Returner { .. }
            | CompTypeView::With(..)
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. }
            | CompTypeView::Unknown => return Err(undischarged),
        };
        binders = binders.saturating_add(1);
    };
    let ValueTypeView::Path { left, .. } = value_type_view(context.arena(), path)?
    else {
        return Err(undischarged);
    };
    let arena = context.arena_mut();
    let here = arena.value_here(left);
    let mut body = arena.computation_return(here);
    for _ in 0 .. binders {
        body = arena.computation_lambda(body);
    }
    Ok(arena.value_thunk(body))
}

#[cfg(test)]
mod tests;
