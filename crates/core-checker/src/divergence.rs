//! Divergence as a row entry: a partial fixpoint states that it may run
//! forever.
//!
//! A fixpoint with partial evidence is a loop the checker cannot see out of.
//! It checks only at a type each returner of which holds [`DIV`], the host
//! interface with no operation: the returners its arrows and dependent arrows
//! end in, and those of each component of a lazy product. A returner whose
//! row lacks it refuses the fixpoint as a [`CheckRefusal::TypeMismatch`]
//! whose synthesised type is the expected one with `Div` added to every such
//! row, which is the row the declaration has to write. Nothing eliminates the
//! entry: a caller of a diverging function holds it in its own row, as it
//! holds any interface its callee performs, and a handler or a capability
//! scope of `Div` has no operation to answer and leaves it in the row it
//! answers at. The empty row is the row of a computation that returns, and a
//! conversion drops an unread call of a variable whose type ends in empty rows
//! alone ([`returning`]): it runs to its end and nothing observes it.
//!
//! # Boundaries
//!
//! - A fixpoint whose body never names its own binder passes: it does not
//!   recurse, so it runs its body once.
//! - The unknown type passes: it is consistent with every row.
//! - A codata type passes: its observations answer one at a time, and the
//!   lowering admits a recursive call only as the whole of an observation's
//!   arm, so each observation yields before the function runs again.
//! - The fixpoint of a ruled operation passes: its rules are oriented, which
//!   the kernel decides when it admits them, so its recursion terminates.
//! - A decode of a computation code no definition unfolds is refused as a
//!   [`CheckRefusal::ShapeMismatch`] wanting a returner: its row is not seen,
//!   so it cannot state the entry.

#[cfg(test)]
mod tests;

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::Calls;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectPresence;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::Purity;
use gandr_core_term::effect::host::DIV;
use gandr_core_term::effect::host::divergence;
use gandr_core_term::row::Label;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// What a partial fixpoint's type says about divergence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Divergence
{
    /// Every returner the type ends in holds [`DIV`], or none is seen.
    Stated,
    /// Some returner lacks it: the type with [`DIV`] added to each that does.
    Unstated(CompTypeId),
}

/// Refuse the partial fixpoint `at` over `body` unless `expected` states that
/// it may run forever, its body never names its own binder, or the
/// declaration under judgement is a ruled operation.
///
/// # Specification
/// - requires: `expected` is formed; `body` is the body of the fixpoint `at`.
/// - ensures: success exactly when the admitted declaration carries operation
///   rules, `body`'s support omits its innermost variable, or [`stated`]
///   answers [`Divergence::Stated`].
/// - fails: [`CheckRefusal::TypeMismatch`] at `at`, synthesising the type
///   [`stated`] rebuilt and expecting `expected`; as [`stated`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a loop at a returner with and without the entry, a
///   fixpoint that never names itself at the empty row, and a ruled operation's
///   fixpoint at the empty row, each asserted as the exact verdict.
/// - witness: `divergence::tests::a_partial_fixpoint_states_div_in_every_row_it_ends_in`
/// - witness: `divergence::tests::a_fixpoint_that_never_recurses_needs_no_entry`
/// - witness: `divergence::tests::a_ruled_operation_terminates_by_its_rules`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::TypeMismatch(Mismatch::Computation { at: site, expected: wanted, .. })) => site == at && wanted == expected,
    | Ok(()) | Err(_) => true,
})]
pub fn require(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    body: ComputationId,
    expected: CompTypeId,
) -> Result<(), CheckRefusal>
{
    if !context.admitted_rules().is_empty() {
        return Ok(());
    }
    let support = context
        .arena()
        .computation_support(body)
        .ok_or(CheckRefusal::DanglingNode {
            node: CoreNode::Term(TermNode::Computation(body)),
        })?;
    if let Maybe::Absent(_) = support.rank(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)) {
        return Ok(());
    }
    match stated(context, at, expected)? {
        Divergence::Stated => Ok(()),
        Divergence::Unstated(synthesised) => {
            Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
                at,
                synthesised,
                expected,
            }))
        },
    }
}

/// Whether every returner `expected` ends in holds [`DIV`], and the type with
/// it added where one does not.
///
/// # Specification
/// - requires: `expected` is formed.
/// - ensures: [`Divergence::Stated`] when each returner reached through arrows,
///   dependent arrows, lazy-product components and decodes that unfold holds
///   [`DIV`]; otherwise [`Divergence::Unstated`] with the type whose every such
///   returner holds it, the rest unchanged.
/// - fails: [`CheckRefusal::ShapeMismatch`] at `at` wanting a returner for a
///   decode no definition unfolds; [`CheckRefusal::EffectSignatureConflict`] at
///   `at` for a row whose own `Div` performs an operation; the weak-head
///   reading's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a returner, an arrow to one, a lazy product with one
///   component stating the entry and one not, and a returner already holding
///   it, each asserted as the exact answer.
/// - witness: `divergence::tests::a_partial_fixpoint_states_div_in_every_row_it_ends_in`
/// - witness: `divergence::tests::a_dependent_arrow_states_div_in_its_codomain_and_a_stuck_decode_is_refused`
#[spec(ensures: |ret| match ret {
    | Ok(Divergence::Unstated(rebuilt)) => rebuilt != expected,
    | Ok(Divergence::Stated) | Err(_) => true,
})]
pub fn stated(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    expected: CompTypeId,
) -> Result<Divergence, CheckRefusal>
{
    // Walk down first: each node is read at its weak head and recorded after
    // the node it stands under, so the rebuild below meets children first.
    let mut order: Vec<(CompTypeId, CompTypeId)> = Vec::new();
    let mut pending = vec![expected];
    while let Some(shape) = pending.pop() {
        let head = context.whnf_comp_type(shape)?;
        order.push((shape, head));
        match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { codomain, .. } | CompTypeView::Pi { codomain, .. } => {
                pending.push(codomain);
            },
            CompTypeView::With(components) => pending.extend(components.iter().copied()),
            CompTypeView::Element { .. } => {
                return Err(CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Returner,
                    found: TypeNode::Computation(shape),
                });
            },
            CompTypeView::Returner { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. } => {
            },
        }
    }
    let entry = EffectRow::singleton(divergence());
    let name = gandr_core_term::effect::EffectLabel::Interface(Label::from(DIV));
    let mut rebuilt: BTreeMap<CompTypeId, CompTypeId> = BTreeMap::new();
    for &(shape, head) in order.iter().rev() {
        let arena = context.arena();
        let replaced = match comp_type_view(arena, head)? {
            CompTypeView::Returner { result, effects } => match effects.contains(&name) {
                EffectPresence::Present => None,
                EffectPresence::Absent => {
                    let row = effects.union(&entry, arena).map_err(|_conflict| {
                        CheckRefusal::EffectSignatureConflict {
                            at,
                            first: head,
                            second: expected,
                        }
                    })?;
                    Some(
                        context
                            .arena_mut()
                            .comp_type_returner_with_effects(result, row),
                    )
                },
            },
            CompTypeView::Arrow { domain, codomain } => rebuilt
                .get(&codomain)
                .copied()
                .map(|codomain| context.arena_mut().comp_type_arrow(domain, codomain)),
            CompTypeView::Pi { domain, codomain } => rebuilt
                .get(&codomain)
                .copied()
                .map(|codomain| context.arena_mut().comp_type_pi(domain, codomain)),
            CompTypeView::With(components) => components
                .iter()
                .any(|part| rebuilt.contains_key(part))
                .then(|| {
                    components
                        .iter()
                        .map(|part| rebuilt.get(part).copied().unwrap_or(*part))
                        .collect::<Vec<CompTypeId>>()
                })
                .map(|parts| context.arena_mut().comp_type_with(&parts)),
            CompTypeView::Element { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. } => {
                None
            },
        };
        if let Some(replaced) = replaced {
            let _previous = rebuilt.insert(shape, replaced);
        }
    }
    Ok(rebuilt
        .get(&expected)
        .copied()
        .map_or(Divergence::Stated, Divergence::Unstated))
}

/// Whether every call of a variable of type `bound` returns.
///
/// # Specification
/// - requires: `bound` is formed.
/// - ensures: [`Calls::Return`] exactly when `bound`'s weak head is a thunk
///   type each returner of which, reached through arrows, dependent arrows and
///   lazy-product components at their weak heads, has the empty row;
///   [`Calls::Unknown`] for any other type, and for one that reaches a decode
///   no definition unfolds, a codata type or the unknown type.
/// - fails: the weak-head reading's refusal.
/// - panics: none.
/// - executable: none — the answer reads the arena's types at their weak heads,
///   which the witness holds to stated types.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` loop over an explicit worklist, not recursion.
/// - measure: the computation types under the thunk, each read once: a node is
///   replaced by its codomain or its components, minted before it.
///
/// # Adequacy
/// - hypothesis: L3 — a function to a returner at the empty row, the same at a
///   row holding `Div`, a lazy product with one such component, and a value
///   type that is no thunk, each asserted as the exact answer.
/// - witness: `divergence::tests::a_call_returns_only_where_every_row_is_empty`
pub fn calls(
    context: &mut CheckingContext<'_>,
    bound: ValueTypeId,
) -> Result<Calls, CheckRefusal>
{
    let head = context.whnf_value_type(bound)?;
    let ValueTypeView::Thunk(computation) = value_type_view(context.arena(), head)?
    else {
        return Ok(Calls::Unknown);
    };
    let mut pending = vec![computation];
    while let Some(shape) = pending.pop() {
        let head = context.whnf_comp_type(shape)?;
        match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { codomain, .. } | CompTypeView::Pi { codomain, .. } => {
                pending.push(codomain);
            },
            CompTypeView::With(components) => pending.extend(components.iter().copied()),
            CompTypeView::Returner { effects, .. } => {
                if effects.purity() != Purity::Pure {
                    return Ok(Calls::Unknown);
                }
            },
            CompTypeView::Element { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. } => {
                return Ok(Calls::Unknown);
            },
        }
    }
    Ok(Calls::Return)
}

/// The intuitionistic variables of the judgement's binders whose calls
/// return, by index, innermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each index whose declared type [`calls`] answers
///   [`Calls::Return`] for, ascending.
/// - provides: the variables a reflexivity's endpoint conversion discards an
///   unread call of.
/// - fails: as [`calls`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`calls`], read at every binder.
/// - witness: `divergence::tests::an_unread_call_converts_only_where_its_row_is_empty`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |indices| indices.is_sorted()))]
pub fn returning(context: &mut CheckingContext<'_>) -> Result<Vec<DeBruijnIndex>, CheckRefusal>
{
    let depth = u32::try_from(usize::from(context.binders().depth(Zone::Intuitionistic)))
        .map_err(|_overflow| CheckRefusal::MachineInvariant)?;
    let mut indices = Vec::new();
    for index in (0 .. depth).map(DeBruijnIndex::from) {
        let declared = context
            .binders()
            .declared(Zone::Intuitionistic, index)
            .map_err(|_unbound| CheckRefusal::MachineInvariant)?;
        if calls(context, declared)? == Calls::Return {
            indices.push(index);
        }
    }
    Ok(indices)
}
