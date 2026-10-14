//! The covariance gate a directed motive passes before `ride` admits it.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Allowance;
use super::FlowError;
use super::Variance;
use crate::conv::Convertibility;
use crate::conv::convert_values;
use crate::conv::convertible_value_types;
use crate::encoding::ContentTable;
use crate::replay::ReplayBudget;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::support::LooseDepths;

/// Where an occurrence of the moving binder stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sign
{
    /// Under a variance: covariant admits the binder, contravariant refuses
    /// it.
    Varies(Variance),
    /// Under a former that reads its argument both ways, or by an identity
    /// that relates it: no occurrence admits.
    Invariant,
}

impl Sign
{
    /// Reverse through an arrow domain or a flow source.
    ///
    /// # Specification
    /// trivial.
    const fn reverse(self) -> Self
    {
        match self {
            | Self::Varies(variance) => Self::Varies(variance.reverse()),
            | Self::Invariant => Self::Invariant,
        }
    }
}

/// One position of the gate's walk, with the moving binder's index there and
/// the former that holds the position.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// A value type.
    Type(ValueTypeId, Sign, DeBruijnIndex),
    /// A computation type.
    Comp(CompTypeId, Sign, DeBruijnIndex),
    /// A code an `El` reads: the binder itself, a quote read through, or a
    /// value the binder must not reach.
    Code(ValueId, Sign, DeBruijnIndex, AnyNode),
    /// A flow endpoint: the binder itself, or a value it must not reach.
    Endpoint(ValueId, Sign, DeBruijnIndex, AnyNode),
    /// A value type the binder must not reach.
    Fixed(ValueTypeId, DeBruijnIndex),
}

/// Whether a node reaches the moving binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The node does not mention the binder.
    Clear,
    /// The node mentions the binder.
    Reaches,
}

/// Decide the covariance side condition of a directed motive.
///
/// # Specification
/// - requires: `motive` formed in its context extended by the moving binder,
///   which `binder` names at the motive's top.
/// - ensures: the binder occurs only at covariant positions. Products, sums,
///   records, lists, lifts, thunks, returners, lazy pairs and a dependent
///   arrow's codomain preserve the sign; an arrow's or a dependent arrow's
///   domain and a flow's source reverse it; an `El` of a quoted type reads
///   through the quote. The binder standing as an `El` code or a flow endpoint
///   is an occurrence at the sign there. Every other position — a flow's
///   carrier, an identity's carrier and endpoints, a datatype's arguments, a
///   session's payloads, a static Pi, an `El` of any other code — is invariant,
///   and the binder must not reach it. `arena` holds what it held on entry.
/// - fails: `NonCovariantMotive` naming the former that holds the first refused
///   occurrence; `Arena` for an unreadable node; `Budget` on exhausted
///   traversal.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — the symmetry motive `Flow_U(x, a)` refuses naming its
///   flow former, a migration `U (El a → F El x)` admits, a double reversal
///   admits, an occurrence in an identity's endpoint refuses, and a motive
///   naming only outer variables admits.
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_at_ride`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && matches!(
        ret,
        Ok(()) | Err(FlowError::NonCovariantMotive(_) | FlowError::Arena | FlowError::Budget)
    ),
)]
#[inline]
pub fn check_motive(
    arena: &mut TermArena,
    motive: ValueTypeId,
    binder: DeBruijnIndex,
    budget: ReplayBudget,
) -> Result<(), FlowError>
{
    let watermark = arena.watermark();
    let verdict = walk(arena, motive, binder, budget);
    arena.truncate_to(watermark);
    verdict
}

/// The gate's walk, retaining what its reach tests mint.
///
/// # Specification
/// - requires: the caller restores the entry watermark.
/// - ensures: as [`check_motive`], without restoring the arena.
/// - fails: as [`check_motive`].
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`check_motive`].
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_at_ride`
#[spec(ensures: |ret| matches!(
    ret,
    Ok(()) | Err(FlowError::NonCovariantMotive(_) | FlowError::Arena | FlowError::Budget)
))]
fn walk(
    arena: &mut TermArena,
    motive: ValueTypeId,
    binder: DeBruijnIndex,
    budget: ReplayBudget,
) -> Result<(), FlowError>
{
    let mut allowance = Allowance(u64::from(budget));
    let mut table = ContentTable::new();
    let mut pending = Vec::from([Visit::Type(
        motive,
        Sign::Varies(Variance::Covariant),
        binder,
    )]);
    while let Some(visit) = pending.pop() {
        allowance.charge()?;
        match visit {
            | Visit::Type(id, sign, at) => {
                let site = AnyNode::ValueType(id);
                match *arena.value_type(id).ok_or(FlowError::Arena)? {
                    | ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                        pending.extend(parts.iter().map(|&part| Visit::Type(part, sign, at)));
                    },
                    | ValueType::Record(ref fields) => {
                        pending.extend(fields.values().map(|&field| Visit::Type(field, sign, at)));
                    },
                    | ValueType::List(inner) | ValueType::Lift { inner, .. } => {
                        pending.push(Visit::Type(inner, sign, at));
                    },
                    | ValueType::Thunk(body) => pending.push(Visit::Comp(body, sign, at)),
                    | ValueType::Element { code, .. } => {
                        pending.push(Visit::Code(code, sign, at, site));
                    },
                    | ValueType::Flow {
                        domain,
                        source,
                        target,
                    } => {
                        pending.push(Visit::Fixed(domain, at));
                        pending.push(Visit::Endpoint(target, sign, at, site));
                        pending.push(Visit::Endpoint(source, sign.reverse(), at, site));
                    },
                    | ValueType::FlowUniverse(source, target) => {
                        pending.push(Visit::Endpoint(target, sign, at, site));
                        pending.push(Visit::Endpoint(source, sign.reverse(), at, site));
                    },
                    | ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) => {
                    },
                    | _ => pending.push(Visit::Fixed(id, at)),
                }
            },
            | Visit::Comp(id, sign, at) => match *arena.comp_type(id).ok_or(FlowError::Arena)? {
                | CompType::Returner(result) => pending.push(Visit::Type(result, sign, at)),
                | CompType::Arrow { domain, codomain } => {
                    pending.push(Visit::Comp(codomain, sign, at));
                    pending.push(Visit::Type(domain, sign.reverse(), at));
                },
                | CompType::Pi { domain, codomain } => {
                    let under = u32::from(at).checked_add(1).ok_or(FlowError::Budget)?;
                    pending.push(Visit::Comp(codomain, sign, DeBruijnIndex::from(under)));
                    pending.push(Visit::Type(domain, sign.reverse(), at));
                },
                | CompType::With(left, right) => {
                    pending.push(Visit::Comp(right, sign, at));
                    pending.push(Visit::Comp(left, sign, at));
                },
                | CompType::Element { code, .. } => {
                    pending.push(Visit::Code(code, sign, at, AnyNode::CompType(id)));
                },
            },
            | Visit::Code(code, sign, at, site) => match *arena
                .value(code)
                .ok_or(FlowError::Arena)?
            {
                | Value::Quote(quoted) => pending.push(Visit::Type(quoted, sign, at)),
                | Value::QuoteComputation(quoted) => pending.push(Visit::Comp(quoted, sign, at)),
                | _ => occurrence(arena, &mut table, code, (sign, at), site)?,
            },
            | Visit::Endpoint(point, sign, at, site) => {
                occurrence(arena, &mut table, point, (sign, at), site)?;
            },
            | Visit::Fixed(ty, at) => {
                if reach_type(arena, &mut table, ty, at) == Reach::Reaches {
                    return Err(FlowError::NonCovariantMotive(AnyNode::ValueType(ty)));
                }
            },
        }
    }
    Ok(())
}

/// Admit or refuse one value at a sign: the binder itself stands only at a
/// covariant position, and any other value must not reach it.
///
/// # Specification
/// - ensures: `Ok` when `value` is the binder at a covariant sign, or does not
///   mention the binder.
/// - fails: `NonCovariantMotive(site)` otherwise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — the binder as a flow source refuses and as a flow target
///   admits.
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_at_ride`
#[spec(ensures: |ret| match ret {
    Ok(()) => true,
    Err(FlowError::NonCovariantMotive(named)) => named == site,
    Err(_) => false,
})]
fn occurrence(
    arena: &mut TermArena,
    table: &mut ContentTable,
    value: ValueId,
    (sign, at): (Sign, DeBruijnIndex),
    site: AnyNode,
) -> Result<(), FlowError>
{
    let admitted = match arena.value(value) {
        | Some(&Value::Variable(index)) if index == at => sign == Sign::Varies(Variance::Covariant),
        | _ => reach_value(arena, table, value, at) == Reach::Clear,
    };
    if admitted {
        Ok(())
    }
    else {
        Err(FlowError::NonCovariantMotive(site))
    }
}

/// Whether a value mentions the binder at `at`.
///
/// # Specification
/// - ensures: [`Reach::Clear`] when the value's reach stops at or below `at`,
///   or when shifting its free indices from `at` and from just past `at` gives
///   convertible values, which happens exactly when `at` itself is absent.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an endpoint naming an outer variable is clear, and one
///   naming the binder beneath a former reaches it.
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_at_ride`
#[spec(ensures: |ret| ret == Reach::Reaches || ret == Reach::Clear)]
fn reach_value(
    arena: &mut TermArena,
    table: &mut ContentTable,
    value: ValueId,
    at: DeBruijnIndex,
) -> Reach
{
    let index = u32::from(at);
    if u32::from(LooseDepths::new().value_reach(arena, value)) <= index {
        return Reach::Clear;
    }
    let Some(past) = index.checked_add(1)
    else {
        return Reach::Reaches;
    };
    let one = BinderDepth::from(1_u32);
    let from = shift_value(
        arena,
        table,
        &mut NullMemo,
        value,
        BinderDepth::from(index),
        one,
    );
    let beyond = shift_value(
        arena,
        table,
        &mut NullMemo,
        value,
        BinderDepth::from(past),
        one,
    );
    // Rewriting by a presented type's rules would only relate more shifts;
    // reading none keeps the reach conservative.
    if convert_values(arena, &crate::presented::FREE, from, beyond) == Convertibility::Convertible {
        Reach::Clear
    }
    else {
        Reach::Reaches
    }
}

/// Whether a value type mentions the binder at `at`; see [`reach_value`].
///
/// # Specification
/// - ensures: as [`reach_value`], over the value-type family, comparing the two
///   shifts structurally.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a flow whose carrier names the binder refuses.
/// - witness: `flow_universe::tests::symmetry_motive_is_refused_at_ride`
#[spec(ensures: |ret| ret == Reach::Reaches || ret == Reach::Clear)]
fn reach_type(
    arena: &mut TermArena,
    table: &mut ContentTable,
    ty: ValueTypeId,
    at: DeBruijnIndex,
) -> Reach
{
    let index = u32::from(at);
    if u32::from(LooseDepths::new().value_type_reach(arena, ty)) <= index {
        return Reach::Clear;
    }
    let Some(past) = index.checked_add(1)
    else {
        return Reach::Reaches;
    };
    let one = BinderDepth::from(1_u32);
    let from = shift_value_type(
        arena,
        table,
        &mut NullMemo,
        ty,
        BinderDepth::from(index),
        one,
    );
    let beyond = shift_value_type(
        arena,
        table,
        &mut NullMemo,
        ty,
        BinderDepth::from(past),
        one,
    );
    if convertible_value_types(arena, from, beyond) == Convertibility::Convertible {
        Reach::Clear
    }
    else {
        Reach::Reaches
    }
}
