//! The directed eliminator's computation table, read by the replay.

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Seam;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::element_identity::BinderUse;
use crate::element_identity::Family;
use crate::element_identity::Mover;
use crate::element_identity::Telescope;
use crate::element_identity::binder_use;
use crate::element_identity::cell;
use crate::element_identity::componentwise;
use crate::element_identity::telescope;
use crate::encoding::ContentTable;
use crate::error::KernelError;
use crate::path_universe::Reduction;
use crate::rewrite::BinderDepth;
use crate::rewrite::RewriteOutcome;
use crate::rewrite::RewriteSupport;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_outer_value_type;

/// A ride as the replay reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RideStep
{
    /// The family, under one value binder for the moving endpoint.
    pub motive: ValueTypeId,
    /// The flow ridden along.
    pub flow: ValueId,
    /// The value at the source endpoint.
    pub value: ValueId,
}

/// The flow's head, as far as the table reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Head
{
    /// Directed reflexivity.
    Stay,
    /// A sequential composition of two flows.
    Then(ValueId, ValueId),
    /// A forward translator.
    Forward(ValueId),
    /// The arrow's action over two boundary flows.
    Function(ValueId, ValueId),
    /// A componentwise product of two universe flows.
    Product(ValueId, ValueId),
    /// A session simulation, a feedback seam or a neutral.
    Other,
}

/// One ride step, by the first row of the module table that applies.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: a reduct by the table, in row order: `stay` returns the value; a
///   sequential composition rides its first flow, then its second from the
///   result; a motive that ignores its binder returns the value; a product, a
///   sum and a list motive ride constructorwise, a list one cell per step; at
///   `El(x)` over the level-zero universe a forward flow applies its
///   translator, a function flow returns the function wrapped by its boundaries
///   — the argument ridden along the domain flow, the function applied, the
///   result ridden along the codomain flow — and a flow product rides a pair's
///   components along its two flows, left then right; at a singleton motive
///   `Flow(D, l, x)` or `Flow_U(l, x)` a `stay` value returns the flow and any
///   other value composes with it. Otherwise `Stuck`: a session simulation, a
///   feedback seam, a neutral flow and a flow product at a value that is no
///   pair have no endpoint-value action.
/// - provides: the replay's δ-free directed computation: a named flow leaves
///   the ride stuck at its head, and a named translator stands at the head of
///   its row's bind, each for the recorded dialogue to unfold.
/// - fails: `ArenaFault` on an unreadable flow, motive or component.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — `stay` rides to the value; a forward flow applies its
///   translator; a composite rides in order; a pair, a sum and a list ride
///   constructorwise; a singleton motive composes; a function flow applies its
///   boundaries in variance order; a neutral flow over a dependent motive
///   sticks; a flow product rides a pair componentwise.
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
/// - witness: `flow_universe::tests::ride_computes_through_the_motive_rows`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
/// - witness: `flow_universe::tests::a_flow_product_rides_a_pair_componentwise`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduction| match *reduction {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
}))]
pub fn ride_beta<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    term: RideStep,
) -> Result<Reduction, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let RideStep {
        motive,
        flow,
        value,
    } = term;
    let head = match arena.value(flow) {
        Some(&Value::Stay { .. }) => Head::Stay,
        Some(&Value::Then {
            first,
            second,
            seam: Seam::Sequence,
        }) => Head::Then(first, second),
        Some(&Value::ForwardFlow { translator, .. }) => Head::Forward(translator),
        Some(&Value::FunctionFlow {
            domain, codomain, ..
        }) => Head::Function(domain, codomain),
        Some(&Value::FlowProduct(first, second)) => Head::Product(first, second),
        Some(_) => Head::Other,
        None => return Err(KernelError::ArenaFault),
    };
    let one = BinderDepth::from(1_u32);
    match head {
        Head::Stay => return Ok(Reduction::Reduced(arena.computation_return(value))),
        Head::Then(first, second) => {
            let step = arena.computation_ride(motive, first, value);
            let lifted = shift_value_type(arena, table, memo, motive, one, one);
            let second = shift_value(arena, table, memo, second, BinderDepth::NONE, one);
            let moved = arena.value_variable(DeBruijnIndex::from(0_u32));
            let rest = arena.computation_ride(lifted, second, moved);
            return Ok(Reduction::Reduced(arena.computation_bind(step, rest)));
        },
        Head::Forward(_) | Head::Function(..) | Head::Product(..) | Head::Other => {},
    }
    if binder_use(arena, table, memo, Family::Type(motive)) == BinderUse::Ignored {
        return Ok(Reduction::Reduced(arena.computation_return(value)));
    }
    let family = arena
        .value_type(motive)
        .cloned()
        .ok_or(KernelError::ArenaFault)?;
    match family {
        ValueType::Product(parts) => {
            let components = match arena.value(value) {
                Some(&Value::Tuple(ref components)) if components.len() == parts.len() => {
                    components.clone()
                },
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
            };
            Ok(Reduction::Reduced(componentwise(
                arena,
                table,
                memo,
                Mover::Ride,
                (&parts, &components),
                flow,
            )?))
        },
        ValueType::Sum(parts) => {
            let (summand, payload) = match arena.value(value) {
                Some(&Value::Injection(summand, payload)) => (summand, payload),
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
            };
            let Some(&part) = parts.get(usize::from(summand))
            else {
                return Ok(Reduction::Stuck);
            };
            let step = Mover::Ride.step(arena, part, flow, payload);
            let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
            let injected = arena.value_injection(summand, bound);
            let returned = arena.computation_return(injected);
            Ok(Reduction::Reduced(arena.computation_bind(step, returned)))
        },
        ValueType::List(element) => {
            let (head, tail) = match arena.value(value) {
                Some(&Value::ListNil) => {
                    return Ok(Reduction::Reduced(arena.computation_return(value)));
                },
                Some(&Value::ListCons(head, tail)) => (head, tail),
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
            };
            Ok(Reduction::Reduced(cell(
                arena,
                table,
                memo,
                Mover::Ride,
                (element, motive),
                flow,
                (head, tail),
            )))
        },
        ValueType::Element { code, target } => {
            let universe_family = matches!(arena.value(code), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && target == Level::zero();
            if !universe_family {
                return Ok(Reduction::Stuck);
            }
            Ok(match head {
                Head::Forward(translator) => {
                    let force = arena.computation_force(translator);
                    Reduction::Reduced(arena.computation_application(force, value))
                },
                Head::Function(domain, codomain) => Reduction::Reduced(wrapped(
                    arena,
                    table,
                    memo,
                    motive,
                    (domain, codomain),
                    value,
                )),
                Head::Product(first, second) => {
                    let Some(&[left, right]) = arena.value(value).and_then(Value::components)
                    else {
                        return Ok(Reduction::Stuck);
                    };
                    let step = arena.computation_ride(motive, first, left);
                    let lifted = shift_value_type(arena, table, memo, motive, one, one);
                    let second = shift_value(arena, table, memo, second, BinderDepth::NONE, one);
                    let right = shift_value(arena, table, memo, right, BinderDepth::NONE, one);
                    let rest = arena.computation_ride(lifted, second, right);
                    let moved_left = arena.value_variable(DeBruijnIndex::from(1_u32));
                    let moved_right = arena.value_variable(DeBruijnIndex::from(0_u32));
                    let pair = arena.value_tuple(&[moved_left, moved_right]);
                    let returned = arena.computation_return(pair);
                    let rest = arena.computation_bind(rest, returned);
                    Reduction::Reduced(arena.computation_bind(step, rest))
                },
                Head::Stay | Head::Then(..) | Head::Other => Reduction::Stuck,
            })
        },
        ValueType::Flow {
            domain,
            source,
            target,
        } => {
            let singleton = matches!(arena.value(target), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && binder_use(arena, table, memo, Family::Type(domain)) == BinderUse::Ignored
                && binder_use(arena, table, memo, Family::Value(source)) == BinderUse::Ignored;
            if !singleton {
                return Ok(Reduction::Stuck);
            }
            Ok(Reduction::Reduced(composed(arena, value, flow)))
        },
        ValueType::FlowUniverse(source, target) => {
            let singleton = matches!(arena.value(target), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && binder_use(arena, table, memo, Family::Value(source)) == BinderUse::Ignored;
            if !singleton {
                return Ok(Reduction::Stuck);
            }
            Ok(Reduction::Reduced(composed(arena, value, flow)))
        },
        ValueType::Data { .. }
        | ValueType::Record(_)
        | ValueType::Session { .. }
        | ValueType::PathUniverse(..)
        | ValueType::Path { .. }
        | ValueType::Base(_)
        | ValueType::Sigma { .. }
        | ValueType::Thunk(_)
        | ValueType::Universe { .. }
        | ValueType::Lift { .. }
        | ValueType::Abstract(_)
        | ValueType::StaticPi { .. }
        | ValueType::Staged { .. } => Ok(Reduction::Stuck),
    }
}

/// The singleton row: a flow from `l` ridden along a flow from its target.
///
/// # Specification
/// - requires: the motive is `Flow(D, l, x)` or `Flow_U(l, x)` with `D` and `l`
///   ignoring the binder `x`.
/// - ensures: the ridden flow when the value is `stay`, else the composition of
///   the value then the flow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a singleton motive rides `stay` to the flow and a forward
///   flow to its composition.
/// - witness: `flow_universe::tests::ride_computes_through_the_motive_rows`
#[spec(ensures: |reduct| arena.computation(reduct).is_some())]
fn composed(
    arena: &mut TermArena,
    value: ValueId,
    flow: ValueId,
) -> gandr_kernel_term::ComputationId
{
    let result = match arena.value(value) {
        Some(&Value::Stay { .. }) => flow,
        _ => arena.value_then(value, flow, Seam::Sequence),
    };
    arena.computation_return(result)
}

/// The function flow's action on a function: `return thunk(λa'. a ←
/// ride(El, domain, a'); b ← force f a; ride(El, codomain, b))`.
///
/// # Specification
/// - requires: `motive` is `El(x)` over the level-zero universe, closed but for
///   its binder.
/// - ensures: the reduct above, each boundary flow and the function shifted
///   past the binders the reduct places outside it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function flow over a negation's boundaries rides the
///   identity function to negation by conversion replay.
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
#[spec(ensures: |reduct| arena.computation(reduct).is_some())]
fn wrapped<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    motive: ValueTypeId,
    (domain, codomain): (ValueId, ValueId),
    function: ValueId,
) -> gandr_kernel_term::ComputationId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let innermost = arena.value_variable(DeBruijnIndex::from(0_u32));
    let domain = shift_value(
        arena,
        table,
        memo,
        domain,
        BinderDepth::NONE,
        BinderDepth::from(1_u32),
    );
    let function = shift_value(
        arena,
        table,
        memo,
        function,
        BinderDepth::NONE,
        BinderDepth::from(2_u32),
    );
    let codomain = shift_value(
        arena,
        table,
        memo,
        codomain,
        BinderDepth::NONE,
        BinderDepth::from(3_u32),
    );
    let argument = arena.computation_ride(motive, domain, innermost);
    let force = arena.computation_force(function);
    let applied = arena.computation_application(force, innermost);
    let result = arena.computation_ride(motive, codomain, innermost);
    let body = arena.computation_bind(applied, result);
    let body = arena.computation_bind(argument, body);
    let lambda = arena.computation_lambda(body);
    let transported = arena.value_thunk(lambda);
    arena.computation_return(transported)
}

/// A telescope ride as the replay reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TelescopeRideStep
{
    /// The motive `Π (y : A). Π (z : B). F C`.
    pub motive: CompTypeId,
    /// The flow in the carrier.
    pub flow: ValueId,
    /// The flow over it in the fibre at its target.
    pub over: ValueId,
    /// The value at the source.
    pub value: ValueId,
}

/// One telescope ride step, by the first row of the module table that
/// applies.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: the value when both flows are `stay`; when only the carrier flow
///   is `stay(c)`, the one-binder ride along the over flow in the fibre family
///   `z. C[c, z]`; otherwise `Stuck`, as for a motive that is no telescope.
/// - provides: the replay's directed J computation.
/// - fails: `ArenaFault` on an unreadable motive layer, flow or over flow.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — `stay` along both flows returns the value; `stay` along
///   the carrier rides in the fibre; a neutral flow sticks.
/// - witness: `flow_universe::tests::directed_j_rides_the_telescope`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduction| match *reduction {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
}))]
pub fn telescope_ride_beta<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    term: TelescopeRideStep,
) -> Result<Reduction, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let TelescopeRideStep {
        motive,
        flow,
        over,
        value,
    } = term;
    let body = match telescope(arena, motive)? {
        Maybe::Present(Telescope { body, .. }) => body,
        Maybe::Absent(_) => return Ok(Reduction::Stuck),
    };
    let point = match arena.value(flow) {
        Some(&Value::Stay { point, .. }) => point,
        Some(_) => return Ok(Reduction::Stuck),
        None => return Err(KernelError::ArenaFault),
    };
    match arena.value(over) {
        Some(&Value::Stay { .. }) => Ok(Reduction::Reduced(arena.computation_return(value))),
        Some(_) => {
            let fibre = substitute_outer_value_type(arena, table, memo, body, point);
            Ok(Reduction::Reduced(
                arena.computation_ride(fibre, over, value),
            ))
        },
        None => Err(KernelError::ArenaFault),
    }
}
