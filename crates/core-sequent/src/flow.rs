//! Flows at run time: a flow runs as the translator it moves values with.
//!
//! The command IL carries no identity types, so a flow has no image of its
//! own. What it does carry is functions, and every flow the checker admits has
//! an action on values that a function computes: the kernel's ride table,
//! read at a motive, is a program. The focusing therefore sends each flow to a
//! thunk of one argument, its translator, and each ride to the motive's
//! action applied to that translator and the ridden value.
//!
//! | Core | Producer |
//! |---|---|
//! | `forward(f)` | `𝓥⟦f⟧`, the translator itself |
//! | `stay(a)`, a session simulation | the identity thunk |
//! | `p then q` | `thunk(force(compose) 𝓥⟦p⟧ 𝓥⟦q⟧)` |
//! | `arrow(d, c)` | `thunk(force(wrap) 𝓥⟦d⟧ 𝓥⟦c⟧)` |
//! | `flowProduct(p, q)` | `thunk(force(pair) 𝓥⟦p⟧ 𝓥⟦q⟧)` |
//! | `ride(P, p, v)` | `force(act_P) 𝓥⟦p⟧ 𝓥⟦v⟧` |
//!
//! `compose` is `thunk(λp. λq. λx. y ← force p x; force q y)`, `wrap` is
//! `thunk(λd. λc. λg. return thunk(λa'. a ← force d a'; b ← force g a; force
//! c b))` — the kernel's function-flow row with the boundaries as functions —
//! `pair` is `thunk(λp. λq. λx. a ← x.0; b ← x.1; a' ← force p a; b' ← force
//! q b; return (a', b'))` — the kernel's flow-product row, the components in
//! order — and `act_P` is `thunk(λt. λv. M_P)`, built over the motive's
//! syntax by the
//! kernel's rows in their order: at the decode of the motive's own binder `M`
//! is `force t v`; a product rides each component by its own action, a sum
//! its payload under its summand, a list each element by a native fold; the
//! singleton `y. Flow(D, l, y)` composes the ridden flow with `t`; any other
//! motive — one that ignores its binder, a run type, a family over an element
//! carrier — returns the value unchanged. That last row is exact: the checker
//! refuses at a universe carrier every motive no row computes, and over an
//! element carrier every closed flow is a stay or a composite of stays, whose
//! action is the identity.
//!
//! Every combinator is closed, so the focusing builds it in a scratch core
//! arena and focuses it into the same command arena; it is applied to the
//! flow's parts rather than closing over them, so no producer is shifted
//! under a binder it did not have. A ride of an open flow runs the same way:
//! the translator is whatever value the flow's variable is bound to at run
//! time.
//!
//! The alternative was a core-to-core pass replacing flows before focusing,
//! rejected because the replacement must rebuild every ancestor of a ride to
//! name the new node, where the focusing already visits each node once. The
//! choice reverses if the command IL gains an identity former of its own.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;

use crate::focus::FocusRefusal;

/// A closed program a flow's image applies to its parts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Combinator
{
    /// `thunk(λx. return x)`: the translator of a stay and of a session
    /// simulation.
    Identity,
    /// `thunk(λp. λq. λx. y ← force p x; force q y)`: sequential composition.
    Compose,
    /// `thunk(λd. λc. λg. return thunk(λa'. a ← force d a'; b ← force g a;
    /// force c b))`: the arrow's action on its boundaries.
    Wrap,
    /// `thunk(λp. λq. λx. a ← x.0; b ← x.1; a' ← force p a; b' ← force q b;
    /// return (a', b'))`: the flow product's action, componentwise.
    Pair,
    /// `thunk(λt. λv. M_P)`: the action of the ride motive `P`, a value type
    /// under one binder in the arena being focused.
    Act(ValueTypeId),
}

/// The variable `index` binders out, in the intuitionistic zone.
///
/// # Specification
/// trivial.
fn variable(
    scratch: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    scratch.value_variable(Zone::Intuitionistic, index)
}

/// `force(head) first second`: a closed combinator applied to two values.
///
/// # Specification
/// trivial.
fn applied(
    scratch: &mut CoreArena,
    head: ValueId,
    (first, second): (ValueId, ValueId),
) -> ComputationId
{
    let forced = scratch.computation_force(head);
    let once = scratch.computation_application(forced, first);
    scratch.computation_application(once, second)
}

/// Build `combinator` as a closed value of `scratch`.
///
/// # Specification
/// - requires: an [`Combinator::Act`] motive names a value type of `core`.
/// - ensures: a closed thunk of `scratch` computing the combinator, as the
///   module table states.
/// - provides: what the focusing focuses and applies to a flow's parts.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a motive naming no type
///   of `core` or an index overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a composite, a function flow and rides at the decode of
///   the binder, a product, a sum, a list and a run type run to the values the
///   kernel's rows compute.
/// - witness: `machine::tests::rides_run_by_the_motives_action`
/// - witness: `machine::tests::a_function_flow_runs_in_variance_order`
/// - witness: `machine::tests::a_flow_product_runs_componentwise`
#[spec(ensures: |ret| match ret {
    | Ok(id) => matches!(scratch.value(id), Some(&Value::Thunk(_))),
    | Err(_) => true,
})]
pub fn build(
    core: &CoreArena,
    combinator: Combinator,
    scratch: &mut CoreArena,
) -> Result<ValueId, FocusRefusal>
{
    match combinator {
        | Combinator::Identity => {
            let bound = variable(scratch, DeBruijnIndex::from(0_u32));
            let body = scratch.computation_return(bound);
            let lambda = scratch.computation_lambda(body);
            Ok(scratch.value_thunk(lambda))
        },
        | Combinator::Compose => Ok(compose(scratch)),
        | Combinator::Wrap => {
            // Under λd. λc. λg. λa': a' = 0, g = 1, c = 2, d = 3.
            let domain = variable(scratch, DeBruijnIndex::from(3_u32));
            let argument = variable(scratch, DeBruijnIndex::from(0_u32));
            let forced = scratch.computation_force(domain);
            let moved = scratch.computation_application(forced, argument);
            // Under a: a = 0, a' = 1, g = 2.
            let function = variable(scratch, DeBruijnIndex::from(2_u32));
            let argument = variable(scratch, DeBruijnIndex::from(0_u32));
            let forced = scratch.computation_force(function);
            let result = scratch.computation_application(forced, argument);
            // Under b: b = 0, a = 1, a' = 2, g = 3, c = 4.
            let codomain = variable(scratch, DeBruijnIndex::from(4_u32));
            let produced = variable(scratch, DeBruijnIndex::from(0_u32));
            let forced = scratch.computation_force(codomain);
            let onward = scratch.computation_application(forced, produced);
            let tail = scratch.computation_bind(result, onward);
            let body = scratch.computation_bind(moved, tail);
            let inner = scratch.computation_lambda(body);
            let wrapped = scratch.value_thunk(inner);
            let returned = scratch.computation_return(wrapped);
            let mut outer = returned;
            for _ in 0_u8 .. 3_u8 {
                outer = scratch.computation_lambda(outer);
            }
            Ok(scratch.value_thunk(outer))
        },
        | Combinator::Pair => {
            // Under λp. λq. λx: x = 0, q = 1, p = 2.
            let whole = variable(scratch, DeBruijnIndex::from(0_u32));
            let left = scratch
                .computation_tuple_projection(whole, gandr_kernel_term::Component::from(0_usize));
            // Under a: a = 0, x = 1.
            let whole = variable(scratch, DeBruijnIndex::from(1_u32));
            let right = scratch
                .computation_tuple_projection(whole, gandr_kernel_term::Component::from(1_usize));
            // Under b: b = 0, a = 1, x = 2, q = 3, p = 4.
            let first = variable(scratch, DeBruijnIndex::from(4_u32));
            let component = variable(scratch, DeBruijnIndex::from(1_u32));
            let moved_left = applied_once(scratch, first, component);
            // Under a': a' = 0, b = 1, a = 2, x = 3, q = 4.
            let second = variable(scratch, DeBruijnIndex::from(4_u32));
            let component = variable(scratch, DeBruijnIndex::from(1_u32));
            let moved_right = applied_once(scratch, second, component);
            // Under b': b' = 0, a' = 1.
            let first = variable(scratch, DeBruijnIndex::from(1_u32));
            let second = variable(scratch, DeBruijnIndex::from(0_u32));
            let pair = scratch.value_tuple(&[first, second]);
            let returned = scratch.computation_return(pair);
            let tail = scratch.computation_bind(moved_right, returned);
            let tail = scratch.computation_bind(moved_left, tail);
            let tail = scratch.computation_bind(right, tail);
            let mut body = scratch.computation_bind(left, tail);
            for _ in 0_u8 .. 3_u8 {
                body = scratch.computation_lambda(body);
            }
            Ok(scratch.value_thunk(body))
        },
        | Combinator::Act(motive) => act(core, motive, scratch),
    }
}

/// `force(head) argument`.
///
/// # Specification
/// trivial.
fn applied_once(
    scratch: &mut CoreArena,
    head: ValueId,
    argument: ValueId,
) -> ComputationId
{
    let forced = scratch.computation_force(head);
    scratch.computation_application(forced, argument)
}

/// `compose`, closed.
///
/// # Specification
/// trivial.
fn compose(scratch: &mut CoreArena) -> ValueId
{
    // Under λp. λq. λx: x = 0, q = 1, p = 2; under y, q = 2 again.
    let first = variable(scratch, DeBruijnIndex::from(2_u32));
    let argument = variable(scratch, DeBruijnIndex::from(0_u32));
    let forced = scratch.computation_force(first);
    let head = scratch.computation_application(forced, argument);
    let second = variable(scratch, DeBruijnIndex::from(2_u32));
    let middle = variable(scratch, DeBruijnIndex::from(0_u32));
    let forced = scratch.computation_force(second);
    let tail = scratch.computation_application(forced, middle);
    let mut body = scratch.computation_bind(head, tail);
    for _ in 0_u8 .. 3_u8 {
        body = scratch.computation_lambda(body);
    }
    scratch.value_thunk(body)
}

/// The action `thunk(λt. λv. M_P)` of the ride motive `motive`, built bottom
/// up over the motive's products, sums and lists so each part's action is a
/// closed value its parent applies.
///
/// # Specification
/// - requires: `motive` names a value type of `core`, under one binder.
/// - ensures: the module table's `act_P`; a node shared by two parts is built
///   once.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a dangling motive part
///   or an index overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — rides at the decode of the binder, through a pair, a sum
///   and a list, and at a run type run to the kernel rows' values.
/// - witness: `machine::tests::rides_run_by_the_motives_action`
#[spec(ensures: |ret| match ret {
    | Ok(id) => matches!(scratch.value(id), Some(&Value::Thunk(_))),
    | Err(_) => true,
})]
fn act(
    core: &CoreArena,
    motive: ValueTypeId,
    scratch: &mut CoreArena,
) -> Result<ValueId, FocusRefusal>
{
    let mut order = Vec::new();
    let mut pending = Vec::from([(motive, false)]);
    while let Some((node, expanded)) = pending.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        pending.push((node, true));
        match core.value_type(node) {
            | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                pending.extend(parts.iter().map(|&part| (part, false)));
            },
            | Some(&ValueType::List(element)) => pending.push((element, false)),
            | Some(_) => {},
            | None => return Err(FocusRefusal::TranslationInvariant),
        }
    }
    let mut built: BTreeMap<ValueTypeId, ValueId> = BTreeMap::new();
    for node in order {
        if built.contains_key(&node) {
            continue;
        }
        let body = action_body(core, node, &built, scratch)?;
        let inner = scratch.computation_lambda(body);
        let outer = scratch.computation_lambda(inner);
        let closed = scratch.value_thunk(outer);
        built.insert(node, closed);
    }
    built
        .get(&motive)
        .copied()
        .ok_or(FocusRefusal::TranslationInvariant)
}

/// `M_P` for one motive node, under `t` (index 1) and `v` (index 0), its
/// parts' actions already in `built`.
///
/// # Specification
/// - requires: every product, sum or list part of `node` has its action in
///   `built`.
/// - ensures: the row of the module table `node` falls under.
/// - fails: [`FocusRefusal::TranslationInvariant`] for a part without an
///   action, an annotation that does not import, or an index overflow.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each row runs to its kernel value.
/// - witness: `machine::tests::rides_run_by_the_motives_action`
#[spec(ensures: |ret| match ret {
    | Ok(id) => scratch.computation(id).is_some(),
    | Err(_) => true,
})]
fn action_body(
    core: &CoreArena,
    node: ValueTypeId,
    built: &BTreeMap<ValueTypeId, ValueId>,
    scratch: &mut CoreArena,
) -> Result<ComputationId, FocusRefusal>
{
    let part_action = |part: ValueTypeId| -> Result<ValueId, FocusRefusal> {
        built
            .get(&part)
            .copied()
            .ok_or(FocusRefusal::TranslationInvariant)
    };
    let translator = DeBruijnIndex::from(1_u32);
    let ridden = DeBruijnIndex::from(0_u32);
    match core.value_type(node) {
        | Some(&ValueType::Element { code, .. }) if matches!(core.value(code), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == DeBruijnIndex::from(0_u32)) =>
        {
            let translator = variable(scratch, translator);
            let ridden = variable(scratch, ridden);
            let forced = scratch.computation_force(translator);
            Ok(scratch.computation_application(forced, ridden))
        },
        | Some(&ValueType::Product(ref parts)) if !parts.is_empty() => {
            // Binders from the outermost: t, v, then x_i and y_i for each
            // component in order.
            let count = parts.len();
            let depth = count
                .checked_mul(2)
                .and_then(|pairs| pairs.checked_add(2))
                .ok_or(FocusRefusal::TranslationInvariant)?;
            // The index of the binder at `position` from the outermost, read
            // at `depth` binders.
            let index_at = |depth: usize, position: usize| {
                depth
                    .checked_sub(1)
                    .and_then(|outermost| outermost.checked_sub(position))
                    .and_then(|distance| u32::try_from(distance).ok())
                    .map(DeBruijnIndex::from)
                    .ok_or(FocusRefusal::TranslationInvariant)
            };
            let mut components = Vec::with_capacity(count);
            for position in 0 .. count {
                let at = position
                    .checked_mul(2)
                    .and_then(|offset| offset.checked_add(3))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                components.push(variable(scratch, index_at(depth, at)?));
            }
            let tuple = scratch.value_tuple(&components);
            let mut body = scratch.computation_return(tuple);
            for (position, &part) in parts.iter().enumerate().rev() {
                let action = part_action(part)?;
                let entry = position
                    .checked_mul(2)
                    .and_then(|offset| offset.checked_add(2))
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let inside = entry
                    .checked_add(1)
                    .ok_or(FocusRefusal::TranslationInvariant)?;
                let translator = variable(scratch, index_at(inside, 0)?);
                let component = variable(scratch, DeBruijnIndex::from(0_u32));
                let moved = applied(scratch, action, (translator, component));
                body = scratch.computation_bind(moved, body);
                let whole = variable(scratch, index_at(entry, 1)?);
                let projected = scratch.computation_tuple_projection(
                    whole,
                    gandr_kernel_term::Component::from(position),
                );
                body = scratch.computation_bind(projected, body);
            }
            Ok(body)
        },
        | Some(&ValueType::Sum(ref parts)) => {
            // Each branch binds its payload: z = 0, v = 1, t = 2.
            let mut branches = Vec::with_capacity(parts.len());
            for (position, &part) in parts.iter().enumerate() {
                let action = part_action(part)?;
                let translator = variable(scratch, DeBruijnIndex::from(2_u32));
                let payload = variable(scratch, DeBruijnIndex::from(0_u32));
                let moved = applied(scratch, action, (translator, payload));
                let result = variable(scratch, DeBruijnIndex::from(0_u32));
                let injected =
                    scratch.value_injection(gandr_kernel_term::Summand::from(position), result);
                let returned = scratch.computation_return(injected);
                branches.push(scratch.computation_bind(moved, returned));
            }
            let scrutinee = variable(scratch, ridden);
            Ok(scratch.computation_case(scrutinee, &branches))
        },
        | Some(&ValueType::List(element)) => {
            let action = part_action(element)?;
            let (element, result) = {
                let mut importer = gandr_core_term::TypeImporter::new(core, scratch);
                let element = importer
                    .value_type(element)
                    .map_err(|gandr_core_term::ImportFault| FocusRefusal::TranslationInvariant)?;
                let result = importer
                    .value_type(node)
                    .map_err(|gandr_core_term::ImportFault| FocusRefusal::TranslationInvariant)?;
                (element, result)
            };
            let nil = scratch.value_list_nil();
            let on_nil = scratch.computation_return(nil);
            // The cell branch binds the head, then the folded tail: tail = 0,
            // head = 1, v = 2, t = 3; under the element's result y, tail = 1.
            let translator = variable(scratch, DeBruijnIndex::from(3_u32));
            let head = variable(scratch, DeBruijnIndex::from(1_u32));
            let moved = applied(scratch, action, (translator, head));
            let first = variable(scratch, DeBruijnIndex::from(0_u32));
            let rest = variable(scratch, DeBruijnIndex::from(1_u32));
            let cell = scratch.value_list_cons(first, rest);
            let returned = scratch.computation_return(cell);
            let on_cons = scratch.computation_bind(moved, returned);
            let list = variable(scratch, ridden);
            Ok(scratch.computation_list_fold(element, result, list, on_nil, on_cons))
        },
        | Some(&ValueType::Flow { target, .. }) if matches!(core.value(target), Some(&Value::Variable { zone: Zone::Intuitionistic, index }) if index == DeBruijnIndex::from(0_u32)) =>
        {
            let composer = compose(scratch);
            let ridden = variable(scratch, ridden);
            let translator = variable(scratch, translator);
            let composite = applied(scratch, composer, (ridden, translator));
            let suspended = scratch.value_thunk(composite);
            Ok(scratch.computation_return(suspended))
        },
        | Some(_) => {
            let ridden = variable(scratch, ridden);
            Ok(scratch.computation_return(ridden))
        },
        | None => Err(FocusRefusal::TranslationInvariant),
    }
}
