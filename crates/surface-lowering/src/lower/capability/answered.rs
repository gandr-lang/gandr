//! A capability scope a model answers, `handle c : T with sort x = A { M }
//! with N`: each operation's clause hands the operation to `N`'s component of
//! its name, and the scope answers `N`'s carrier.
//!
//! A theory's operation `op : (p : P, k : K) --> C` is, in a model, the
//! component `op : P -> K -> -F C`: its port `K` is the carrier where it binds
//! nothing, and the thunked function `+U ((x : R) -> -F C)` where it binds
//! `x : R`. The clause for `op` applies the component, forced, to the payload
//! and then to the continuation: the continuation run at unit and its answer
//! passed, for a port binding nothing; the function resuming the continuation
//! with the values it binds, for a binding port. The return clause returns the
//! subject's result at the carrier, so the subject computes a value of it.
//! Each component a clause applies is ascribed its type, every sort read as
//! the manifest's type or the module's, so the checker reads the module's
//! members at the theory's signature. The scope owes no law: the module's
//! ascription to the theory's model type states each one.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::TheoryInterface;
use super::theory::TheoryOperation;
use crate::lower::Lowerer;
use crate::lower::Sink;
use crate::lower::lowered;
use crate::lower::model::ComponentPlace;
use crate::lower::model::ModelSlot;
use crate::lower::model::Supplied;
use crate::origin::Origin;

/// The model answering a capability scope over a theory: the theory's slot,
/// the sorts the scope's manifest fixes left out, and what the module the
/// scope names passes for it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lower) struct Answering
{
    /// The theory's slot.
    pub slot: ModelSlot,
    /// The module's members.
    pub supplied: Supplied,
}

impl Lowerer<'_, '_>
{
    /// The return clause and the operation clauses of the scope over `theory`
    /// that `answering` answers.
    ///
    /// # Specification
    /// - requires: `answering` was read for the scope over `theory`, and the
    ///   types its manifest writes are minted.
    /// - ensures: the return clause, returning its result at the carrier the
    ///   module gives; one clause per operation of `theory`, in its order, as
    ///   [`clause`] mints it for the module's component of its name, ascribed
    ///   the component's type; every node carrying `origin`; nothing when a
    ///   component, its type or a manifest's type did not lower.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope over `State` naming a state-passing module
    ///   runs as the clauses written out run.
    /// - witness: `lower::capability::tests::a_scope_names_a_model_of_its_theory_2272`
    #[spec(ensures: |ret| match ret {
        | Maybe::Present((_, ref clauses)) => clauses.len() == theory.operations.len(),
        | Maybe::Absent(_) => true,
    })]
    pub(in crate::lower) fn mint_answered(
        &self,
        theory: &TheoryInterface,
        answering: &Answering,
        sink: &mut Sink<'_>,
        origin: Origin,
    ) -> Maybe<(ComputationId, Vec<EffectClause>), lowered::Absent>
    {
        let unminted = Maybe::Absent(lowered::Absent::Unminted);
        let slot = &answering.slot;
        let (carrier, answer) = match self.supplied_carrier(slot, &answering.supplied, sink, origin)
        {
            Maybe::Present(carrier) => carrier,
            Maybe::Absent(reason) => return Maybe::Absent(reason),
        };
        let mut sorts: Vec<(&Name, ValueTypeId)> =
            Vec::with_capacity(slot.fixed().len().saturating_add(1));
        for (name, stated) in slot.fixed() {
            match self.value_type_at(stated.node) {
                Maybe::Present(ty) => sorts.push((name, ty)),
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            }
        }
        sorts.push((&carrier, answer));
        let result = variable(sink, DeBruijnIndex::from(0_u32), origin);
        let returned = sink.arena.computation_return(result);
        sink.origins.record_computation(returned, origin);
        let answer = raised_type(sink, answer, Binders::from(1_u32), origin);
        let returner = sink.arena.comp_type_returner(answer);
        sink.origins.record_comp_type(returner, origin);
        let on_return = sink.arena.computation_ascribe(returned, returner);
        sink.origins.record_computation(on_return, origin);
        let components = slot.components();
        // Each component's place by its name, read once for every operation.
        let places: BTreeMap<&str, ComponentPlace> = components
            .iter()
            .enumerate()
            .map(|(place, component)| (component.name.as_ref(), ComponentPlace::from(place)))
            .collect();
        let mut clauses = Vec::with_capacity(theory.operations.len());
        for operation in &theory.operations {
            let Some(&place) = places.get(operation.name.as_ref())
            else {
                return unminted;
            };
            let member =
                match self.mint_supplied(&answering.supplied, place, Binders::NONE, sink, origin) {
                    Maybe::Present(member) => member,
                    Maybe::Absent(reason) => return Maybe::Absent(reason),
                };
            let ty = match self.operation_domain(slot, place, &sorts, sink, origin) {
                Maybe::Present(ty) => ty,
                Maybe::Absent(reason) => return Maybe::Absent(reason),
            };
            let head = sink.arena.value_ascribe(member, ty);
            sink.origins.record_value(head, origin);
            clauses.push(EffectClause {
                operation: operation.name.clone(),
                body: clause(sink, head, operation, origin),
            });
        }

        Maybe::Present((on_return, clauses))
    }
}

/// The body of the clause for `operation`, sending its payload's values and
/// binding its reply's at its port, under the clause's payload and
/// continuation binders: `head`, the model's component standing at the scope,
/// raised past the binders the body opens, forced and applied to each payload
/// value, then to the continuation as the component's port takes it.
///
/// # Specification
/// - requires: `head` stands at the scope, outside the clause's binders.
/// - ensures: the payload binder's value passed as itself for one payload
///   value, and split into each for several; then, for a port binding nothing,
///   the continuation resumed at unit, its answer bound and passed; for a port
///   binding values, the thunk of the function over them resuming the
///   continuation with them, one as itself and several as their tuple, passed;
///   every node carrying `origin`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `State`'s `get` binds the state at its port and `put`
///   sends one and binds nothing; a clause misplacing either runs to another
///   value.
/// - witness: `lower::capability::tests::a_scope_names_a_model_of_its_theory_2272`
#[spec(ensures: |ret| sink.arena.computation(ret).is_some())]
fn clause(
    sink: &mut Sink<'_>,
    head: ValueId,
    operation: &TheoryOperation,
    origin: Origin,
) -> ComputationId
{
    let at = |index: usize| DeBruijnIndex::from(u32::try_from(index).unwrap_or(u32::MAX));
    let payload = operation.payload.len();
    let reply = operation.reply.len();
    // The payload's values, split off its binder when there are several.
    let split = if payload > 1 { payload } else { 0 };
    // The continuation's answer, bound when the port binds nothing.
    let bound = usize::from(reply == 0);
    let opened = 2_usize.saturating_add(split).saturating_add(bound);
    let raised = raised_value(
        sink,
        head,
        Binders::from(u32::try_from(opened).unwrap_or(u32::MAX)),
        origin,
    );
    let mut applied = sink.arena.computation_force(raised);
    sink.origins.record_computation(applied, origin);
    let sent: Vec<DeBruijnIndex> = match payload {
        0 => Vec::new(),
        1 => Vec::from([at(1_usize.saturating_add(bound))]),
        _ => (0 .. payload)
            .map(|place| {
                at(split
                    .saturating_sub(1)
                    .saturating_sub(place)
                    .saturating_add(bound))
            })
            .collect(),
    };
    for index in sent {
        let argument = variable(sink, index, origin);
        applied = sink.arena.computation_application(applied, argument);
        sink.origins.record_computation(applied, origin);
    }
    let continued = if reply == 0 {
        variable(sink, at(0), origin)
    }
    else {
        let replied = if reply == 1 {
            variable(sink, at(0), origin)
        }
        else {
            let values: Vec<ValueId> = (0 .. reply)
                .map(|place| {
                    variable(
                        sink,
                        at(reply.saturating_sub(1).saturating_sub(place)),
                        origin,
                    )
                })
                .collect();
            let id = sink.arena.value_tuple(&values);
            sink.origins.record_value(id, origin);
            id
        };
        let mut resumed = resume(sink, at(split.saturating_add(reply)), replied, origin);
        for _ in 0 .. reply {
            resumed = sink.arena.computation_lambda(resumed);
            sink.origins.record_computation(resumed, origin);
        }
        let id = sink.arena.value_thunk(resumed);
        sink.origins.record_value(id, origin);
        id
    };
    applied = sink.arena.computation_application(applied, continued);
    sink.origins.record_computation(applied, origin);
    let mut body = applied;
    if reply == 0 {
        let unit = sink.arena.value_unit();
        sink.origins.record_value(unit, origin);
        let resumed = resume(sink, at(split), unit, origin);
        body = sink.arena.computation_bind(resumed, body);
        sink.origins.record_computation(body, origin);
    }
    if split > 0 {
        let held = variable(sink, at(1), origin);
        body = sink
            .arena
            .computation_split(held, ComponentCount::from(payload), body);
        sink.origins.record_computation(body, origin);
    }

    body
}

/// The continuation at `index` resumed with `reply` returned.
///
/// # Specification
/// trivial.
fn resume(
    sink: &mut Sink<'_>,
    index: DeBruijnIndex,
    reply: ValueId,
    origin: Origin,
) -> ComputationId
{
    let continuation = variable(sink, index, origin);
    let returned = sink.arena.computation_return(reply);
    sink.origins.record_computation(returned, origin);
    let id = sink.arena.computation_resume(continuation, returned);
    sink.origins.record_computation(id, origin);
    id
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    sink: &mut Sink<'_>,
    index: DeBruijnIndex,
    origin: Origin,
) -> ValueId
{
    let id = sink.arena.value_variable(Zone::Intuitionistic, index);
    sink.origins.record_value(id, origin);
    id
}

/// `value` raised past `under` binders, the raised node carrying `origin`
/// when the raise minted one.
///
/// # Specification
/// trivial.
fn raised_value(
    sink: &mut Sink<'_>,
    value: ValueId,
    under: Binders,
    origin: Origin,
) -> ValueId
{
    let raised = gandr_core_term::shift_value(sink.arena, value, under).settle(sink.arena);
    if raised != value {
        sink.origins.record_value(raised, origin);
    }
    raised
}

/// `ty` raised past `under` binders, the raised node carrying `origin` when
/// the raise minted one.
///
/// # Specification
/// trivial.
fn raised_type(
    sink: &mut Sink<'_>,
    ty: ValueTypeId,
    under: Binders,
    origin: Origin,
) -> ValueTypeId
{
    let raised = gandr_core_term::shift_value_type(sink.arena, ty, under).settle(sink.arena);
    if raised != ty {
        sink.origins.record_value_type(raised, origin);
    }
    raised
}
