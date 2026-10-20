//! First-class stacks, deep handlers and delimited control.
//!
//! A literal stack is a flat sequence in observation order. A bind frame binds
//! one intuitionistic value in its body, never in later frames. Handler clauses
//! bind the payload followed by the resumption, so index zero is the
//! resumption.

use alloc::sync::Arc;

use anodized::spec;

use crate::CompType;
use crate::CompTypeId;
use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::Value;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;
use crate::effect::EffectSig;
use crate::effect::OperationName;

/// One observation in a first-class stack literal.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StackFrame<V = ValueId, C = ComputationId>
{
    /// Supply an argument to a negative function.
    Apply(V),
    /// Bind a returned value over a computation, then continue with the next
    /// frame.
    Bind(C),
    /// Select the component of a negative product at a position.
    Project(crate::Component),
}

/// One operation clause, with payload and resumption bound in that order.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EffectClause<C = ComputationId>
{
    /// The operation answered by the clause.
    pub operation: OperationName,
    /// The clause body beneath two intuitionistic binders.
    pub body: C,
}

/// Runtime control formers outside the pure certificate language.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ControlFormer
{
    /// A first-class stack literal.
    Reify,
    /// An operation request.
    Perform,
    /// A deep effect handler.
    Handle,
    /// Application of a first-class stack.
    Resume,
    /// A delimited-control boundary.
    Reset,
    /// Capture of the continuation up to a reset.
    Shift,
    /// Introduction of a lazy computation pair.
    With,
    /// Observation of a lazy computation pair.
    Project,
    /// An operation exercised through a capability.
    Exercise,
    /// A deep handler introducing the capability its body exercises.
    Scope,
}

impl CoreArena
{
    /// Mint a literal stack over existing value and computation children.
    ///
    /// # Specification
    /// - requires: every frame child resolves in this arena.
    /// - ensures: preserves observation order and the bind frame's local scope.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — argument, bind and projection frames distinguish
    ///   order and scope.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(requires: frames.iter().all(|frame| match *frame { StackFrame::Apply(value) => self.value(value).is_some(), StackFrame::Bind(body) => self.computation(body).is_some(), StackFrame::Project(_) => true }), ensures: |ret| matches!(self.value(ret), Some(Value::Reify(_))))]
    #[inline]
    pub fn value_reify(
        &mut self,
        frames: Arc<[StackFrame]>,
    ) -> ValueId
    {
        self.alloc_value(Value::Reify(frames))
    }

    /// Mint the type of a stack consuming `input` and delivering `output`.
    ///
    /// # Specification
    /// - requires: both computation types resolve in this arena.
    /// - ensures: preserves the distinct input and output roles.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal input and output types, each rebuilt at its
    ///   own index, distinguish reversal.
    /// - witness: `control::tests::stack_types_rebuild_both_computation_children`
    #[spec(requires: self.comp_type(input).is_some() && self.comp_type(output).is_some(), ensures: |ret| self.value_type(ret) == Some(&ValueType::Stack { input, output }))]
    #[inline]
    pub fn value_type_stack(
        &mut self,
        input: CompTypeId,
        output: CompTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Stack { input, output })
    }

    /// Mint an operation request; checking resolves its name and payload type.
    ///
    /// # Specification
    /// - requires: the payload and every signature type resolve in this arena.
    /// - ensures: records the interface rather than consulting an ambient
    ///   registry.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substituting through a request rewrites its payload
    ///   and its interface's operation types together; a dropped or swapped
    ///   edge changes the observed payload or operation type.
    /// - witness: `control::tests::effect_interfaces_and_clauses_rewrite_in_their_own_scopes`
    #[spec(requires: self.value(payload).is_some() && signature.types().all(|ty| self.value_type(ty).is_some()), ensures: |ret| matches!(self.computation(ret), Some(Computation::Perform { .. })))]
    #[inline]
    pub fn computation_perform(
        &mut self,
        signature: EffectSig,
        operation: OperationName,
        payload: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Perform {
            signature,
            operation,
            payload,
        })
    }

    /// Mint a deep handler with its return and operation clauses.
    ///
    /// # Specification
    /// - requires: all computation children and interface types resolve.
    /// - ensures: preserves the subject and clause scopes; coverage is a typing
    ///   premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substituting through a handler distinguishes the
    ///   subject, return and clause scopes: each sees the replacement at its
    ///   own depth.
    /// - witness: `control::tests::effect_interfaces_and_clauses_rewrite_in_their_own_scopes`
    #[spec(requires: self.computation(subject).is_some() && self.computation(on_return).is_some() && clauses.iter().all(|clause| self.computation(clause.body).is_some()) && signature.types().all(|ty| self.value_type(ty).is_some()), ensures: |ret| matches!(self.computation(ret), Some(Computation::Handle { .. })))]
    #[inline]
    pub fn computation_handle(
        &mut self,
        signature: EffectSig,
        subject: ComputationId,
        on_return: ComputationId,
        clauses: Arc<[EffectClause]>,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Handle {
            signature,
            subject,
            on_return,
            clauses,
        })
    }

    /// Mint an operation exercised through a capability.
    ///
    /// # Specification
    /// - requires: the capability, the payload and every signature type resolve
    ///   in this arena.
    /// - ensures: records the interface inline and keeps the capability and
    ///   payload in their distinct roles; whether the capability's authority
    ///   grants the operation is a typing premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substituting through an exercise under a scope's
    ///   binder rewrites its capability and payload at their own depth, and a
    ///   swapped pair reads back different.
    /// - witness: `control::tests::a_capability_scope_binds_its_subject_once`
    #[spec(requires: self.value(capability).is_some() && self.value(payload).is_some() && signature.types().all(|ty| self.value_type(ty).is_some()), ensures: |ret| matches!(self.computation(ret), Some(Computation::Exercise { .. })))]
    #[inline]
    pub fn computation_exercise(
        &mut self,
        capability: ValueId,
        signature: EffectSig,
        operation: OperationName,
        payload: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Exercise {
            capability,
            signature,
            operation,
            payload,
        })
    }

    /// Mint a deep handler whose subject receives the capability it
    /// introduces.
    ///
    /// # Specification
    /// - requires: all computation children and interface types resolve.
    /// - ensures: the subject stands under one binder, the capability; the
    ///   return and clause scopes are a handler's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substituting through a scope sees the replacement one
    ///   binder deeper in the subject and the return clause and two deeper in
    ///   an operation clause, each asserted at its exact index.
    /// - witness: `control::tests::a_capability_scope_binds_its_subject_once`
    #[spec(requires: self.computation(subject).is_some() && self.computation(on_return).is_some() && clauses.iter().all(|clause| self.computation(clause.body).is_some()) && signature.types().all(|ty| self.value_type(ty).is_some()), ensures: |ret| matches!(self.computation(ret), Some(Computation::Scope { .. })))]
    #[inline]
    pub fn computation_scope(
        &mut self,
        signature: EffectSig,
        subject: ComputationId,
        on_return: ComputationId,
        clauses: Arc<[EffectClause]>,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Scope {
            signature,
            subject,
            on_return,
            clauses,
        })
    }

    /// Feed a computation to a stack value.
    ///
    /// # Specification
    /// - requires: both children resolve.
    /// - ensures: keeps the stack and fed computation in their distinct roles.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — substitution through a resumption under a shift
    ///   binder, compared with an independently built term, distinguishes the
    ///   stack from the fed computation.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(requires: self.value(stack).is_some() && self.computation(body).is_some(), ensures: |ret| self.computation(ret) == Some(&Computation::Resume(stack, body)))]
    #[inline]
    pub fn computation_resume(
        &mut self,
        stack: ValueId,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Resume(stack, body))
    }

    /// Delimit captures in `body` without introducing a value binder.
    ///
    /// # Specification
    /// - requires: the body resolves.
    /// - ensures: retains the delimiter as a distinct control former.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reset around a shift, rewritten and compared with
    ///   an independently built term, keeps the delimiter distinct from its
    ///   body.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(requires: self.computation(body).is_some(), ensures: |ret| self.computation(ret) == Some(&Computation::Reset(body)))]
    #[inline]
    pub fn computation_reset(
        &mut self,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Reset(body))
    }

    /// Capture the nearest reset's continuation under one stack binder.
    ///
    /// # Specification
    /// - requires: the body resolves under its intuitionistic binder.
    /// - ensures: retains the capture rather than executing or erasing it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — capture followed by resumption distinguishes the
    ///   local stack binder from outer variables.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(requires: self.computation(body).is_some(), ensures: |ret| self.computation(ret) == Some(&Computation::Shift(body)))]
    #[inline]
    pub fn computation_shift(
        &mut self,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Shift(body))
    }

    /// Pair computations lazily: an observation runs exactly one component.
    ///
    /// # Specification
    /// - requires: every component resolves.
    /// - ensures: preserves the ordered components without running any.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reordered tuple and a substitution that reaches
    ///   only the first component distinguish component order.
    /// - witness: `control::tests::lazy_tuples_keep_their_components_and_projection_position`
    #[spec(requires: components.iter().all(|component| self.computation(*component).is_some()), ensures: |ret| matches!(self.computation(ret), Some(&Computation::With(ref stored)) if **stored == *components))]
    #[inline]
    pub fn computation_with(
        &mut self,
        components: &[ComputationId],
    ) -> ComputationId
    {
        self.alloc_computation(Computation::With(components.into()))
    }

    /// Observe the component of a negative product at a position.
    ///
    /// # Specification
    /// - requires: the subject resolves.
    /// - ensures: retains the chosen component.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct positions and a reordered tuple distinguish
    ///   the chosen component.
    /// - witness: `control::tests::lazy_tuples_keep_their_components_and_projection_position`
    #[spec(requires: self.computation(subject).is_some(), ensures: |ret| self.computation(ret) == Some(&Computation::Project(component, subject)))]
    #[inline]
    pub fn computation_project(
        &mut self,
        component: crate::Component,
        subject: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Project(component, subject))
    }

    /// Form a negative product whose components share the ambient scope.
    ///
    /// # Specification
    /// - requires: every component type resolves.
    /// - ensures: preserves the ordered computation types.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stack projection must consume a negative product,
    ///   not a returner of a positive pair.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(requires: components.iter().all(|component| self.comp_type(*component).is_some()), ensures: |ret| matches!(self.comp_type(ret), Some(&CompType::With(ref stored)) if **stored == *components))]
    #[inline]
    pub fn comp_type_with(
        &mut self,
        components: &[CompTypeId],
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::With(components.into()))
    }
}

#[cfg(test)]
mod tests;
