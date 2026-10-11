//! First-class stacks, deep handlers and delimited control.
//!
//! A literal stack is a flat sequence in observation order. A bind frame binds
//! one intuitionistic value in its body, never in later frames. Handler clauses
//! bind the payload followed by the resumption, so index zero is the
//! resumption.

use alloc::sync::Arc;

use anodized::spec;
use gandr_kernel_term::Side;

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
    /// Select a component of a negative product.
    Project(Side),
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
    /// - requires: both components resolve.
    /// - ensures: preserves the ordered components without running either.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a flipped pair and a substitution that reaches only
    ///   the first component distinguish component order.
    /// - witness: `control::tests::lazy_pairs_keep_their_components_and_projection_side`
    #[spec(requires: self.computation(first).is_some() && self.computation(second).is_some(), ensures: |ret| self.computation(ret) == Some(&Computation::With(first, second)))]
    #[inline]
    pub fn computation_with(
        &mut self,
        first: ComputationId,
        second: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::With(first, second))
    }

    /// Observe one component of a negative pair.
    ///
    /// # Specification
    /// - requires: the subject resolves.
    /// - ensures: retains the chosen side.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — opposite sides and a flipped pair distinguish the
    ///   chosen side.
    /// - witness: `control::tests::lazy_pairs_keep_their_components_and_projection_side`
    #[spec(requires: self.computation(subject).is_some(), ensures: |ret| self.computation(ret) == Some(&Computation::Project(side, subject)))]
    #[inline]
    pub fn computation_project(
        &mut self,
        side: Side,
        subject: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Project(side, subject))
    }

    /// Form a negative product whose components share the ambient scope.
    ///
    /// # Specification
    /// - requires: both component types resolve.
    /// - ensures: preserves the ordered computation types.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stack projection must consume a negative product,
    ///   not a returner of a positive pair.
    /// - witness: `control::tests::stack_literals_preserve_binder_scope`
    #[spec(requires: self.comp_type(first).is_some() && self.comp_type(second).is_some(), ensures: |ret| self.comp_type(ret) == Some(&CompType::With(first, second)))]
    #[inline]
    pub fn comp_type_with(
        &mut self,
        first: CompTypeId,
        second: CompTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::With(first, second))
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::DeBruijnIndex;

    use super::*;
    use crate::CertificateEquality;
    use crate::TypeImporter;
    use crate::Zone;
    use crate::effect::EffectName;
    use crate::effect::EffectOp;
    use crate::effect::EffectRow;
    use crate::equal_certificate_syntax;
    use crate::instantiate_value;

    #[test]
    fn stack_literals_preserve_binder_scope()
    {
        let mut arena = CoreArena::new();
        let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let beneath = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let pair = arena.value_pair(outer, beneath);
        let bound_body = arena.computation_return(pair);
        let stack = arena.value_reify(Arc::from([
            StackFrame::Apply(outer),
            StackFrame::Bind(bound_body),
            StackFrame::Project(Side::Left),
        ]));
        let unit = arena.value_unit();
        let rewritten = instantiate_value(&mut arena, stack, unit);
        let Value::Reify(ref frames) = *arena.value(rewritten).unwrap()
        else {
            panic!("stack literal")
        };
        let [
            StackFrame::Apply(actual),
            StackFrame::Bind(body),
            StackFrame::Project(side),
        ] = *frames.as_ref()
        else {
            panic!("flat stack frames")
        };
        assert_eq!(actual, unit);
        assert_eq!(side, Side::Left);
        let Computation::Return(pair) = *arena.computation(body).unwrap()
        else {
            panic!("return")
        };
        assert_eq!(arena.value(pair), Some(&Value::Pair(outer, unit)));
        let fed = arena.computation_return(beneath);
        let resumed = arena.computation_resume(outer, fed);
        let shifted = arena.computation_shift(resumed);
        let reset = arena.computation_reset(shifted);
        let thunk = arena.value_thunk(reset);
        let rewritten = instantiate_value(&mut arena, thunk, unit);
        let expected_fed = arena.computation_return(unit);
        let expected_resume = arena.computation_resume(outer, expected_fed);
        let expected_shift = arena.computation_shift(expected_resume);
        let expected_reset = arena.computation_reset(expected_shift);
        let expected = arena.value_thunk(expected_reset);
        assert_eq!(
            equal_certificate_syntax(&arena, rewritten, expected),
            CertificateEquality::Equal
        );
        assert_eq!(
            equal_certificate_syntax(&arena, thunk, expected),
            CertificateEquality::Different
        );
    }

    /// The index the code of a returner's element type names.
    ///
    /// # Specification
    /// trivial.
    fn returned_code(
        arena: &CoreArena,
        returner: CompTypeId,
    ) -> Option<DeBruijnIndex>
    {
        let &CompType::Returner { result, .. } = arena.comp_type(returner)?
        else {
            return None;
        };
        let &ValueType::Element { code, .. } = arena.value_type(result)?
        else {
            return None;
        };
        let &Value::Variable { index, .. } = arena.value(code)?
        else {
            return None;
        };
        Some(index)
    }

    #[test]
    fn stack_types_rebuild_both_computation_children()
    {
        let mut arena = CoreArena::new();
        let local = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let ambient = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
        let local_type = arena.value_type_element(local, Level::zero());
        let ambient_type = arena.value_type_element(ambient, Level::zero());
        let consumes = arena.comp_type_returner(local_type);
        let delivers = arena.comp_type_returner(ambient_type);
        let stack = arena.value_type_stack(consumes, delivers);
        assert_eq!(
            arena.value_type(stack),
            Some(&ValueType::Stack {
                input: consumes,
                output: delivers,
            })
        );
        let rewritten = crate::instantiate_value_type(&mut arena, stack, argument);
        let Some(&ValueType::Stack { input, output }) = arena.value_type(rewritten)
        else {
            panic!("a stack type stays a stack type")
        };
        assert_eq!(
            returned_code(&arena, input),
            Some(DeBruijnIndex::from(3_u32))
        );
        assert_eq!(
            returned_code(&arena, output),
            Some(DeBruijnIndex::from(0_u32))
        );
    }

    #[test]
    fn lazy_pairs_keep_their_components_and_projection_side()
    {
        let mut arena = CoreArena::new();
        let free = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let unit = arena.value_unit();
        let first = arena.computation_return(free);
        let second = arena.computation_return(unit);
        let pair = arena.computation_with(first, second);
        let left = arena.computation_project(Side::Left, pair);
        let right = arena.computation_project(Side::Right, pair);
        assert_eq!(
            arena.computation(pair),
            Some(&Computation::With(first, second))
        );
        assert_eq!(
            arena.computation(left),
            Some(&Computation::Project(Side::Left, pair))
        );
        let flipped = arena.computation_with(second, first);
        let flipped_left = arena.computation_project(Side::Left, flipped);
        let observed_left = arena.value_thunk(left);
        let observed_right = arena.value_thunk(right);
        let observed_flipped = arena.value_thunk(flipped_left);
        for other in [observed_right, observed_flipped] {
            assert_eq!(
                equal_certificate_syntax(&arena, observed_left, other),
                CertificateEquality::Different
            );
        }
        let replacement = arena.value_unit();
        let rewritten = instantiate_value(&mut arena, observed_left, replacement);
        let expected_first = arena.computation_return(replacement);
        let expected_pair = arena.computation_with(expected_first, second);
        let expected_left = arena.computation_project(Side::Left, expected_pair);
        let expected = arena.value_thunk(expected_left);
        assert_eq!(
            equal_certificate_syntax(&arena, rewritten, expected),
            CertificateEquality::Equal
        );
    }

    #[test]
    fn effect_interfaces_and_clauses_rewrite_in_their_own_scopes()
    {
        let mut arena = CoreArena::new();
        let variable = |arena: &mut CoreArena, index| {
            arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
        };
        let free = variable(&mut arena, 0_u32);
        let under_one = variable(&mut arena, 1_u32);
        let under_two = variable(&mut arena, 2_u32);
        let element = arena.value_type_element(free, gandr_kernel_strata::Level::zero());
        let reply = arena.value_type_list(element);
        let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: "ask".into(),
            payload: element,
            reply,
        }])
        .unwrap();
        let performed = arena.computation_perform(signature.clone(), "ask".into(), free);
        let returned = arena.computation_return(under_one);
        let pair = arena.value_pair(free, under_two);
        let clause = arena.computation_return(pair);
        let handled = arena.computation_handle(
            signature,
            performed,
            returned,
            Arc::from([EffectClause {
                operation: "ask".into(),
                body: clause,
            }]),
        );
        let thunk = arena.value_thunk(handled);
        let string = arena.value_type_base(BaseType::String);
        let quote = arena.value_quote(string);
        let rewritten = instantiate_value(&mut arena, thunk, quote);
        let Value::Thunk(body) = *arena.value(rewritten).unwrap()
        else {
            panic!("thunk")
        };
        let Computation::Handle {
            ref signature,
            subject,
            on_return,
            ref clauses,
        } = *arena.computation(body).unwrap()
        else {
            panic!("handler")
        };
        let operation = signature.operations().next().unwrap();
        assert_eq!(operation.payload, string);
        assert_eq!(
            arena.value_type(operation.reply),
            Some(&ValueType::List(string))
        );
        assert_eq!(
            arena.computation(on_return),
            Some(&Computation::Return(quote))
        );
        let Computation::Perform {
            ref signature,
            payload,
            ..
        } = *arena.computation(subject).unwrap()
        else {
            panic!("perform")
        };
        assert_eq!(payload, quote);
        assert_eq!(signature.operations().next().unwrap().payload, string);
        let Computation::Return(pair) = *arena.computation(clauses[0].body).unwrap()
        else {
            panic!("clause")
        };
        assert_eq!(arena.value(pair), Some(&Value::Pair(free, quote)));
    }

    #[test]
    fn effect_and_stack_annotations_import_without_foreign_handles()
    {
        let build = |arena: &mut CoreArena| {
            let unit = arena.value_type_unit();
            let strings = arena.value_type_base(BaseType::String);
            let list = arena.value_type_list(strings);
            let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
                name: "ask".into(),
                payload: unit,
                reply: list,
            }])
            .unwrap();
            let input =
                arena.comp_type_returner_with_effects(list, EffectRow::singleton(signature));
            let pure = arena.comp_type_returner(unit);
            let output = arena.comp_type_with(pure, input);
            arena.value_type_stack(input, output)
        };
        let mut source = CoreArena::new();
        let root = build(&mut source);
        let mut target = CoreArena::new();
        for _ in 0_u32 .. 17_u32 {
            let _ = target.value_type_unit();
        }
        let imported = TypeImporter::new(&source, &mut target)
            .value_type(root)
            .unwrap();
        let expected = build(&mut target);
        let imported = target.value_quote(imported);
        let expected = target.value_quote(expected);
        assert_eq!(
            equal_certificate_syntax(&target, imported, expected),
            CertificateEquality::Equal
        );
    }
}
