//! The children of a core node, in order, each with the binders it stands
//! under.
//!
//! A former's scoping is stated here once: which children a node holds, in
//! which order, and how many binders of each zone the former opens over each.
//! The intuitionistic binders are the ones the rewrite machines count per
//! child. The linear ones are a fork's two ends, a receive's payload and a
//! hold's or an access's view. The arena folds a node's support over its
//! children when it mints the node, and a walk that descends a term reads the
//! children here rather than restating the formers.
//!
//! A node's own names are not children: a variable's index, a session
//! action's endpoint and a memory form's resident are what the node names
//! itself. A primitive's generated body is closed and stands as a leaf, as the
//! rewrites read it.
//!
//! # Items
//!
//! - [`Visit`]: what a walk does with each child, one method per family.
//! - [`of_value`], [`of_computation`], [`of_value_type`] and [`of_comp_type`]:
//!   a node's children, in order, each handed to a [`Visit`] with its
//!   [`Crossing`].

use quenchant_shape::shape::Maybe;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::context::BinderDepth;
use crate::control::StackFrame;
use crate::rewrite::Binders;
use crate::support::Crossing;
use crate::syntax::CompType;
use crate::syntax::Computation;
use crate::syntax::SplitMotive;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

/// What a walk does with each child of a node, one method per family.
///
/// Each method receives the child and the binders of each zone that the
/// parent's former opens over it.
pub trait Visit
{
    /// A value child, standing under `crossing`.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        child: ValueId,
        crossing: Crossing,
    );

    /// A computation child, standing under `crossing`.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        child: ComputationId,
        crossing: Crossing,
    );

    /// A value-type child, standing under `crossing`.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        child: ValueTypeId,
        crossing: Crossing,
    );

    /// A computation-type child, standing under `crossing`.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        child: CompTypeId,
        crossing: Crossing,
    );
}

/// `binders` intuitionistic binders crossed.
///
/// # Specification
/// trivial.
fn under(binders: Binders) -> Crossing
{
    opened(Zone::Intuitionistic, binders)
}

/// A binder count as the crossing it opens, in `zone`.
///
/// # Specification
/// trivial.
fn opened(
    zone: Zone,
    binders: Binders,
) -> Crossing
{
    Crossing::of(
        zone,
        BinderDepth::from(usize::try_from(u32::from(binders)).unwrap_or(usize::MAX)),
    )
}

/// Hand each child of `value` to `visit`, in order.
///
/// # Specification
/// - ensures: every child the former holds, once each and in the order the
///   former lists it, past the binders the former opens over it: one for a
///   static lambda's body and a bind frame's body, none elsewhere. A variable,
///   a constant, a literal, a primitive, the empty list, a hole and a web hold
///   no child.
/// - panics: none.
/// - executable: none — the clause is the former's scoping, which the body
///   states once; a predicate would restate it beside it.
///
/// # Adequacy
/// - hypothesis: L3 — the arena folds every minted value's support over these
///   children, so a binder former whose body reads its bound variable and one
///   that ignores it separate a crossing from none.
/// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
#[inline]
pub fn of_value<Walk>(
    value: &Value,
    visit: &mut Walk,
) where
    Walk: Visit,
{
    let at = Crossing::default();
    match *value {
        Value::Variable { .. }
        | Value::Primitive { .. }
        | Value::Constant(_)
        | Value::Literal(_)
        | Value::ListNil
        | Value::Hole(_)
        | Value::Web(_) => {},
        Value::PathRefl(body)
        | Value::Here(body)
        | Value::Injection(_, body)
        | Value::Stay(body)
        | Value::Forward(body)
        | Value::Lift { body, .. }
        | Value::Mark { body, .. } => visit.value(body, at),
        Value::PathProduct(first, second)
        | Value::Funext(first, second)
        | Value::Equiv(first, second)
        | Value::Univalence(first, second)
        | Value::Then(first, second)
        | Value::FlowProduct(first, second)
        | Value::FunctionFlow(first, second)
        | Value::ListCons(first, second)
        | Value::StaticApplication(first, second)
        | Value::RecordUpdate {
            base: first,
            overlay: second,
        }
        | Value::Ua {
            forward: first,
            backward: second,
            ..
        } => {
            visit.value(first, at);
            visit.value(second, at);
        },
        Value::Ascribe { value, ty } => {
            visit.value(value, at);
            visit.value_type(ty, at);
        },
        Value::PathEquiv {
            path_type,
            forward,
            backward,
            ..
        } => {
            visit.value_type(path_type, at);
            visit.value(forward, at);
            visit.value(backward, at);
        },
        Value::SessionRelated {
            source,
            target,
            payloads,
            ..
        } => {
            visit.value(source, at);
            visit.value(target, at);
            visit.value(payloads, at);
        },
        Value::Recorded(ref moves) => {
            for movement in moves.iter() {
                if let Maybe::Present(payload) = movement.payload() {
                    visit.value(payload, at);
                }
            }
        },
        Value::Dialogue(ref moves) => {
            for turn in moves.iter() {
                if let Maybe::Present(payload) = turn.movement.payload() {
                    visit.value(payload, at);
                }
            }
        },
        Value::Returned(body) | Value::Nested(body) | Value::Run(body) | Value::Thunk(body) => {
            visit.computation(body, at);
        },
        Value::Tuple(ref components) => {
            for &component in components {
                visit.value(component, at);
            }
        },
        Value::Compose {
            ref cells,
            realised,
            ..
        } => {
            for &cell in cells {
                visit.value(cell, at);
            }
            visit.computation(realised, at);
        },
        Value::Quote(quoted) => visit.value_type(quoted, at),
        Value::QuoteComputation(quoted) => visit.comp_type(quoted, at),
        Value::StaticLambda(body) => visit.value(body, under(Binders::ONE)),
        Value::Constructor {
            datatype,
            ref fields,
            ..
        } => {
            visit.value_type(datatype, at);
            for &field in fields {
                visit.value(field, at);
            }
        },
        Value::Record(ref fields) => {
            for &field in fields.values() {
                visit.value(field, at);
            }
        },
        Value::Row(ref row) => {
            for ty in row.types() {
                visit.value_type(ty, at);
            }
        },
        Value::Reify(ref frames) => {
            for frame in frames.iter() {
                match *frame {
                    StackFrame::Apply(argument) => visit.value(argument, at),
                    StackFrame::Bind(body) => visit.computation(body, under(Binders::ONE)),
                    StackFrame::Project(_) => {},
                }
            }
        },
    }
}

/// Hand each child of `computation` to `visit`, in order.
///
/// # Specification
/// - ensures: every child the former holds, once each and in the order the
///   former lists it, past the binders the former opens over it: one
///   intuitionistic for a lambda's, a fixpoint's and a shift's body, a bind's
///   continuation, a case's branches, a data case's motive, a transport's or a
///   ride's motive, a return clause and a scoped subject; two for a fold's cell
///   branch and an operation clause; one per component for a split's body and
///   one for its motive; a world form's scoped binders; one linear for each
///   half of a fork, for a receive's body, and a memory form's scoped binders.
///   A hole holds no child; a session action's endpoint and a memory form's
///   resident are names, not children.
/// - panics: none.
/// - executable: none — the clause is the former's scoping, which the body
///   states once; a predicate would restate it beside it.
///
/// # Adequacy
/// - hypothesis: L3 — the arena folds every minted computation's support over
///   these children, so a binder former whose body reads its bound variable and
///   one that ignores it separate a crossing from none, and the zones from each
///   other.
/// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
#[inline]
pub fn of_computation<Walk>(
    computation: &Computation,
    visit: &mut Walk,
) where
    Walk: Visit,
{
    let at = Crossing::default();
    match *computation {
        Computation::Primitive { ref arguments, .. } => {
            for &argument in arguments.iter() {
                visit.value(argument, at);
            }
        },
        Computation::Transport(path, value) => {
            visit.value(path, at);
            visit.value(value, at);
        },
        Computation::PathTransport {
            motive,
            path,
            value,
        }
        | Computation::Ride {
            motive,
            flow: path,
            value,
        } => {
            visit.value_type(motive, under(Binders::ONE));
            visit.value(path, at);
            visit.value(value, at);
        },
        Computation::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        } => {
            visit.comp_type(motive, at);
            for child in [path, start, over, value] {
                visit.value(child, at);
            }
        },
        Computation::Lambda(body)
        | Computation::Fixpoint { body, .. }
        | Computation::Shift(body) => {
            visit.computation(body, under(Binders::ONE));
        },
        Computation::Application(head, argument) => {
            visit.computation(head, at);
            visit.value(argument, at);
        },
        Computation::Return(value)
        | Computation::Force(value)
        | Computation::RecordProjection(value, _)
        | Computation::TupleProjection(value, _) => visit.value(value, at),
        Computation::Bind(bound, body) => {
            visit.computation(bound, at);
            visit.computation(body, under(Binders::ONE));
        },
        Computation::Ascribe { body, ty } => {
            visit.computation(body, at);
            visit.comp_type(ty, at);
        },
        Computation::Case {
            scrutinee,
            ref branches,
        } => {
            visit.value(scrutinee, at);
            for &branch in branches {
                visit.computation(branch, under(Binders::ONE));
            }
        },
        Computation::Split {
            scrutinee,
            arity,
            motive,
            body,
        } => {
            visit.value(scrutinee, at);
            if let SplitMotive::Scrutinee(motive) = motive {
                visit.comp_type(motive, under(Binders::ONE));
            }
            visit.computation(body, under(Binders::NONE.deeper_by(arity)));
        },
        Computation::DataCase {
            scrutinee,
            motive,
            ref branches,
            ..
        } => {
            visit.value(scrutinee, at);
            visit.comp_type(motive, under(Binders::ONE));
            for &branch in branches {
                visit.computation(branch, at);
            }
        },
        Computation::Hole(_) => {},
        Computation::Mark { body, .. }
        | Computation::Reset(body)
        | Computation::Project(_, body) => {
            visit.computation(body, at);
        },
        Computation::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        } => {
            visit.value_type(element, at);
            visit.value_type(result, at);
            visit.value(list, at);
            visit.computation(on_nil, at);
            visit.computation(on_cons, under(Binders::ONE.deeper()));
        },
        Computation::ListCase {
            list,
            on_nil,
            on_cons,
        } => {
            visit.value(list, at);
            visit.computation(on_nil, at);
            visit.computation(on_cons, under(Binders::ONE.deeper()));
        },
        Computation::Perform {
            ref signature,
            payload,
            ..
        } => {
            for ty in signature.types() {
                visit.value_type(ty, at);
            }
            visit.value(payload, at);
        },
        Computation::Exercise {
            capability,
            ref signature,
            payload,
            ..
        } => {
            for ty in signature.types() {
                visit.value_type(ty, at);
            }
            visit.value(capability, at);
            visit.value(payload, at);
        },
        Computation::Handle {
            ref signature,
            subject,
            on_return,
            ref clauses,
        } => {
            for ty in signature.types() {
                visit.value_type(ty, at);
            }
            visit.computation(subject, at);
            visit.computation(on_return, under(Binders::ONE));
            for clause in clauses.iter() {
                visit.computation(clause.body, under(Binders::ONE.deeper()));
            }
        },
        Computation::Scope {
            ref signature,
            subject,
            on_return,
            ref clauses,
        } => {
            for ty in signature.types() {
                visit.value_type(ty, at);
            }
            visit.computation(subject, under(Binders::ONE));
            visit.computation(on_return, under(Binders::ONE));
            for clause in clauses.iter() {
                visit.computation(clause.body, under(Binders::ONE.deeper()));
            }
        },
        Computation::Resume(stack, body) => {
            visit.value(stack, at);
            visit.computation(body, at);
        },
        Computation::Abandon(stack) | Computation::Decompose(stack) => visit.value(stack, at),
        Computation::With(ref components) => {
            for &component in components {
                visit.computation(component, at);
            }
        },
        Computation::Session(ref action) => {
            for ty in action.value_types() {
                visit.value_type(ty, at);
            }
            for value in action.values() {
                visit.value(value, at);
            }
            let crossing = match action.child_binders() {
                Binders::NONE => at,
                binders => opened(Zone::Linear, binders),
            };
            for child in action.computations() {
                visit.computation(child, crossing);
            }
        },
        Computation::Memory(ref form) => {
            for value in form.values() {
                visit.value(value, at);
            }
            for (body, binders) in form.scoped() {
                visit.computation(body, opened(Zone::Linear, binders));
            }
        },
        Computation::World(ref form) => {
            for value in form.values() {
                visit.value(value, at);
            }
            for (body, binders) in form.scoped() {
                visit.computation(body, opened(Zone::Intuitionistic, binders));
            }
        },
    }
}

/// Hand each child of `value_type` to `visit`, in order.
///
/// # Specification
/// - ensures: every child the former holds, once each and in the order the
///   former lists it: a Σ's second factor past one binder and every other child
///   in place. A base type, a universe, an abstract type, the unknown type, a
///   buffer, a web and a row type hold no child.
/// - panics: none.
/// - executable: none — the clause is the former's scoping, which the body
///   states once; a predicate would restate it beside it.
///
/// # Adequacy
/// - hypothesis: L3 — the arena folds every minted value type's support over
///   these children, so a Σ whose second factor reads its binder and one that
///   reads past it separate the crossing from none.
/// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
#[inline]
pub fn of_value_type<Walk>(
    value_type: &ValueType,
    visit: &mut Walk,
) where
    Walk: Visit,
{
    let at = Crossing::default();
    match *value_type {
        ValueType::Data { ref arguments, .. } => {
            for &argument in arguments {
                visit.value(argument, at);
            }
        },
        ValueType::Record(ref fields) => {
            for &field in fields.values() {
                visit.value_type(field, at);
            }
        },
        ValueType::PathUniverse(source, target) => {
            visit.value(source, at);
            visit.value(target, at);
        },
        ValueType::Path {
            carrier,
            left,
            right,
        }
        | ValueType::Bridge {
            carrier,
            left,
            right,
        }
        | ValueType::Flow {
            carrier,
            source: left,
            target: right,
        } => {
            visit.value_type(carrier, at);
            visit.value(left, at);
            visit.value(right, at);
        },
        ValueType::Run(session) | ValueType::Prefix(session) | ValueType::Dialogue(session) => {
            visit.value(session, at);
        },
        ValueType::Base(_)
        | ValueType::Universe { .. }
        | ValueType::Abstract(_)
        | ValueType::Unknown
        | ValueType::Buffer
        | ValueType::Web
        | ValueType::Row => {},
        ValueType::Product(ref components) | ValueType::Sum(ref components) => {
            for &component in components {
                visit.value_type(component, at);
            }
        },
        ValueType::Sigma { first, second } => {
            visit.value_type(first, at);
            visit.value_type(second, under(Binders::ONE));
        },
        ValueType::List(inner)
        | ValueType::Lift { inner, .. }
        | ValueType::Staged { base: inner, .. }
        | ValueType::Kept { value: inner, .. } => visit.value_type(inner, at),
        ValueType::Thunk(body) => visit.comp_type(body, at),
        ValueType::Element { code, .. } | ValueType::RowTail(code) => visit.value(code, at),
        ValueType::StaticPi { domain, codomain } => {
            visit.value_type(domain, at);
            visit.value_type(codomain, at);
        },
        ValueType::Stack { input, output } => {
            visit.comp_type(input, at);
            visit.comp_type(output, at);
        },
        ValueType::Session(ref session) => {
            for &payload in session.payloads() {
                visit.value_type(payload, at);
            }
        },
        ValueType::Capability { ref authority, .. } => {
            for ty in authority.types() {
                visit.value_type(ty, at);
            }
        },
        ValueType::World(ref ty) => {
            for inner in ty.types() {
                visit.value_type(inner, at);
            }
        },
    }
}

/// Hand each child of `comp_type` to `visit`, in order.
///
/// # Specification
/// - ensures: every child the former holds, once each and in the order the
///   former lists it: a Π's codomain past one binder and every other child in
///   place. The unknown computation type holds no child.
/// - panics: none.
/// - executable: none — the clause is the former's scoping, which the body
///   states once; a predicate would restate it beside it.
///
/// # Adequacy
/// - hypothesis: L3 — the arena folds every minted computation type's support
///   over these children, so a Π whose codomain reads its binder beside an
///   arrow over the same codomain separates the crossing from none.
/// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
#[inline]
pub fn of_comp_type<Walk>(
    comp_type: &CompType,
    visit: &mut Walk,
) where
    Walk: Visit,
{
    let at = Crossing::default();
    match *comp_type {
        CompType::Returner {
            result,
            ref effects,
        } => {
            visit.value_type(result, at);
            for ty in effects.types() {
                visit.value_type(ty, at);
            }
        },
        CompType::Arrow { domain, codomain } => {
            visit.value_type(domain, at);
            visit.comp_type(codomain, at);
        },
        CompType::Pi { domain, codomain } => {
            visit.value_type(domain, at);
            visit.comp_type(codomain, under(Binders::ONE));
        },
        CompType::Element { code, .. } => visit.value(code, at),
        CompType::Unknown => {},
        CompType::With(ref components) => {
            for &component in components {
                visit.comp_type(component, at);
            }
        },
        CompType::Codata { ref arguments, .. } => {
            for &argument in arguments {
                visit.value(argument, at);
            }
        },
    }
}
