//! The support every node carries, built from its children's when it is
//! minted.
//!
//! A node's support is what it names itself — a variable its index, a session
//! action its endpoint, a memory form its resident slot — together with what
//! each child selects past the binders between them, lowered by them. The
//! binders each child stands under are the former's scoping, stated once
//! here: the intuitionistic binders are the ones the rewrite machines count
//! per child, and the linear ones are a fork's two ends, a receive's payload
//! and a hold's or an access's view. A primitive's generated body is closed
//! and stands as a leaf, as the rewrites read it.
//!
//! A child is read through the support it carries, so minting a node is one
//! union over its children rather than a walk below them; a dangling child
//! adds nothing, as a dangling child resolves to nothing everywhere else. The
//! union is kept as one slot in the node's row, its wide words in the arena's
//! word arena.

use quenchant_shape::shape::Maybe;

use super::ArenaIndex;
use super::CoreArena;
use super::id_offset;
use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::context::BinderDepth;
use crate::control::StackFrame;
use crate::rewrite::Binders;
use crate::support::Crossing;
use crate::support::Slot;
use crate::support::ThinningRef;
use crate::support::Union;
use crate::syntax::CompType;
use crate::syntax::Computation;
use crate::syntax::SplitMotive;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

/// `binders` intuitionistic binders crossed.
///
/// # Specification
/// trivial.
fn under(binders: Binders) -> Crossing
{
    opened(Zone::Intuitionistic, binders)
}

/// `binders` linear binders crossed.
///
/// # Specification
/// trivial.
fn under_linear(binders: Binders) -> Crossing
{
    opened(Zone::Linear, binders)
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

impl CoreArena
{
    /// Add a value child's support, read past `crossing`, to `union`.
    ///
    /// # Specification
    /// trivial.
    fn value_into(
        &self,
        union: &mut Union,
        child: ValueId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.values.get(id_offset(ArenaIndex(child.0)).0) {
            union.stored_child(row.support, &self.words, crossing);
        }
    }

    /// Add a computation child's support, read past `crossing`, to `union`.
    ///
    /// # Specification
    /// trivial.
    fn computation_into(
        &self,
        union: &mut Union,
        child: ComputationId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.computations.get(id_offset(ArenaIndex(child.0)).0) {
            union.stored_child(row.support, &self.words, crossing);
        }
    }

    /// Add a value-type child's support, read past `crossing`, to `union`.
    ///
    /// # Specification
    /// trivial.
    fn value_type_into(
        &self,
        union: &mut Union,
        child: ValueTypeId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.value_types.get(id_offset(ArenaIndex(child.0)).0) {
            union.stored_child(row.support, &self.words, crossing);
        }
    }

    /// Add a computation-type child's support, read past `crossing`, to
    /// `union`.
    ///
    /// # Specification
    /// trivial.
    fn comp_type_into(
        &self,
        union: &mut Union,
        child: CompTypeId,
        crossing: Crossing,
    )
    {
        if let Some(row) = self.comp_types.get(id_offset(ArenaIndex(child.0)).0) {
            union.stored_child(row.support, &self.words, crossing);
        }
    }

    /// The support a value about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `value` is minted in this arena.
    /// - ensures: the variable's own index for a variable; otherwise the union
    ///   of the children's carried supports, each past the binders the former
    ///   opens over it — one for a static lambda's body and a bind frame's
    ///   body, none elsewhere.
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which the body
    ///   states once; a predicate would restate it beside it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every binder former with a body that reads and one
    ///   that ignores its bound variable separates a crossing from none, and a
    ///   variable in each zone separates the zones. Beyond this crate,
    ///   `gandr-core-sequent`'s property suite holds every node of every
    ///   generated term to the free indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn value_carried(
        &mut self,
        value: &Value,
    ) -> Slot
    {
        let at = Crossing::default();
        let mut union = Union::new();
        match *value {
            Value::Variable { zone, index } => union.name(zone, index),
            Value::Primitive { .. }
            | Value::Constant(_)
            | Value::Literal(_)
            | Value::ListNil
            | Value::Hole(_) => {},
            Value::PathRefl(body)
            | Value::Here(body)
            | Value::Injection(_, body)
            | Value::Stay(body)
            | Value::Forward(body)
            | Value::Lift { body, .. }
            | Value::Mark { body, .. } => self.value_into(&mut union, body, at),
            Value::PathProduct(first, second)
            | Value::Funext(first, second)
            | Value::Equiv(first, second)
            | Value::Univalence(first, second)
            | Value::Then(first, second)
            | Value::FlowProduct(first, second)
            | Value::FunctionFlow(first, second)
            | Value::ListCons(first, second)
            | Value::StaticApplication(first, second)
            | Value::SessionRelated {
                source: first,
                target: second,
                ..
            }
            | Value::Ua {
                forward: first,
                backward: second,
                ..
            } => {
                self.value_into(&mut union, first, at);
                self.value_into(&mut union, second, at);
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => {
                self.value_type_into(&mut union, path_type, at);
                self.value_into(&mut union, forward, at);
                self.value_into(&mut union, backward, at);
            },
            Value::Recorded(ref moves) => {
                for movement in moves.iter() {
                    if let quenchant_shape::shape::Maybe::Present(payload) = movement.payload() {
                        self.value_into(&mut union, payload, at);
                    }
                }
            },
            Value::Returned(body) | Value::Nested(body) | Value::Run(body) | Value::Thunk(body) => {
                self.computation_into(&mut union, body, at);
            },
            Value::Tuple(ref components) => {
                for &component in components {
                    self.value_into(&mut union, component, at);
                }
            },
            Value::Quote(quoted) => self.value_type_into(&mut union, quoted, at),
            Value::QuoteComputation(quoted) => self.comp_type_into(&mut union, quoted, at),
            Value::StaticLambda(body) => self.value_into(&mut union, body, under(Binders::ONE)),
            Value::Constructor {
                datatype,
                ref fields,
                ..
            } => {
                self.value_type_into(&mut union, datatype, at);
                for &field in fields {
                    self.value_into(&mut union, field, at);
                }
            },
            Value::Record(ref fields) => {
                for &field in fields.values() {
                    self.value_into(&mut union, field, at);
                }
            },
            Value::Reify(ref frames) => {
                for frame in frames.iter() {
                    match *frame {
                        StackFrame::Apply(argument) => self.value_into(&mut union, argument, at),
                        StackFrame::Bind(body) => {
                            self.computation_into(&mut union, body, under(Binders::ONE));
                        },
                        StackFrame::Project(_) => {},
                    }
                }
            },
        }
        self.words.store_union(union)
    }

    /// The support a computation about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `computation` is minted in this arena.
    /// - ensures: the union of what the computation names itself — a session
    ///   action's endpoint, a memory form's resident, each linear — and the
    ///   children's carried supports, each past the binders the former opens
    ///   over it: one intuitionistic for a lambda's, a fixpoint's and a shift's
    ///   body, a bind's continuation, a case's branches, a data case's motive,
    ///   a transport's or a ride's motive, a return clause and a scoped
    ///   subject; two for a fold's cell branch and an operation clause; one per
    ///   component for a split's body and one for its motive; a world form's
    ///   scoped binders; one linear for each half of a fork, for a receive's
    ///   body, and a memory form's scoped binders.
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which the body
    ///   states once; a predicate would restate it beside it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every binder former with a body that reads and one
    ///   that ignores its bound variable separates a crossing from none and the
    ///   zones from each other. Beyond this crate, `gandr-core-sequent`'s
    ///   property suite holds every node of every generated term to the free
    ///   indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn computation_carried(
        &mut self,
        computation: &Computation,
    ) -> Slot
    {
        let at = Crossing::default();
        let mut union = Union::new();
        match *computation {
            Computation::Primitive { ref arguments, .. } => {
                for &argument in arguments.iter() {
                    self.value_into(&mut union, argument, at);
                }
            },
            Computation::Transport(path, value) => {
                self.value_into(&mut union, path, at);
                self.value_into(&mut union, value, at);
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
                self.value_type_into(&mut union, motive, under(Binders::ONE));
                self.value_into(&mut union, path, at);
                self.value_into(&mut union, value, at);
            },
            Computation::TelescopeTransport {
                motive,
                path,
                start,
                over,
                value,
            } => {
                self.comp_type_into(&mut union, motive, at);
                for child in [path, start, over, value] {
                    self.value_into(&mut union, child, at);
                }
            },
            Computation::Lambda(body)
            | Computation::Fixpoint { body, .. }
            | Computation::Shift(body) => {
                self.computation_into(&mut union, body, under(Binders::ONE));
            },
            Computation::Application(head, argument) => {
                self.computation_into(&mut union, head, at);
                self.value_into(&mut union, argument, at);
            },
            Computation::Return(value)
            | Computation::Force(value)
            | Computation::RecordProjection(value, _)
            | Computation::TupleProjection(value, _) => self.value_into(&mut union, value, at),
            Computation::Bind(bound, body) => {
                self.computation_into(&mut union, bound, at);
                self.computation_into(&mut union, body, under(Binders::ONE));
            },
            Computation::Ascribe { body, ty } => {
                self.computation_into(&mut union, body, at);
                self.comp_type_into(&mut union, ty, at);
            },
            Computation::Case {
                scrutinee,
                ref branches,
            } => {
                self.value_into(&mut union, scrutinee, at);
                for &branch in branches {
                    self.computation_into(&mut union, branch, under(Binders::ONE));
                }
            },
            Computation::Split {
                scrutinee,
                arity,
                motive,
                body,
            } => {
                self.value_into(&mut union, scrutinee, at);
                if let SplitMotive::Scrutinee(motive) = motive {
                    self.comp_type_into(&mut union, motive, under(Binders::ONE));
                }
                self.computation_into(&mut union, body, under(Binders::NONE.deeper_by(arity)));
            },
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            } => {
                self.value_into(&mut union, scrutinee, at);
                self.comp_type_into(&mut union, motive, under(Binders::ONE));
                for &branch in branches {
                    self.computation_into(&mut union, branch, at);
                }
            },
            Computation::Hole(_) => {},
            Computation::Mark { body, .. }
            | Computation::Reset(body)
            | Computation::Project(_, body) => self.computation_into(&mut union, body, at),
            Computation::ListFold {
                element,
                result,
                list,
                on_nil,
                on_cons,
            } => {
                self.value_type_into(&mut union, element, at);
                self.value_type_into(&mut union, result, at);
                self.value_into(&mut union, list, at);
                self.computation_into(&mut union, on_nil, at);
                self.computation_into(&mut union, on_cons, under(Binders::ONE.deeper()));
            },
            Computation::ListCase {
                list,
                on_nil,
                on_cons,
            } => {
                self.value_into(&mut union, list, at);
                self.computation_into(&mut union, on_nil, at);
                self.computation_into(&mut union, on_cons, under(Binders::ONE.deeper()));
            },
            Computation::Perform {
                ref signature,
                payload,
                ..
            } => {
                for ty in signature.types() {
                    self.value_type_into(&mut union, ty, at);
                }
                self.value_into(&mut union, payload, at);
            },
            Computation::Exercise {
                capability,
                ref signature,
                payload,
                ..
            } => {
                for ty in signature.types() {
                    self.value_type_into(&mut union, ty, at);
                }
                self.value_into(&mut union, capability, at);
                self.value_into(&mut union, payload, at);
            },
            Computation::Handle {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => {
                for ty in signature.types() {
                    self.value_type_into(&mut union, ty, at);
                }
                self.computation_into(&mut union, subject, at);
                self.computation_into(&mut union, on_return, under(Binders::ONE));
                for clause in clauses.iter() {
                    self.computation_into(&mut union, clause.body, under(Binders::ONE.deeper()));
                }
            },
            Computation::Scope {
                ref signature,
                subject,
                on_return,
                ref clauses,
            } => {
                for ty in signature.types() {
                    self.value_type_into(&mut union, ty, at);
                }
                self.computation_into(&mut union, subject, under(Binders::ONE));
                self.computation_into(&mut union, on_return, under(Binders::ONE));
                for clause in clauses.iter() {
                    self.computation_into(&mut union, clause.body, under(Binders::ONE.deeper()));
                }
            },
            Computation::Resume(stack, body) => {
                self.value_into(&mut union, stack, at);
                self.computation_into(&mut union, body, at);
            },
            Computation::With(ref components) => {
                for &component in components {
                    self.computation_into(&mut union, component, at);
                }
            },
            Computation::Session(ref action) => {
                if let quenchant_shape::shape::Maybe::Present(endpoint) = action.endpoint() {
                    union.name(Zone::Linear, endpoint);
                }
                for ty in action.value_types() {
                    self.value_type_into(&mut union, ty, at);
                }
                for value in action.values() {
                    self.value_into(&mut union, value, at);
                }
                let crossing = match action.child_binders() {
                    Binders::NONE => at,
                    binders => under_linear(binders),
                };
                for child in action.computations() {
                    self.computation_into(&mut union, child, crossing);
                }
            },
            Computation::Memory(ref form) => {
                if let quenchant_shape::shape::Maybe::Present(resident) = form.resident() {
                    union.name(Zone::Linear, resident);
                }
                for value in form.values() {
                    self.value_into(&mut union, value, at);
                }
                for (body, binders) in form.scoped() {
                    self.computation_into(&mut union, body, opened(Zone::Linear, binders));
                }
            },
            Computation::World(ref form) => {
                for value in form.values() {
                    self.value_into(&mut union, value, at);
                }
                for (body, binders) in form.scoped() {
                    self.computation_into(&mut union, body, opened(Zone::Intuitionistic, binders));
                }
            },
        }
        self.words.store_union(union)
    }

    /// The support a value type about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `value_type` is minted in this arena.
    /// - ensures: the union of the children's carried supports, a Σ's second
    ///   factor past one binder and every other child in place.
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which the body
    ///   states once; a predicate would restate it beside it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a Σ whose second factor reads its binder and one that
    ///   reads past it separate the crossing from none. Beyond this crate,
    ///   `gandr-core-sequent`'s property suite holds every node of every
    ///   generated term to the free indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn value_type_carried(
        &mut self,
        value_type: &ValueType,
    ) -> Slot
    {
        let at = Crossing::default();
        let mut union = Union::new();
        match *value_type {
            ValueType::Data { ref arguments, .. } => {
                for &argument in arguments {
                    self.value_into(&mut union, argument, at);
                }
            },
            ValueType::Record(ref fields) => {
                for &field in fields.values() {
                    self.value_type_into(&mut union, field, at);
                }
            },
            ValueType::PathUniverse(source, target) => {
                self.value_into(&mut union, source, at);
                self.value_into(&mut union, target, at);
            },
            ValueType::Path {
                carrier,
                left,
                right,
            }
            | ValueType::Flow {
                carrier,
                source: left,
                target: right,
            } => {
                self.value_type_into(&mut union, carrier, at);
                self.value_into(&mut union, left, at);
                self.value_into(&mut union, right, at);
            },
            ValueType::Run(session) => self.value_into(&mut union, session, at),
            ValueType::Base(_)
            | ValueType::Universe { .. }
            | ValueType::Abstract(_)
            | ValueType::Unknown => {},
            ValueType::Product(ref components) | ValueType::Sum(ref components) => {
                for &component in components {
                    self.value_type_into(&mut union, component, at);
                }
            },
            ValueType::Sigma { first, second } => {
                self.value_type_into(&mut union, first, at);
                self.value_type_into(&mut union, second, under(Binders::ONE));
            },
            ValueType::List(inner)
            | ValueType::Lift { inner, .. }
            | ValueType::Staged { base: inner, .. } => {
                self.value_type_into(&mut union, inner, at);
            },
            ValueType::Thunk(body) => self.comp_type_into(&mut union, body, at),
            ValueType::Element { code, .. } => self.value_into(&mut union, code, at),
            ValueType::StaticPi { domain, codomain } => {
                self.value_type_into(&mut union, domain, at);
                self.value_type_into(&mut union, codomain, at);
            },
            ValueType::Stack { input, output } => {
                self.comp_type_into(&mut union, input, at);
                self.comp_type_into(&mut union, output, at);
            },
            ValueType::Session(ref session) => {
                for &payload in session.payloads() {
                    self.value_type_into(&mut union, payload, at);
                }
            },
            ValueType::Capability { ref authority, .. } => {
                for ty in authority.types() {
                    self.value_type_into(&mut union, ty, at);
                }
            },
            ValueType::World(ref ty) => {
                for inner in ty.types() {
                    self.value_type_into(&mut union, inner, at);
                }
            },
        }
        self.words.store_union(union)
    }

    /// The support a computation type about to be minted carries.
    ///
    /// # Specification
    /// - requires: every child of `comp_type` is minted in this arena.
    /// - ensures: the union of the children's carried supports, a Π's codomain
    ///   past one binder and every other child in place.
    /// - panics: none.
    /// - executable: none — the clause is the former's scoping, which the body
    ///   states once; a predicate would restate it beside it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a Π whose codomain reads its binder beside an arrow
    ///   over the same codomain separates the crossing from none. Beyond this
    ///   crate, `gandr-core-sequent`'s property suite holds every node of every
    ///   generated term to the free indices the shift machine finds.
    /// - witness: `arena::tests::every_binder_former_carries_its_bodys_support_past_its_binders`
    pub(super) fn comp_type_carried(
        &mut self,
        comp_type: &CompType,
    ) -> Slot
    {
        let at = Crossing::default();
        let mut union = Union::new();
        match *comp_type {
            CompType::Returner {
                result,
                ref effects,
            } => {
                self.value_type_into(&mut union, result, at);
                for ty in effects.types() {
                    self.value_type_into(&mut union, ty, at);
                }
            },
            CompType::Arrow { domain, codomain } => {
                self.value_type_into(&mut union, domain, at);
                self.comp_type_into(&mut union, codomain, at);
            },
            CompType::Pi { domain, codomain } => {
                self.value_type_into(&mut union, domain, at);
                self.comp_type_into(&mut union, codomain, under(Binders::ONE));
            },
            CompType::Element { code, .. } => self.value_into(&mut union, code, at),
            CompType::Unknown => {},
            CompType::With(ref components) => {
                for &component in components {
                    self.comp_type_into(&mut union, component, at);
                }
            },
            CompType::Codata { ref arguments, .. } => {
                for &argument in arguments {
                    self.value_into(&mut union, argument, at);
                }
            },
        }
        self.words.store_union(union)
    }

    /// The support `slot` keeps, read in place.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(super) fn support_of(
        &self,
        slot: Slot,
    ) -> ThinningRef<'_>
    {
        match self.words.read(slot) {
            Maybe::Present(support) => support,
            // reason: every handle a row holds names words this arena wrote,
            // and a truncation drops the row with them.
            Maybe::Absent(_) => ThinningRef::empty(),
        }
    }
}
