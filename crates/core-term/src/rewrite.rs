//! The rewrites a dependent type needs: shifting a type into a deeper context,
//! instantiating a dependent codomain at an argument, and strengthening a type
//! out from under the binder it was synthesized beneath.
//!
//! # Why a type is rewritten at all
//!
//! [`ValueType::Element`] and [`CompType::Element`] read a type off a code,
//! and a code can be a bound variable, so a type can carry a free de Bruijn
//! index. A type read from a context slot was formed where the slot was
//! opened and has to be shifted to the depth it is read at; a dependent
//! codomain is scoped under its binder and has to be instantiated at the
//! argument an application supplies; a type synthesized under a binder has to
//! be lowered back out of it, which fails exactly when the type mentions the
//! binder.
//!
//! # One engine, three rewrites
//!
//! The three differ only at a variable occurrence; every other former is a
//! congruence that rewrites its children, each at the depth its position sits
//! at, and mints a node only where a child changed. The engine is iterative —
//! a heap task stack, children opened in reverse and closed in order — so a
//! deep type costs heap rather than stack, and memoized per node at the depth
//! it is reached at, so a shared subterm is rewritten once however many paths
//! reach it.
//!
//! A substitution carries its replacement under the binders it crosses: at
//! depth `d` the occurrence the depth names becomes the replacement shifted by
//! `d`, scheduled through the same engine, which is what keeps a free variable
//! of the replacement from being captured by a binder it is carried under.
//!
//! Rebuilding goes through the arena's constructors, so a rewrite that turns a
//! decode's code into a quote yields the quoted type: instantiating `El x` at
//! `⌜A⌝` answers `A`.
//!
//! Only the intuitionistic zone is rewritten. No former binds into the linear
//! zone, so a linear index counts no binder these rewrites cross and stands.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_arith::arith;
use quenchant_shape::shape::Maybe;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::syntax::CompType;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

/// A count of intuitionistic binders: how far a walk has descended, or how far
/// a shift raises a free index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Binders(u32);

impl Binders
{
    /// No binder.
    pub const NONE: Self = Self(0_u32);
    /// One binder.
    pub const ONE: Self = Self(1_u32);

    /// One binder further in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count plus one, clamped at the representable ceiling,
    ///   which no context reaches.
    /// - provides: the step a walk takes past a binder.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn deeper(self) -> Self
    {
        // reason: a binder count uses u32::MAX as its conservative ceiling.
        Self(u32::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(1_u32),
        )))
    }

    /// The count a variable at `index` reaches past: its index plus one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `index + 1`, clamped at the representable ceiling.
    /// - provides: the shift a context slot's type takes when read through an
    ///   occurrence at `index`, since the slot was opened that many binders
    ///   further out.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn past(index: DeBruijnIndex) -> Self
    {
        Self(u32::from(index)).deeper()
    }
}

impl From<u32> for Binders
{
    /// Wraps a raw count as a binder count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<Binders> for u32
{
    /// Unwraps a binder count to its raw value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Binders) -> Self
    {
        count.0
    }
}

/// Why a strengthening answered nothing.
pub mod strengthening
{
    /// The single reason a type cannot be lowered out of its binder.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// The type mentions the binder it is being lowered out of.
        MentionsBinder,
    }
}

/// A node of any of the four families.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// What a walk does at a variable occurrence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Rewrite
{
    /// Raise every free index by the count.
    Shift(Binders),
    /// Replace the index the depth names by the value, and lower every index
    /// outside it.
    Substitute(ValueId),
    /// Lower every index outside the depth, recording a mention of the index
    /// the depth names.
    Lower,
}

/// Whether a lowering met the binder it lowers out of.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Mention
{
    /// No occurrence named the binder.
    Absent,
    /// Some occurrence did.
    Present,
}

/// One unit of the engine's work.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Task
{
    /// Rewrite a node at a depth: answer it from the memo or a variable rule,
    /// or schedule its children and its close.
    Open(Node, Binders, Rewrite),
    /// Combine a node's rewritten children into its own result.
    Close(Node, Binders, Rewrite),
    /// Record the result on top of the stack as a node's own.
    Record(Node, Binders, Rewrite),
}

/// What one variable occurrence rewrites to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Occurrence
{
    /// The occurrence's rewritten value, final.
    Answered(ValueId),
    /// The replacement, still to be carried under this many binders.
    Carried(ValueId, Binders),
}

/// The engine's state for one rewrite of one subject.
struct Engine<'arena>
{
    /// The arena the subject lives in and the rewritten nodes are minted into.
    arena: &'arena mut CoreArena,
    /// Rewritten results, keyed by node, depth and rewrite.
    memo: BTreeMap<(Node, Binders, Rewrite), Node>,
    /// The pending work.
    tasks: Vec<Task>,
    /// The results of closed nodes, awaiting their parents.
    results: Vec<Node>,
    /// Whether a lowering met its binder.
    mention: Mention,
}

impl<'arena> Engine<'arena>
{
    /// A fresh engine over `arena`.
    ///
    /// # Specification
    /// trivial.
    fn new(arena: &'arena mut CoreArena) -> Self
    {
        Self {
            arena,
            memo: BTreeMap::new(),
            tasks: Vec::new(),
            results: Vec::new(),
            mention: Mention::Absent,
        }
    }

    /// Rewrite `subject` from depth zero.
    ///
    /// # Specification
    /// - requires: `subject` names a node of this engine's arena.
    /// - ensures: the rewritten node, in the subject's family; an unreadable
    ///   subject answers itself.
    /// - provides: the whole iterative walk, memoized per node and depth.
    /// - fails: never.
    /// - panics: none.
    fn run(
        &mut self,
        subject: Node,
        rewrite: Rewrite,
    ) -> Node
    {
        self.tasks.push(Task::Open(subject, Binders::NONE, rewrite));
        while let Some(task) = self.tasks.pop() {
            match task {
                | Task::Open(node, depth, step) => self.open(node, depth, step),
                | Task::Close(node, depth, step) => {
                    let rewritten = self.close(node);
                    let _previous = self.memo.insert((node, depth, step), rewritten);
                    self.results.push(rewritten);
                },
                | Task::Record(node, depth, step) => {
                    if let Some(&rewritten) = self.results.last() {
                        let _previous = self.memo.insert((node, depth, step), rewritten);
                    }
                },
            }
        }
        self.results.pop().unwrap_or(subject)
    }

    /// Open one node: answer it at once when the memo or a variable rule can,
    /// and otherwise schedule its close after its children.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach `node`.
    /// - ensures: pushes exactly one result for `node` by the time every task
    ///   this call schedules has run.
    /// - provides: the scheduling half of the engine.
    /// - fails: never.
    /// - panics: none.
    fn open(
        &mut self,
        node: Node,
        depth: Binders,
        rewrite: Rewrite,
    )
    {
        if let Some(&done) = self.memo.get(&(node, depth, rewrite)) {
            self.results.push(done);
            return;
        }
        if let Node::Value(id) = node
            && let Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }) = self.arena.value(id)
        {
            match self.occurrence(id, index, depth, rewrite) {
                | Occurrence::Answered(rewritten) => {
                    let _previous = self
                        .memo
                        .insert((node, depth, rewrite), Node::Value(rewritten));
                    self.results.push(Node::Value(rewritten));
                },
                | Occurrence::Carried(replacement, under) => {
                    self.tasks.push(Task::Record(node, depth, rewrite));
                    self.tasks.push(Task::Open(
                        Node::Value(replacement),
                        Binders::NONE,
                        Rewrite::Shift(under),
                    ));
                },
            }
            return;
        }
        self.tasks.push(Task::Close(node, depth, rewrite));
        self.push_children(node, depth, rewrite);
    }

    /// The rewritten form of one intuitionistic occurrence.
    ///
    /// **This is the only place the three rewrites differ.** A shift raises
    /// an index at or past the depth and spares one inside it; a substitution
    /// spares an index inside the depth, replaces the one the depth names and
    /// lowers every one past it; a lowering does the same with no
    /// replacement, recording that the named index occurred.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach the
    ///   occurrence `id` at `index`.
    /// - ensures: the rule above; a substitution's replacement at a positive
    ///   depth is answered as a carry, to be shifted by the depth.
    /// - provides: the whole variable rule of the three rewrites.
    /// - fails: never.
    /// - panics: none.
    fn occurrence(
        &mut self,
        id: ValueId,
        index: DeBruijnIndex,
        depth: Binders,
        rewrite: Rewrite,
    ) -> Occurrence
    {
        let position = Binders(u32::from(index));
        match rewrite {
            | Rewrite::Shift(amount) => {
                if position < depth || amount == Binders::NONE {
                    Occurrence::Answered(id)
                }
                else {
                    // reason: a raised index clamps at the representable ceiling.
                    let raised = u32::from(arith::saturating_add(
                        arith::Int::from(position.0),
                        arith::Int::from(amount.0),
                    ));
                    Occurrence::Answered(
                        self.arena
                            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(raised)),
                    )
                }
            },
            | Rewrite::Substitute(replacement) => match position.cmp(&depth) {
                | core::cmp::Ordering::Less => Occurrence::Answered(id),
                | core::cmp::Ordering::Equal if depth == Binders::NONE => {
                    Occurrence::Answered(replacement)
                },
                | core::cmp::Ordering::Equal => Occurrence::Carried(replacement, depth),
                | core::cmp::Ordering::Greater => Occurrence::Answered(self.lowered(position)),
            },
            | Rewrite::Lower => match position.cmp(&depth) {
                | core::cmp::Ordering::Less => Occurrence::Answered(id),
                | core::cmp::Ordering::Equal => {
                    self.mention = Mention::Present;
                    Occurrence::Answered(id)
                },
                | core::cmp::Ordering::Greater => Occurrence::Answered(self.lowered(position)),
            },
        }
    }

    /// Mint the occurrence one binder further in than `position`.
    ///
    /// # Specification
    /// - requires: `position` is strictly above some depth, so it is positive.
    /// - ensures: a fresh intuitionistic variable at `position - 1`.
    /// - provides: the lowering half of substitution and strengthening.
    /// - fails: never.
    /// - panics: none.
    fn lowered(
        &mut self,
        position: Binders,
    ) -> ValueId
    {
        // reason: the caller established position > depth >= 0, and a
        // saturating step keeps the walk total on any input.
        let lowered = u32::from(arith::saturating_sub(
            arith::Int::from(position.0),
            arith::Int::from(1_u32),
        ));
        self.arena
            .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(lowered))
    }

    /// Schedule `node`'s children, each at the depth its position sits at.
    ///
    /// **The binding positions are the whole content of this function.** A
    /// lambda binds for its body, a static lambda for its body, a bind for
    /// its body and not its bound computation, a case for each branch and not
    /// its scrutinee, and the dependent arrow for its codomain and not its
    /// domain. A quote and a decode bind nothing: they cross between terms
    /// and types at the depth they stand at. Nor does a static Pi: its
    /// codomain stands in the ambient context.
    ///
    /// # Specification
    /// - requires: `depth` is the number of binders crossed to reach `node`.
    /// - ensures: one open task per child, pushed in reverse so the children
    ///   close in order, each at the depth its position sits at; a leaf and an
    ///   unreadable node push nothing.
    /// - provides: the only statement of where the core language binds.
    /// - fails: never.
    /// - panics: none.
    fn push_children(
        &mut self,
        node: Node,
        depth: Binders,
        rewrite: Rewrite,
    )
    {
        let mut children: Vec<(Node, Binders)> = Vec::new();
        match node {
            | Node::Value(id) => match self.arena.value(id) {
                | Some(
                    &Value::Variable { .. }
                    | &Value::Constant(_)
                    | &Value::Unit
                    | &Value::Literal(_),
                )
                | None => {},
                | Some(&Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                }) => {
                    children.push((Node::ValueType(path_type), depth));
                    children.push((Node::Value(forward), depth));
                    children.push((Node::Value(backward), depth));
                },
                | Some(&Value::PathRefl(code)) => children.push((Node::Value(code), depth)),
                | Some(&Value::PathProduct(first, second) | &Value::Pair(first, second)) => {
                    children.push((Node::Value(first), depth));
                    children.push((Node::Value(second), depth));
                },
                | Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                    children.push((Node::Value(body), depth));
                },
                | Some(&Value::Thunk(body)) => children.push((Node::Computation(body), depth)),
                | Some(&Value::Quote(quoted)) => children.push((Node::ValueType(quoted), depth)),
                | Some(&Value::QuoteComputation(quoted)) => {
                    children.push((Node::CompType(quoted), depth));
                },
                | Some(&Value::StaticLambda(body)) => {
                    children.push((Node::Value(body), depth.deeper()));
                },
                | Some(&Value::StaticApplication(head, argument)) => {
                    children.push((Node::Value(head), depth));
                    children.push((Node::Value(argument), depth));
                },
            },
            | Node::Computation(id) => match self.arena.computation(id) {
                | None => {},
                | Some(&Computation::Transport(path, value)) => {
                    children.push((Node::Value(path), depth));
                    children.push((Node::Value(value), depth));
                },
                | Some(&Computation::Lambda(body)) => {
                    children.push((Node::Computation(body), depth.deeper()));
                },
                | Some(&Computation::Application(head, argument)) => {
                    children.push((Node::Computation(head), depth));
                    children.push((Node::Value(argument), depth));
                },
                | Some(&Computation::Return(value) | &Computation::Force(value)) => {
                    children.push((Node::Value(value), depth));
                },
                | Some(&Computation::Bind(bound, body)) => {
                    children.push((Node::Computation(bound), depth));
                    children.push((Node::Computation(body), depth.deeper()));
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => {
                    children.push((Node::Value(scrutinee), depth));
                    children.push((Node::Computation(on_left), depth.deeper()));
                    children.push((Node::Computation(on_right), depth.deeper()));
                },
            },
            | Node::ValueType(id) => match self.arena.value_type(id) {
                | Some(
                    &ValueType::Base(_)
                    | &ValueType::Unit
                    | &ValueType::Universe { .. }
                    | &ValueType::Abstract(_),
                )
                | None => {},
                | Some(
                    &ValueType::Product(first, second)
                    | &ValueType::Sum(first, second)
                    | &ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    },
                ) => {
                    children.push((Node::ValueType(first), depth));
                    children.push((Node::ValueType(second), depth));
                },
                | Some(&ValueType::PathUniverse(source, target)) => {
                    children.push((Node::Value(source), depth));
                    children.push((Node::Value(target), depth));
                },
                | Some(&ValueType::Thunk(body)) => children.push((Node::CompType(body), depth)),
                | Some(&ValueType::Lift { inner, .. }) => {
                    children.push((Node::ValueType(inner), depth));
                },
                | Some(&ValueType::Element { code, .. }) => {
                    children.push((Node::Value(code), depth));
                },
            },
            | Node::CompType(id) => match self.arena.comp_type(id) {
                | None => {},
                | Some(&CompType::Returner(result)) => {
                    children.push((Node::ValueType(result), depth));
                },
                | Some(&CompType::Arrow { domain, codomain }) => {
                    children.push((Node::ValueType(domain), depth));
                    children.push((Node::CompType(codomain), depth));
                },
                | Some(&CompType::Pi { domain, codomain }) => {
                    children.push((Node::ValueType(domain), depth));
                    children.push((Node::CompType(codomain), depth.deeper()));
                },
                | Some(&CompType::Element { code, .. }) => {
                    children.push((Node::Value(code), depth));
                },
            },
        }
        while let Some((child, at)) = children.pop() {
            self.tasks.push(Task::Open(child, at, rewrite));
        }
    }

    /// Pop one child's result, read in `family`, or fall back to the child.
    ///
    /// The fallback is unreachable: an open pushed one result per child
    /// before its parent's close ran. Reading it as unchanged is the fail-safe
    /// direction, since it cannot fabricate a node.
    ///
    /// # Specification
    /// trivial.
    fn popped(
        &mut self,
        original: Node,
    ) -> Node
    {
        self.results.pop().unwrap_or(original)
    }

    /// Pop a value child's result.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        original: ValueId,
    ) -> ValueId
    {
        match self.popped(Node::Value(original)) {
            | Node::Value(id) => id,
            | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => original,
        }
    }

    /// Pop a computation child's result.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        original: ComputationId,
    ) -> ComputationId
    {
        match self.popped(Node::Computation(original)) {
            | Node::Computation(id) => id,
            | Node::Value(_) | Node::ValueType(_) | Node::CompType(_) => original,
        }
    }

    /// Pop a value-type child's result.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        original: ValueTypeId,
    ) -> ValueTypeId
    {
        match self.popped(Node::ValueType(original)) {
            | Node::ValueType(id) => id,
            | Node::Value(_) | Node::Computation(_) | Node::CompType(_) => original,
        }
    }

    /// Pop a computation-type child's result.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        original: CompTypeId,
    ) -> CompTypeId
    {
        match self.popped(Node::CompType(original)) {
            | Node::CompType(id) => id,
            | Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => original,
        }
    }

    /// Combine `node`'s rewritten children into its own result, minting only
    /// where a child changed.
    ///
    /// Children were scheduled to close in order, so the last child's result
    /// is on top: each arm pops in reverse.
    ///
    /// # Specification
    /// - requires: the results stack holds one result per child of `node`.
    /// - ensures: `node` itself when no child changed, and a node minted
    ///   through the arena's constructors over the changed children otherwise —
    ///   so a decode whose code became a quote answers the quoted type. A leaf,
    ///   a linear occurrence and an unreadable node answer themselves.
    /// - provides: the combining half of the engine.
    /// - fails: never.
    /// - panics: none.
    fn close(
        &mut self,
        node: Node,
    ) -> Node
    {
        match node {
            | Node::Value(id) => Node::Value(self.close_value(id)),
            | Node::Computation(id) => Node::Computation(self.close_computation(id)),
            | Node::ValueType(id) => Node::ValueType(self.close_value_type(id)),
            | Node::CompType(id) => Node::CompType(self.close_comp_type(id)),
        }
    }

    /// Combine a value node.
    ///
    /// # Specification
    /// trivial.
    fn close_value(
        &mut self,
        id: ValueId,
    ) -> ValueId
    {
        let Some(node) = self.arena.value(id).cloned()
        else {
            return id;
        };
        match node {
            | Value::PathRefl(code) => {
                let rewritten = self.value(code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.value_path_refl(rewritten)
                }
            },
            | Value::PathProduct(first, second) => {
                let rewritten_second = self.value(second);
                let rewritten_first = self.value(first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena
                        .value_path_product(rewritten_first, rewritten_second)
                }
            },
            | Value::PathEquiv {
                path_type,
                forward,
                backward,
                evidence,
            } => {
                let rewritten_backward = self.value(backward);
                let rewritten_forward = self.value(forward);
                let rewritten_type = self.value_type(path_type);
                if (rewritten_type, rewritten_forward, rewritten_backward)
                    == (path_type, forward, backward)
                {
                    id
                }
                else {
                    self.arena.value_path_equiv(
                        rewritten_type,
                        rewritten_forward,
                        rewritten_backward,
                        evidence,
                    )
                }
            },
            | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => id,
            | Value::Pair(first, second) => {
                let rewritten_second = self.value(second);
                let rewritten_first = self.value(first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena.value_pair(rewritten_first, rewritten_second)
                }
            },
            | Value::Injection(side, body) => {
                let rewritten = self.value(body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_injection(side, rewritten)
                }
            },
            | Value::Thunk(body) => {
                let rewritten = self.computation(body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_thunk(rewritten)
                }
            },
            | Value::Lift { target, body } => {
                let rewritten = self.value(body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_lift(target, rewritten)
                }
            },
            | Value::Quote(quoted) => {
                let rewritten = self.value_type(quoted);
                if rewritten == quoted {
                    id
                }
                else {
                    self.arena.value_quote(rewritten)
                }
            },
            | Value::QuoteComputation(quoted) => {
                let rewritten = self.comp_type(quoted);
                if rewritten == quoted {
                    id
                }
                else {
                    self.arena.value_quote_computation(rewritten)
                }
            },
            | Value::StaticLambda(body) => {
                let rewritten = self.value(body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_static_lambda(rewritten)
                }
            },
            | Value::StaticApplication(head, argument) => {
                let rewritten_argument = self.value(argument);
                let rewritten_head = self.value(head);
                if (rewritten_head, rewritten_argument) == (head, argument) {
                    id
                }
                else {
                    self.arena
                        .value_static_application(rewritten_head, rewritten_argument)
                }
            },
        }
    }

    /// Combine a computation node.
    ///
    /// # Specification
    /// trivial.
    fn close_computation(
        &mut self,
        id: ComputationId,
    ) -> ComputationId
    {
        let Some(node) = self.arena.computation(id).cloned()
        else {
            return id;
        };
        match node {
            | Computation::Transport(path, value) => {
                let rewritten_value = self.value(value);
                let rewritten_path = self.value(path);
                if (rewritten_path, rewritten_value) == (path, value) {
                    id
                }
                else {
                    self.arena
                        .computation_transport(rewritten_path, rewritten_value)
                }
            },
            | Computation::Lambda(body) => {
                let rewritten = self.computation(body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.computation_lambda(rewritten)
                }
            },
            | Computation::Application(head, argument) => {
                let rewritten_argument = self.value(argument);
                let rewritten_head = self.computation(head);
                if (rewritten_head, rewritten_argument) == (head, argument) {
                    id
                }
                else {
                    self.arena
                        .computation_application(rewritten_head, rewritten_argument)
                }
            },
            | Computation::Return(value) => {
                let rewritten = self.value(value);
                if rewritten == value {
                    id
                }
                else {
                    self.arena.computation_return(rewritten)
                }
            },
            | Computation::Force(value) => {
                let rewritten = self.value(value);
                if rewritten == value {
                    id
                }
                else {
                    self.arena.computation_force(rewritten)
                }
            },
            | Computation::Bind(bound, body) => {
                let rewritten_body = self.computation(body);
                let rewritten_bound = self.computation(bound);
                if (rewritten_bound, rewritten_body) == (bound, body) {
                    id
                }
                else {
                    self.arena.computation_bind(rewritten_bound, rewritten_body)
                }
            },
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => {
                let rewritten_right = self.computation(on_right);
                let rewritten_left = self.computation(on_left);
                let rewritten_scrutinee = self.value(scrutinee);
                if (rewritten_scrutinee, rewritten_left, rewritten_right)
                    == (scrutinee, on_left, on_right)
                {
                    id
                }
                else {
                    self.arena.computation_case(
                        rewritten_scrutinee,
                        rewritten_left,
                        rewritten_right,
                    )
                }
            },
        }
    }

    /// Combine a value-type node.
    ///
    /// # Specification
    /// trivial.
    fn close_value_type(
        &mut self,
        id: ValueTypeId,
    ) -> ValueTypeId
    {
        let Some(node) = self.arena.value_type(id).cloned()
        else {
            return id;
        };
        match node {
            | ValueType::PathUniverse(source, target) => {
                let rewritten_target = self.value(target);
                let rewritten_source = self.value(source);
                if (rewritten_source, rewritten_target) == (source, target) {
                    id
                }
                else {
                    self.arena
                        .value_type_path_universe(rewritten_source, rewritten_target)
                }
            },
            | ValueType::Base(_)
            | ValueType::Unit
            | ValueType::Universe { .. }
            | ValueType::Abstract(_) => id,
            | ValueType::Product(first, second) => {
                let rewritten_second = self.value_type(second);
                let rewritten_first = self.value_type(first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena
                        .value_type_product(rewritten_first, rewritten_second)
                }
            },
            | ValueType::Sum(first, second) => {
                let rewritten_second = self.value_type(second);
                let rewritten_first = self.value_type(first);
                if (rewritten_first, rewritten_second) == (first, second) {
                    id
                }
                else {
                    self.arena.value_type_sum(rewritten_first, rewritten_second)
                }
            },
            | ValueType::Thunk(body) => {
                let rewritten = self.comp_type(body);
                if rewritten == body {
                    id
                }
                else {
                    self.arena.value_type_thunk(rewritten)
                }
            },
            | ValueType::Lift { inner, target } => {
                let rewritten = self.value_type(inner);
                if rewritten == inner {
                    id
                }
                else {
                    self.arena.value_type_lift(rewritten, target)
                }
            },
            | ValueType::Element { code, target } => {
                let rewritten = self.value(code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.value_type_element(rewritten, target)
                }
            },
            | ValueType::StaticPi { domain, codomain } => {
                let rewritten_codomain = self.value_type(codomain);
                let rewritten_domain = self.value_type(domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .value_type_static_pi(rewritten_domain, rewritten_codomain)
                }
            },
        }
    }

    /// Combine a computation-type node.
    ///
    /// # Specification
    /// trivial.
    fn close_comp_type(
        &mut self,
        id: CompTypeId,
    ) -> CompTypeId
    {
        let Some(node) = self.arena.comp_type(id).cloned()
        else {
            return id;
        };
        match node {
            | CompType::Returner(result) => {
                let rewritten = self.value_type(result);
                if rewritten == result {
                    id
                }
                else {
                    self.arena.comp_type_returner(rewritten)
                }
            },
            | CompType::Arrow { domain, codomain } => {
                let rewritten_codomain = self.comp_type(codomain);
                let rewritten_domain = self.value_type(domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .comp_type_arrow(rewritten_domain, rewritten_codomain)
                }
            },
            | CompType::Pi { domain, codomain } => {
                let rewritten_codomain = self.comp_type(codomain);
                let rewritten_domain = self.value_type(domain);
                if (rewritten_domain, rewritten_codomain) == (domain, codomain) {
                    id
                }
                else {
                    self.arena
                        .comp_type_pi(rewritten_domain, rewritten_codomain)
                }
            },
            | CompType::Element { code, target } => {
                let rewritten = self.value(code);
                if rewritten == code {
                    id
                }
                else {
                    self.arena.comp_type_element(rewritten, target)
                }
            },
        }
    }
}

/// Shift a value type `amount` binders deeper: every free intuitionistic index
/// rises by `amount`.
///
/// # Specification
/// - requires: `subject` names a value type of `arena`, formed in some context
///   `Γ`.
/// - ensures: the same type read in `Γ` extended by `amount` further binders;
///   `subject` itself when it is closed or `amount` is zero, so a closed type
///   costs no minting.
/// - provides: the read of a context slot's type at an occurrence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the shift agrees with a capture-free reference over
///   generated dependent types, on the lowering side of instantiation that
///   carries every replacement through it.
/// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
#[inline]
#[must_use]
pub fn shift_value_type(
    arena: &mut CoreArena,
    subject: ValueTypeId,
    amount: Binders,
) -> ValueTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(Node::ValueType(subject), Rewrite::Shift(amount)) {
        | Node::ValueType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::CompType(_) => subject,
    }
}

/// Shift a computation type `amount` binders deeper.
///
/// # Specification
/// - requires: `subject` names a computation type of `arena`, formed in some
///   context `Γ`.
/// - ensures: the same type read in `Γ` extended by `amount` further binders;
///   `subject` itself when it is closed or `amount` is zero.
/// - provides: the expected type a binder's body is checked against when the
///   binder does not scope the type.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — free and bound indices separated within one subject.
/// - witness: `rewrite::tests::shifting_raises_free_indices_and_spares_bound_ones`
#[inline]
#[must_use]
pub fn shift_comp_type(
    arena: &mut CoreArena,
    subject: CompTypeId,
    amount: Binders,
) -> CompTypeId
{
    if amount == Binders::NONE {
        return subject;
    }
    match Engine::new(arena).run(Node::CompType(subject), Rewrite::Shift(amount)) {
        | Node::CompType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => subject,
    }
}

/// Instantiate a dependent codomain at an argument: `C[v / x]`.
///
/// # Specification
/// - requires: `codomain` names a computation type of `arena` scoped under one
///   binder beyond some context `Γ`, and `argument` a value of `arena` in `Γ`.
/// - ensures: the codomain in `Γ`, with every occurrence of its binder replaced
///   by the argument carried under the binders it crosses, every index outside
///   the binder lowered by one, and every decode whose code became a quote read
///   as the quoted type.
/// - provides: the result type of applying a dependent arrow.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the machine agrees with a capture-free reference over
///   every generated dependent type of a bounded size, at arguments that are
///   themselves open.
/// - witness: `rewrite::tests::instantiating_a_codomain_avoids_capture`
/// - witness: `rewrite::tests::instantiating_a_decode_at_a_quote_decodes`
#[inline]
#[must_use]
pub fn instantiate_comp_type(
    arena: &mut CoreArena,
    codomain: CompTypeId,
    argument: ValueId,
) -> CompTypeId
{
    match Engine::new(arena).run(Node::CompType(codomain), Rewrite::Substitute(argument)) {
        | Node::CompType(id) => id,
        | Node::Value(_) | Node::Computation(_) | Node::ValueType(_) => codomain,
    }
}

/// Instantiate a value scoped under one binder at an argument: `v[a / x]`,
/// the reduct of a static redex `(λ. v) a`.
///
/// # Specification
/// - requires: `body` names a value of `arena` scoped under one binder beyond
///   some context `Γ`, and `argument` a value of `arena` in `Γ`.
/// - ensures: the body in `Γ`, with every occurrence of its binder replaced by
///   the argument carried under the binders it crosses, every index outside the
///   binder lowered by one, and every decode whose code became a quote read as
///   the quoted type; `body` itself when nothing in it changed.
/// - provides: the one substitution static beta takes, shared by the
///   normaliser's certificates and every walk that unfolds a static definition
///   at an instance.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the three substitution boundaries, each asserted as the
///   exact rewritten term: a free occurrence replaced, an occurrence under a
///   shadowing static lambda spared, and an open argument carried under a
///   binder without capture.
/// - witness: `rewrite::tests::substitution_replaces_a_free_occurrence`
/// - witness: `rewrite::tests::substitution_stops_at_a_shadowing_binder`
/// - witness: `rewrite::tests::substitution_avoids_capture`
#[inline]
#[must_use]
#[spec(ensures: |ret| ret == body || arena.value(ret).is_some())]
pub fn instantiate_value(
    arena: &mut CoreArena,
    body: ValueId,
    argument: ValueId,
) -> ValueId
{
    match Engine::new(arena).run(Node::Value(body), Rewrite::Substitute(argument)) {
        | Node::Value(id) => id,
        | Node::Computation(_) | Node::ValueType(_) | Node::CompType(_) => body,
    }
}

/// Lower a computation type out from under its innermost binder.
///
/// # Specification
/// - requires: `subject` names a computation type of `arena` formed in some
///   context `Γ` extended by one binder.
/// - ensures: the same type in `Γ`, every index outside the binder lowered by
///   one, when no occurrence names the binder;
///   [`strengthening::Absent::MentionsBinder`] when one does.
/// - provides: the result type of a bind or a case, synthesized under the
///   binder its continuation introduces.
/// - fails: never; a mention is a named absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type that mentions the binder and one that mentions
///   only an outer index separate the two answers.
/// - witness: `rewrite::tests::strengthening_refuses_a_mention_and_lowers_the_rest`
#[inline]
pub fn strengthen_comp_type(
    arena: &mut CoreArena,
    subject: CompTypeId,
) -> Maybe<CompTypeId, strengthening::Absent>
{
    let mut engine = Engine::new(arena);
    let lowered = engine.run(Node::CompType(subject), Rewrite::Lower);
    match (engine.mention, lowered) {
        | (Mention::Present, _) => Maybe::Absent(strengthening::Absent::MentionsBinder),
        | (Mention::Absent, Node::CompType(id)) => Maybe::Present(id),
        | (Mention::Absent, Node::Value(_) | Node::Computation(_) | Node::ValueType(_)) => {
            Maybe::Present(subject)
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use quenchant_shape::shape::Maybe;

    use super::Binders;
    use super::instantiate_comp_type;
    use super::instantiate_value;
    use super::shift_comp_type;
    use super::shift_value_type;
    use super::strengthen_comp_type;
    use super::strengthening;
    use crate::arena::CompTypeId;
    use crate::arena::CoreArena;
    use crate::arena::ValueId;
    use crate::arena::ValueTypeId;
    use crate::syntax::CompType;
    use crate::syntax::Value;
    use crate::syntax::ValueType;
    use crate::syntax::Zone;

    /// An intuitionistic occurrence at `index`.
    ///
    /// # Specification
    /// trivial.
    fn variable(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        arena.value_variable(Zone::Intuitionistic, index)
    }

    /// The value type `El x` at the variable `index`.
    ///
    /// # Specification
    /// trivial.
    fn decoded(
        arena: &mut CoreArena,
        index: DeBruijnIndex,
    ) -> ValueTypeId
    {
        let code = variable(arena, index);
        arena.value_type_element(code, Level::zero())
    }

    /// One token of a type's pre-order spelling.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Token
    {
        Returner,
        Arrow,
        Pi,
        CompElement,
        Base(BaseType),
        Element,
        Thunk,
        Product,
        Variable(u32),
        Constant(ConstantIndex),
        Pair,
        Quote,
        QuoteComputation,
        StaticLambda,
        StaticApplication,
        Other,
    }

    /// A node the spelling walk visits.
    #[derive(Clone, Copy)]
    enum Visit
    {
        Value(ValueId),
        ValueType(ValueTypeId),
        CompType(CompTypeId),
    }

    /// The pre-order spelling of a computation type, through the formers the
    /// generator writes: two types spell alike exactly when they are equal up
    /// to node identity.
    ///
    /// # Specification
    /// trivial.
    fn spelling(
        arena: &CoreArena,
        root: CompTypeId,
    ) -> Vec<Token>
    {
        spelling_of(arena, Visit::CompType(root))
    }

    /// The pre-order spelling of a value, through the formers the static
    /// tests write.
    ///
    /// # Specification
    /// trivial.
    fn value_spelling(
        arena: &CoreArena,
        root: ValueId,
    ) -> Vec<Token>
    {
        spelling_of(arena, Visit::Value(root))
    }

    /// The pre-order spelling of any node the walk visits.
    ///
    /// # Specification
    /// trivial.
    fn spelling_of(
        arena: &CoreArena,
        root: Visit,
    ) -> Vec<Token>
    {
        let mut tokens = Vec::new();
        let mut pending = vec![root];
        while let Some(visit) = pending.pop() {
            match visit {
                | Visit::CompType(id) => match arena.comp_type(id) {
                    | Some(&CompType::Returner(result)) => {
                        tokens.push(Token::Returner);
                        pending.push(Visit::ValueType(result));
                    },
                    | Some(&CompType::Arrow { domain, codomain }) => {
                        tokens.push(Token::Arrow);
                        pending.push(Visit::CompType(codomain));
                        pending.push(Visit::ValueType(domain));
                    },
                    | Some(&CompType::Pi { domain, codomain }) => {
                        tokens.push(Token::Pi);
                        pending.push(Visit::CompType(codomain));
                        pending.push(Visit::ValueType(domain));
                    },
                    | Some(&CompType::Element { code, .. }) => {
                        tokens.push(Token::CompElement);
                        pending.push(Visit::Value(code));
                    },
                    | None => tokens.push(Token::Other),
                },
                | Visit::ValueType(id) => match arena.value_type(id) {
                    | Some(&ValueType::Base(base)) => tokens.push(Token::Base(base)),
                    | Some(&ValueType::Element { code, .. }) => {
                        tokens.push(Token::Element);
                        pending.push(Visit::Value(code));
                    },
                    | Some(&ValueType::Thunk(body)) => {
                        tokens.push(Token::Thunk);
                        pending.push(Visit::CompType(body));
                    },
                    | Some(&ValueType::Product(first, second)) => {
                        tokens.push(Token::Product);
                        pending.push(Visit::ValueType(second));
                        pending.push(Visit::ValueType(first));
                    },
                    | Some(_) | None => tokens.push(Token::Other),
                },
                | Visit::Value(id) => match arena.value(id) {
                    | Some(&Value::Variable { index, .. }) => {
                        tokens.push(Token::Variable(u32::from(index)));
                    },
                    | Some(&Value::Constant(constant)) => tokens.push(Token::Constant(constant)),
                    | Some(&Value::Pair(first, second)) => {
                        tokens.push(Token::Pair);
                        pending.push(Visit::Value(second));
                        pending.push(Visit::Value(first));
                    },
                    | Some(&Value::Quote(quoted)) => {
                        tokens.push(Token::Quote);
                        pending.push(Visit::ValueType(quoted));
                    },
                    | Some(&Value::QuoteComputation(quoted)) => {
                        tokens.push(Token::QuoteComputation);
                        pending.push(Visit::CompType(quoted));
                    },
                    | Some(&Value::StaticLambda(body)) => {
                        tokens.push(Token::StaticLambda);
                        pending.push(Visit::Value(body));
                    },
                    | Some(&Value::StaticApplication(head, argument)) => {
                        tokens.push(Token::StaticApplication);
                        pending.push(Visit::Value(argument));
                        pending.push(Visit::Value(head));
                    },
                    | Some(_) | None => tokens.push(Token::Other),
                },
            }
        }
        tokens
    }

    /// What a generated node is.
    #[derive(Clone, Copy, Debug)]
    enum Shape
    {
        Returner,
        Arrow,
        Pi,
        CompElement,
        Integer,
        Element,
        Thunk,
        Product,
        /// A variable of the context the tree is placed in, by level: level
        /// zero is the outermost binder.
        Free(u32),
        /// A variable bound inside the tree, by level counted from the
        /// tree's own outermost binder.
        Local(u32),
        Quote,
        QuoteComputation,
    }

    /// What a pending slot of the generator must be filled with.
    #[derive(Clone, Copy, Debug)]
    enum Kind
    {
        Comp,
        ValueType,
        ValueCode,
        CompCode,
    }

    /// One generated node: its shape, its children in order, and how many of
    /// the tree's own binders stand above it.
    #[derive(Clone, Debug)]
    struct GeneratedNode
    {
        shape: Shape,
        children: Vec<usize>,
        binders: u32,
    }

    /// A generated tree, in pre-order: every child after its parent.
    #[repr(transparent)]
    #[derive(Clone, Debug, Default)]
    struct Tree
    {
        nodes: Vec<GeneratedNode>,
    }

    /// A count the generator draws, bounds or places by.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Count(u32);

    /// A deterministic xorshift stream.
    #[repr(transparent)]
    struct Stream(u64);

    impl Stream
    {
        /// The next draw below `bound`, which must be positive.
        ///
        /// # Specification
        /// trivial.
        fn below(
            &mut self,
            bound: Count,
        ) -> Count
        {
            self.0 ^= self.0.wrapping_shl(13);
            self.0 ^= self.0.wrapping_shr(7);
            self.0 ^= self.0.wrapping_shl(17);
            Count(u32::try_from(self.0.checked_rem(u64::from(bound.0)).unwrap()).unwrap())
        }
    }

    /// Generate a tree of `kind` whose free variables range over `frees`
    /// context levels, at most `fuel` formers deep.
    ///
    /// # Specification
    /// trivial.
    fn generate(
        stream: &mut Stream,
        kind: Kind,
        frees: Count,
        fuel: Count,
    ) -> Tree
    {
        let frees = frees.0;
        let mut tree = Tree::default();
        // (parent, kind, binders above, fuel left)
        let mut pending: Vec<(Option<usize>, Kind, u32, u32)> = vec![(None, kind, 0, fuel.0)];
        while let Some((parent, kind, binders, fuel)) = pending.pop() {
            let here = tree.nodes.len();
            if let Some(parent) = parent {
                tree.nodes[parent].children.push(here);
            }
            let variables = frees.checked_add(binders).unwrap();
            let leaf = fuel == 0;
            let less = fuel.saturating_sub(1);
            let variable_shape = |stream: &mut Stream| {
                let pick = stream.below(Count(variables)).0;
                if pick < frees {
                    Shape::Free(pick)
                }
                else {
                    Shape::Local(pick.checked_sub(frees).unwrap())
                }
            };
            // Children are pushed in reverse so they are generated in order.
            let (shape, children): (Shape, Vec<(Kind, u32)>) = match kind {
                | Kind::Comp => match (leaf, stream.below(Count(4)).0) {
                    | (true, _) | (false, 0) => (Shape::Returner, vec![(Kind::ValueType, binders)]),
                    | (false, 1) => (Shape::Arrow, vec![
                        (Kind::ValueType, binders),
                        (Kind::Comp, binders),
                    ]),
                    | (false, 2) => (Shape::Pi, vec![
                        (Kind::ValueType, binders),
                        (Kind::Comp, binders.checked_add(1).unwrap()),
                    ]),
                    | (false, _) => (Shape::CompElement, vec![(Kind::CompCode, binders)]),
                },
                | Kind::ValueType => match (leaf, stream.below(Count(4)).0) {
                    | (true, 0) | (_, 1) if variables > 0 => {
                        (Shape::Element, vec![(Kind::ValueCode, binders)])
                    },
                    | (true, _) => (Shape::Integer, Vec::new()),
                    | (false, 0) => (Shape::Thunk, vec![(Kind::Comp, binders)]),
                    | (false, 2) => (Shape::Product, vec![
                        (Kind::ValueType, binders),
                        (Kind::ValueType, binders),
                    ]),
                    | (false, _) => (Shape::Element, vec![(Kind::ValueCode, binders)]),
                },
                | Kind::ValueCode => match (leaf, stream.below(Count(3)).0) {
                    | (true, _) | (false, 0 | 1) if variables > 0 => {
                        (variable_shape(stream), Vec::new())
                    },
                    | (..) => (Shape::Quote, vec![(Kind::ValueType, binders)]),
                },
                | Kind::CompCode => match (leaf, stream.below(Count(3)).0) {
                    | (true, _) | (false, 0 | 1) if variables > 0 => {
                        (variable_shape(stream), Vec::new())
                    },
                    | (..) => (Shape::QuoteComputation, vec![(Kind::Comp, binders)]),
                },
            };
            tree.nodes.push(GeneratedNode {
                shape,
                children: Vec::new(),
                binders,
            });
            for &(child, child_binders) in children.iter().rev() {
                pending.push((Some(here), child, child_binders, less));
            }
        }
        tree
    }

    /// A node the builder minted.
    #[derive(Clone, Copy, Debug)]
    enum Built
    {
        Value(ValueId),
        ValueType(ValueTypeId),
        CompType(CompTypeId),
    }

    /// How the builder reads a free variable.
    #[derive(Clone, Copy)]
    enum Reading<'tree>
    {
        /// As an index at the depth it is reached at.
        Plain,
        /// The context level `binder` is replaced by the argument, built
        /// beforehand at every depth below the tree's own binders:
        /// `arguments[n]` stands under `n` of them. Levels past it drop by one.
        Spliced
        {
            binder: u32,
            arguments: &'tree [ValueId],
        },
    }

    /// Mint `tree` into `arena` with its root at absolute depth `placement`,
    /// reading free variables as `reading` says.
    ///
    /// # Specification
    /// trivial.
    fn build(
        arena: &mut CoreArena,
        tree: &Tree,
        placement: Count,
        reading: Reading<'_>,
    ) -> Built
    {
        let mut built: Vec<Option<Built>> = vec![None; tree.nodes.len()];
        for here in (0 .. tree.nodes.len()).rev() {
            let node = &tree.nodes[here];
            let depth = placement.0.checked_add(node.binders).unwrap();
            let child = |position: usize| built[node.children[position]].unwrap();
            let value_type = |position: usize| match child(position) {
                | Built::ValueType(id) => id,
                | Built::Value(_) | Built::CompType(_) => panic!("a value-type child"),
            };
            let comp_type = |position: usize| match child(position) {
                | Built::CompType(id) => id,
                | Built::Value(_) | Built::ValueType(_) => panic!("a computation-type child"),
            };
            let value = |position: usize| match child(position) {
                | Built::Value(id) => id,
                | Built::ValueType(_) | Built::CompType(_) => panic!("a value child"),
            };
            let minted = match node.shape {
                | Shape::Returner => Built::CompType(arena.comp_type_returner(value_type(0))),
                | Shape::Arrow => {
                    Built::CompType(arena.comp_type_arrow(value_type(0), comp_type(1)))
                },
                | Shape::Pi => Built::CompType(arena.comp_type_pi(value_type(0), comp_type(1))),
                | Shape::CompElement => {
                    Built::CompType(arena.comp_type_element(value(0), Level::zero()))
                },
                | Shape::Integer => Built::ValueType(arena.value_type_base(BaseType::Integer)),
                | Shape::Element => {
                    Built::ValueType(arena.value_type_element(value(0), Level::zero()))
                },
                | Shape::Thunk => Built::ValueType(arena.value_type_thunk(comp_type(0))),
                | Shape::Product => {
                    Built::ValueType(arena.value_type_product(value_type(0), value_type(1)))
                },
                | Shape::Quote => Built::Value(arena.value_quote(value_type(0))),
                | Shape::QuoteComputation => {
                    Built::Value(arena.value_quote_computation(comp_type(0)))
                },
                | Shape::Local(level) => {
                    let index = node
                        .binders
                        .checked_sub(1)
                        .unwrap()
                        .checked_sub(level)
                        .unwrap();
                    Built::Value(variable(arena, DeBruijnIndex::from(index)))
                },
                | Shape::Free(level) => match reading {
                    | Reading::Spliced { binder, arguments } if level == binder => {
                        Built::Value(arguments[usize::try_from(node.binders).unwrap()])
                    },
                    | Reading::Spliced { binder, .. } if level > binder => {
                        let lowered = level.checked_sub(1).unwrap();
                        let index = depth.checked_sub(1).unwrap().checked_sub(lowered).unwrap();
                        Built::Value(variable(arena, DeBruijnIndex::from(index)))
                    },
                    | Reading::Plain | Reading::Spliced { .. } => {
                        let index = depth.checked_sub(1).unwrap().checked_sub(level).unwrap();
                        Built::Value(variable(arena, DeBruijnIndex::from(index)))
                    },
                },
            };
            built[here] = Some(minted);
        }
        built[0].unwrap()
    }

    #[test]
    fn instantiating_a_codomain_avoids_capture()
    {
        let mut stream = Stream(0x9E37_79B9_7F4A_7C15);
        for round in 0 .. 600_u32 {
            let outer = round.checked_rem(3).unwrap();
            // The codomain reads the outer context and the dependent arrow's
            // own binder, at level `outer`; the argument reads the outer
            // context alone.
            let codomain = generate(
                &mut stream,
                Kind::Comp,
                Count(outer.checked_add(1).unwrap()),
                Count(4),
            );
            let argument = generate(&mut stream, Kind::ValueCode, Count(outer), Count(3));
            let mut arena = CoreArena::new();
            let Built::CompType(scoped) = build(
                &mut arena,
                &codomain,
                Count(outer.checked_add(1).unwrap()),
                Reading::Plain,
            )
            else {
                panic!("a computation type");
            };
            let Built::Value(supplied) = build(&mut arena, &argument, Count(outer), Reading::Plain)
            else {
                panic!("a value");
            };
            let machine = instantiate_comp_type(&mut arena, scoped, supplied);
            let deepest = codomain
                .nodes
                .iter()
                .map(|node| node.binders)
                .max()
                .unwrap();
            let arguments: Vec<ValueId> = (0 ..= deepest)
                .map(|binders| {
                    let placement = Count(outer.checked_add(binders).unwrap());
                    match build(&mut arena, &argument, placement, Reading::Plain) {
                        | Built::Value(id) => id,
                        | Built::ValueType(_) | Built::CompType(_) => panic!("a value"),
                    }
                })
                .collect();
            let Built::CompType(reference) =
                build(&mut arena, &codomain, Count(outer), Reading::Spliced {
                    binder: outer,
                    arguments: &arguments,
                })
            else {
                panic!("a computation type");
            };
            assert_eq!(
                spelling(&arena, reference),
                spelling(&arena, machine),
                "round {round}: the machine agrees with the capture-free reference for {codomain:?} at {argument:?}"
            );
        }
    }

    #[test]
    fn shifting_raises_free_indices_and_spares_bound_ones()
    {
        let mut arena = CoreArena::new();
        // Π (_ : El #0). El #0 → F (El #1): the domain's #0 is free, the
        // codomain's #0 is the arrow's own binder and its #1 is free.
        let domain = decoded(&mut arena, DeBruijnIndex::from(0));
        let bound = decoded(&mut arena, DeBruijnIndex::from(0));
        let free = decoded(&mut arena, DeBruijnIndex::from(1));
        let result = arena.comp_type_returner(free);
        let codomain = arena.comp_type_arrow(bound, result);
        let subject = arena.comp_type_pi(domain, codomain);
        let shifted = shift_comp_type(&mut arena, subject, Binders::from(2_u32));

        let expected_domain = decoded(&mut arena, DeBruijnIndex::from(2));
        let expected_bound = decoded(&mut arena, DeBruijnIndex::from(0));
        let expected_free = decoded(&mut arena, DeBruijnIndex::from(3));
        let expected_result = arena.comp_type_returner(expected_free);
        let expected_codomain = arena.comp_type_arrow(expected_bound, expected_result);
        let expected = arena.comp_type_pi(expected_domain, expected_codomain);
        assert_eq!(
            spelling(&arena, expected),
            spelling(&arena, shifted),
            "free indices rise by the amount and the bound one stands"
        );

        let integer = arena.value_type_base(BaseType::Integer);
        assert_eq!(
            integer,
            shift_value_type(&mut arena, integer, Binders::from(2_u32)),
            "a closed type shifts to itself"
        );
    }

    #[test]
    fn instantiating_a_decode_at_a_quote_decodes()
    {
        let mut arena = CoreArena::new();
        let decode = decoded(&mut arena, DeBruijnIndex::from(0));
        let codomain = arena.comp_type_returner(decode);
        let integer = arena.value_type_base(BaseType::Integer);
        let code = arena.value_quote(integer);
        let instantiated = instantiate_comp_type(&mut arena, codomain, code);
        assert_eq!(
            Some(&CompType::Returner(integer)),
            arena.comp_type(instantiated),
            "F (El x) at ⌜Integer⌝ is F Integer, with the decode read off the quote"
        );
    }

    #[test]
    fn strengthening_refuses_a_mention_and_lowers_the_rest()
    {
        let mut arena = CoreArena::new();
        let mentioning = decoded(&mut arena, DeBruijnIndex::from(0));
        let mentioning = arena.comp_type_returner(mentioning);
        assert_eq!(
            Maybe::Absent(strengthening::Absent::MentionsBinder),
            strengthen_comp_type(&mut arena, mentioning),
            "a type that reads the binder cannot leave it"
        );

        let outer = decoded(&mut arena, DeBruijnIndex::from(1));
        let outer = arena.comp_type_returner(outer);
        let Maybe::Present(lowered) = strengthen_comp_type(&mut arena, outer)
        else {
            panic!("a type that reads only an outer index leaves the binder");
        };
        let expected = decoded(&mut arena, DeBruijnIndex::from(0));
        let expected = arena.comp_type_returner(expected);
        assert_eq!(
            spelling(&arena, expected),
            spelling(&arena, lowered),
            "and its outer index lowers by one"
        );
    }

    #[test]
    fn a_shared_type_is_rewritten_once_per_node()
    {
        /// A product chain of sixty-four doublings over `El #index`, whose
        /// unfolding is exponential and whose node count is linear.
        ///
        /// # Specification
        /// trivial.
        fn chain(
            arena: &mut CoreArena,
            index: DeBruijnIndex,
        ) -> ValueTypeId
        {
            let mut shared = decoded(arena, index);
            for _ in 0 .. 64_u32 {
                shared = arena.value_type_product(shared, shared);
            }
            shared
        }

        let mut arena = CoreArena::new();
        let subject = chain(&mut arena, DeBruijnIndex::from(0));
        let shifted = shift_value_type(&mut arena, subject, Binders::ONE);
        assert_ne!(subject, shifted, "the free index was raised");

        let mut reference = CoreArena::new();
        let _original = chain(&mut reference, DeBruijnIndex::from(0));
        let _raised = chain(&mut reference, DeBruijnIndex::from(1));
        assert_eq!(
            reference.watermark(),
            arena.watermark(),
            "the shift minted exactly one more copy of the shared chain, never its unfolding"
        );
    }

    #[test]
    fn substitution_replaces_a_free_occurrence()
    {
        let mut arena = CoreArena::new();
        // F #0 #1 under one binder, at G: the binder's #0 becomes G and the
        // outer #1 lowers to #0.
        let operator = arena.value_constant(ConstantIndex::from(0_usize));
        let bound = variable(&mut arena, DeBruijnIndex::from(0));
        let outer = variable(&mut arena, DeBruijnIndex::from(1));
        let inner = arena.value_static_application(operator, bound);
        let body = arena.value_static_application(inner, outer);
        let argument = arena.value_constant(ConstantIndex::from(1_usize));
        let reduct = instantiate_value(&mut arena, body, argument);
        assert_eq!(
            vec![
                Token::StaticApplication,
                Token::StaticApplication,
                Token::Constant(ConstantIndex::from(0_usize)),
                Token::Constant(ConstantIndex::from(1_usize)),
                Token::Variable(0),
            ],
            value_spelling(&arena, reduct),
            "the free occurrence is the argument and the outer index lowers by one"
        );
    }

    #[test]
    fn substitution_stops_at_a_shadowing_binder()
    {
        let mut arena = CoreArena::new();
        // λ. ⟨#0, #1⟩ under one binder: the inner #0 is the lambda's own and
        // stays; the inner #1 is the substituted binder.
        let own = variable(&mut arena, DeBruijnIndex::from(0));
        let substituted = variable(&mut arena, DeBruijnIndex::from(1));
        let pair = arena.value_pair(own, substituted);
        let body = arena.value_static_lambda(pair);
        let argument = arena.value_constant(ConstantIndex::from(1_usize));
        let reduct = instantiate_value(&mut arena, body, argument);
        assert_eq!(
            vec![
                Token::StaticLambda,
                Token::Pair,
                Token::Variable(0),
                Token::Constant(ConstantIndex::from(1_usize)),
            ],
            value_spelling(&arena, reduct),
            "the shadowing lambda's own occurrence is spared"
        );

        let only_own = variable(&mut arena, DeBruijnIndex::from(0));
        let closed = arena.value_static_lambda(only_own);
        assert_eq!(
            closed,
            instantiate_value(&mut arena, closed, argument),
            "and a body that never reads the binder is returned as it stands"
        );
    }

    #[test]
    fn substitution_avoids_capture()
    {
        let mut arena = CoreArena::new();
        // λ. #1 under one binder, at the open argument #0: carried under the
        // lambda the argument is #1, not the lambda's own #0.
        let substituted = variable(&mut arena, DeBruijnIndex::from(1));
        let body = arena.value_static_lambda(substituted);
        let argument = variable(&mut arena, DeBruijnIndex::from(0));
        let reduct = instantiate_value(&mut arena, body, argument);
        assert_eq!(
            vec![Token::StaticLambda, Token::Variable(1)],
            value_spelling(&arena, reduct),
            "the open argument rises past the binder it crosses"
        );
    }
}
