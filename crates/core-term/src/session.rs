//! Binary session types: the protocol a linear endpoint follows, the endpoint
//! type that binds into the linear zone, and the actions that advance it.
//!
//! # A session type is the type of a linear endpoint
//!
//! A session type is two-sided, typestate-indexed codata whose observations
//! are sends, receives, selections and offers. Its former has six cases:
//!
//! |former|written|the endpoint that holds it|
//! |---|---|---|
//! |send|`!A. S`|sends a value of type `A`, continues as `S`|
//! |receive|`?A. S`|receives a value of type `A`, continues as `S`|
//! |select|`+{ l : S, … }`|chooses one label, continues as its branch|
//! |offer|`&{ l : S, … }`|the peer chooses; every label is handled|
//! |recursion|`mu t. S`|the fixed point, unfolded explicitly|
//! |end|`end`|closed|
//!
//! [`ValueType::Session`] is the endpoint type: a [`Protocol`] graph, the
//! payload types its sends and receives carry, and the state the endpoint
//! stands at. An endpoint is held in the linear zone `Σ` of the one
//! [`Context`], opened by [`SessionAction::Fork`] or by the receive of an
//! endpoint sent over another, so the zone's discipline — one consumption, no
//! weakening — is the endpoint's.
//!
//! # One protocol graph, a state into it
//!
//! A protocol is a flat, closed, contractive node list: recursion is a `Mu`
//! node and a `Recur` node naming its binder, so unfolding is a step to the
//! binder's body and never a substitution. The session type an action
//! advances to is the same protocol at another state, so advancing mints one
//! node and copies no syntax; payload types are the node's value-type
//! children, in slot order, which is how every binder rewrite, import and
//! content walk reaches them. [`SessionType::dual`] swaps send with receive
//! and select with offer and keeps the payloads, the binders and the state.
//!
//! **Choice.** One value-type former holding the protocol and a state.
//! **Alternatives.** A value-type former per session former, which adds six
//! arms to every walk and needs a substitution to unfold `mu`; a session
//! language beside the value types with its own arena family, which
//! duplicates every walk. **Reversal.** A consumer that rewrites inside a
//! protocol — a payload that binds, or protocol-level polymorphism — makes
//! the nodes arena children.
//!
//! # Contractivity at construction
//!
//! [`Protocol::new`] refuses a recursion whose body is another recursion or a
//! variable (`mu t. t`), a variable that names no enclosing binder, an edge
//! that names no node, a node reached twice and a node never reached, as
//! `gandr-core-session`'s engine does for its own syntax; a validated
//! protocol's head is therefore found in at most three steps.
//!
//! # An action rebinds the endpoint in place
//!
//! The actions are [`SessionAction`]: `send`, `recv`, `select`, `offer`,
//! `close`, each naming its endpoint by its linear de Bruijn index, and
//! `fork`, which binds the two ends. No action returns an endpoint: the
//! checker rebinds the endpoint's slot at its continuation type, as
//! [`Context::advance`] states, and `close` consumes it. `send`, `select`
//! and `close` return the unit. `recv` carries the rest of its block as its
//! body, under one linear binder that holds the payload, as `fork` carries
//! its parent: a received endpoint is a linear resident like the ends a fork
//! binds, and the checker places every other payload in that slot too, read
//! by copy. The alternative was pair-returning actions, `(x, c′) = recv c`,
//! which needs a binding form per action and a fresh name per step.
//!
//! **Choice.** One computation former whose cases are the six actions, the
//! subject an index rather than a value, so an action on something that is
//! not an endpoint cannot be written. **Alternative.** A computation former
//! per action, which adds an arm per action to every walk.
//!
//! [`Context`]: crate::Context
//! [`Context::advance`]: crate::Context::advance
//! [`ValueType::Session`]: crate::ValueType::Session

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use quenchant_shape::shape::Maybe;

use crate::Computation;
use crate::ComputationId;
use crate::CoreArena;
use crate::ValueId;
use crate::ValueType;
use crate::ValueTypeId;

/// A position in one protocol's node list: a state of the session.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProtocolState(usize);

impl From<usize> for ProtocolState
{
    /// The state at node position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<ProtocolState> for usize
{
    /// The node position of `state`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(state: ProtocolState) -> Self
    {
        state.0
    }
}

/// The position of one payload type among a session type's payloads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PayloadSlot(usize);

impl From<usize> for PayloadSlot
{
    /// The slot at position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<PayloadSlot> for usize
{
    /// The position of `slot`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slot: PayloadSlot) -> Self
    {
        slot.0
    }
}

/// How many payload types a protocol's sends and receives read.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PayloadCount(usize);

impl From<usize> for PayloadCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<PayloadCount> for usize
{
    /// The number `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: PayloadCount) -> Self
    {
        count.0
    }
}

/// How many recursion binders a written recursion variable counts outward
/// past: zero names the innermost enclosing `mu`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecursionIndex(usize);

impl From<usize> for RecursionIndex
{
    /// The variable counting `binders` binders outward.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(binders: usize) -> Self
    {
        Self(binders)
    }
}

impl From<RecursionIndex> for usize
{
    /// How many binders `index` counts outward past.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: RecursionIndex) -> Self
    {
        index.0
    }
}

/// One node of protocol syntax as a producer writes it, its recursion
/// variables counted outward over the enclosing `mu` binders.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ProtocolSyntax
{
    /// `!A. S`: send the payload in `payload`, continue at `next`.
    Send
    {
        /// The payload type's slot.
        payload: PayloadSlot,
        /// The continuation.
        next: ProtocolState,
    },
    /// `?A. S`: receive the payload in `payload`, continue at `next`.
    Receive
    {
        /// The payload type's slot.
        payload: PayloadSlot,
        /// The continuation.
        next: ProtocolState,
    },
    /// `+{ l : S, … }`: choose one label.
    Select(BTreeMap<FieldLabel, ProtocolState>),
    /// `&{ l : S, … }`: handle the label the peer chooses.
    Offer(BTreeMap<FieldLabel, ProtocolState>),
    /// `end`: closed.
    End,
    /// `mu t. S`: the fixed point of its body.
    Mu(ProtocolState),
    /// `t`: the enclosing `mu` the index counts out to.
    Recur(RecursionIndex),
}

/// One node of a validated protocol: a recursion variable names its binder.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ProtocolNode
{
    /// Send the payload in `payload`, continue at `next`.
    Send
    {
        /// The payload type's slot.
        payload: PayloadSlot,
        /// The continuation.
        next: ProtocolState,
    },
    /// Receive the payload in `payload`, continue at `next`.
    Receive
    {
        /// The payload type's slot.
        payload: PayloadSlot,
        /// The continuation.
        next: ProtocolState,
    },
    /// Choose one label.
    Select(BTreeMap<FieldLabel, ProtocolState>),
    /// Handle the label the peer chooses.
    Offer(BTreeMap<FieldLabel, ProtocolState>),
    /// Closed.
    End,
    /// The fixed point of its body.
    Mu(ProtocolState),
    /// The `Mu` node it unfolds to.
    Recur(ProtocolState),
}

/// Why a protocol, or a session type over one, is malformed.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ProtocolError
{
    /// An edge or the root names no node.
    MissingNode(ProtocolState),
    /// A node is reached twice; recursion is written with `Recur`.
    RepeatedNode(ProtocolState),
    /// A recursion variable counts past every enclosing `mu`.
    UnboundRecursion(ProtocolState),
    /// A `mu` whose body is a `mu` or a recursion variable: `mu t. t`.
    NonContractive(ProtocolState),
    /// A node the root does not reach.
    UnreachableNode(ProtocolState),
    /// A send or receive names a payload slot past the protocol's count.
    MissingPayload(PayloadSlot),
    /// A session type supplies a number of payload types other than its
    /// protocol reads.
    PayloadCount
    {
        /// The number the protocol reads.
        expected: PayloadCount,
        /// The number supplied.
        found: PayloadCount,
    },
}

impl core::fmt::Display for ProtocolError
{
    /// Describe the malformation and the node or slot it is at.
    ///
    /// # Specification
    /// - ensures: writes the refused construction rule and its position.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable sink.
    ///
    /// # Errors
    /// Returns the formatter's error when its sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders its own rule and position.
    /// - witness: `session::tests::every_malformation_renders_its_rule`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::MissingNode(ProtocolState(at)) => write!(f, "missing protocol node {at}"),
            Self::RepeatedNode(ProtocolState(at)) => {
                write!(f, "protocol node {at} reached twice")
            },
            Self::UnboundRecursion(ProtocolState(at)) => {
                write!(f, "unbound recursion variable at node {at}")
            },
            Self::NonContractive(ProtocolState(at)) => {
                write!(f, "non-contractive recursion at node {at}")
            },
            Self::UnreachableNode(ProtocolState(at)) => {
                write!(f, "protocol node {at} is unreachable")
            },
            Self::MissingPayload(PayloadSlot(slot)) => write!(f, "missing payload slot {slot}"),
            Self::PayloadCount { expected, found } => write!(
                f,
                "the protocol reads {} payload types, {} supplied",
                expected.0, found.0
            ),
        }
    }
}

impl core::error::Error for ProtocolError
{
}

/// A validation obligation; leaving a binder restores the enclosing scope.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// Validate a node.
    Enter(ProtocolState),
    /// Drop the `mu` binder whose body has been validated.
    Leave,
}

/// A closed, contractive binary protocol: a flat node list and its root.
///
/// # Specification
/// - provides: every node reachable once from the root; every `Recur` names an
///   enclosing `Mu`; every `Mu` body is an action or `End`; every payload slot
///   is below the payload count.
/// - panics: none.
/// - executable: none — the invariant is established by [`Protocol::new`] and
///   preserved by [`Protocol::dual`]; a type has no call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — malformed lists distinguish each refusal by its exact
///   variant, and nested binders resolve each variable to its own binder.
/// - witness: `session::tests::malformed_protocols_are_refused_by_rule`
/// - witness: `session::tests::recursion_variables_resolve_to_their_own_binder`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Protocol
{
    /// The nodes, addressed by [`ProtocolState`].
    nodes: Box<[ProtocolNode]>,
    /// The state a fresh endpoint stands at.
    root: ProtocolState,
    /// How many payload types the sends and receives read.
    payloads: PayloadCount,
}

impl Protocol
{
    /// Validate written protocol syntax and resolve its recursion variables.
    ///
    /// # Specification
    /// - requires: nothing — malformed syntax is admissible input and is
    ///   refused.
    /// - ensures: a protocol of the same nodes and root, each `Recur` naming
    ///   the `Mu` its index counts out to.
    /// - fails: [`ProtocolError::MissingNode`] for an edge or root past the
    ///   list; [`ProtocolError::RepeatedNode`] for a node reached twice;
    ///   [`ProtocolError::UnboundRecursion`] for a variable past every binder;
    ///   [`ProtocolError::NonContractive`] for a `mu` whose body is a `mu` or a
    ///   variable; [`ProtocolError::MissingPayload`] for a slot at or past
    ///   `payloads`; [`ProtocolError::UnreachableNode`] for a node the root
    ///   does not reach.
    /// - panics: none.
    ///
    /// # Errors
    /// The first [`ProtocolError`] met, in the walk's order.
    ///
    /// # Termination
    /// - reason: the `while let` pops one visit per iteration.
    /// - measure: the visits pending plus twice the nodes not yet entered.
    /// - boundedness: a node entered twice is refused, so each node pushes its
    ///   children once.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one list per refusal, each asserted by exact variant
    ///   and position, and nested binders observed through the resolved
    ///   variables.
    /// - witness: `session::tests::malformed_protocols_are_refused_by_rule`
    /// - witness: `session::tests::recursion_variables_resolve_to_their_own_binder`
    #[spec(
        captures: [count = syntax.len()],
        ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|protocol| {
            protocol.nodes.len() == count && protocol.root == root && protocol.payloads == payloads
                && protocol.nodes.iter().all(|node| match *node {
                    | ProtocolNode::Mu(body) => protocol.nodes.get(body.0).is_some_and(|body|
                        !matches!(*body, ProtocolNode::Mu(_) | ProtocolNode::Recur(_))),
                    | ProtocolNode::Recur(binder) => matches!(protocol.nodes.get(binder.0), Some(ProtocolNode::Mu(_))),
                    | ProtocolNode::Send { payload, .. } | ProtocolNode::Receive { payload, .. } => payload.0 < payloads.0,
                    | ProtocolNode::Select(_) | ProtocolNode::Offer(_) | ProtocolNode::End => true,
                })
        })
    )]
    #[inline]
    pub fn new(
        syntax: Vec<ProtocolSyntax>,
        root: ProtocolState,
        payloads: PayloadCount,
    ) -> Result<Self, ProtocolError>
    {
        let mut seen = BTreeSet::new();
        let mut binders: Vec<ProtocolState> = Vec::new();
        let mut resolved = BTreeMap::new();
        let mut pending = alloc::vec![Visit::Enter(root)];
        while let Some(visit) = pending.pop() {
            let state = match visit {
                Visit::Leave => {
                    let _binder = binders.pop();
                    continue;
                },
                Visit::Enter(state) => state,
            };
            let node = syntax
                .get(state.0)
                .ok_or(ProtocolError::MissingNode(state))?;
            if !seen.insert(state) {
                return Err(ProtocolError::RepeatedNode(state));
            }
            match *node {
                ProtocolSyntax::Send { payload, next }
                | ProtocolSyntax::Receive { payload, next } => {
                    if payload.0 >= payloads.0 {
                        return Err(ProtocolError::MissingPayload(payload));
                    }
                    pending.push(Visit::Enter(next));
                },
                ProtocolSyntax::Select(ref branches) | ProtocolSyntax::Offer(ref branches) => {
                    pending.extend(branches.values().copied().map(Visit::Enter));
                },
                ProtocolSyntax::End => {},
                ProtocolSyntax::Mu(body) => {
                    let written = syntax.get(body.0).ok_or(ProtocolError::MissingNode(body))?;
                    if matches!(*written, ProtocolSyntax::Mu(_) | ProtocolSyntax::Recur(_)) {
                        return Err(ProtocolError::NonContractive(state));
                    }
                    binders.push(state);
                    pending.push(Visit::Leave);
                    pending.push(Visit::Enter(body));
                },
                ProtocolSyntax::Recur(RecursionIndex(outward)) => {
                    let binder = binders
                        .len()
                        .checked_sub(outward)
                        .and_then(|above| above.checked_sub(1_usize))
                        .and_then(|position| binders.get(position))
                        .copied()
                        .ok_or(ProtocolError::UnboundRecursion(state))?;
                    let _first = resolved.insert(state, binder);
                },
            }
        }
        if let Some(unreached) = (0 .. syntax.len())
            .map(ProtocolState)
            .find(|state| !seen.contains(state))
        {
            return Err(ProtocolError::UnreachableNode(unreached));
        }
        let mut nodes = Vec::with_capacity(syntax.len());
        for (position, written) in syntax.into_iter().enumerate() {
            nodes.push(match written {
                ProtocolSyntax::Send { payload, next } => ProtocolNode::Send { payload, next },
                ProtocolSyntax::Receive { payload, next } => {
                    ProtocolNode::Receive { payload, next }
                },
                ProtocolSyntax::Select(branches) => ProtocolNode::Select(branches),
                ProtocolSyntax::Offer(branches) => ProtocolNode::Offer(branches),
                ProtocolSyntax::End => ProtocolNode::End,
                ProtocolSyntax::Mu(body) => ProtocolNode::Mu(body),
                ProtocolSyntax::Recur(_) => ProtocolNode::Recur(
                    resolved
                        .get(&ProtocolState(position))
                        .copied()
                        .ok_or(ProtocolError::UnboundRecursion(ProtocolState(position)))?,
                ),
            });
        }
        Ok(Self {
            nodes: nodes.into_boxed_slice(),
            root,
            payloads,
        })
    }

    /// The state a fresh endpoint stands at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> ProtocolState
    {
        self.root
    }

    /// How many payload types the protocol's sends and receives read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn payload_count(&self) -> PayloadCount
    {
        self.payloads
    }

    /// The nodes, in [`ProtocolState`] order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ProtocolNode]
    {
        &self.nodes
    }

    /// The written form: the nodes in [`ProtocolState`] order, each `Recur`
    /// counting out to its binder again.
    ///
    /// # Specification
    /// - ensures: one written node per node; [`Protocol::new`] over the written
    ///   form, this root and this payload count gives this protocol back. A
    ///   persisted protocol is stored in this form, so the one validating
    ///   constructor reads it back.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let` pops one visit per iteration.
    /// - measure: the visits pending plus twice the nodes not yet entered.
    /// - boundedness: the invariant reaches each node once from the root, so
    ///   each node pushes its children once.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested binders write each variable's own count, and
    ///   the written form validates to the same protocol.
    /// - witness: `session::tests::recursion_variables_resolve_to_their_own_binder`
    #[spec(ensures: |ret| ret.len() == self.nodes.len())]
    #[inline]
    #[must_use]
    pub fn syntax(&self) -> Vec<ProtocolSyntax>
    {
        let mut written: Vec<ProtocolSyntax> = self
            .nodes
            .iter()
            .map(|node| match *node {
                ProtocolNode::Send { payload, next } => ProtocolSyntax::Send { payload, next },
                ProtocolNode::Receive { payload, next } => {
                    ProtocolSyntax::Receive { payload, next }
                },
                ProtocolNode::Select(ref branches) => ProtocolSyntax::Select(branches.clone()),
                ProtocolNode::Offer(ref branches) => ProtocolSyntax::Offer(branches.clone()),
                ProtocolNode::End => ProtocolSyntax::End,
                ProtocolNode::Mu(body) => ProtocolSyntax::Mu(body),
                ProtocolNode::Recur(_) => ProtocolSyntax::Recur(RecursionIndex::default()),
            })
            .collect();
        let mut binders: Vec<ProtocolState> = Vec::new();
        let mut pending = alloc::vec![Visit::Enter(self.root)];
        while let Some(visit) = pending.pop() {
            let state = match visit {
                Visit::Leave => {
                    let _binder = binders.pop();
                    continue;
                },
                Visit::Enter(state) => state,
            };
            match self.nodes.get(state.0) {
                Some(&ProtocolNode::Send { next, .. } | &ProtocolNode::Receive { next, .. }) => {
                    pending.push(Visit::Enter(next));
                },
                Some(&(ProtocolNode::Select(ref branches) | ProtocolNode::Offer(ref branches))) => {
                    pending.extend(branches.values().copied().map(Visit::Enter));
                },
                Some(&ProtocolNode::Mu(body)) => {
                    binders.push(state);
                    pending.push(Visit::Leave);
                    pending.push(Visit::Enter(body));
                },
                Some(&ProtocolNode::Recur(binder)) => {
                    let outward = binders
                        .iter()
                        .rev()
                        .position(|&enclosing| enclosing == binder);
                    if let (Some(outward), Some(slot)) = (outward, written.get_mut(state.0)) {
                        *slot = ProtocolSyntax::Recur(RecursionIndex(outward));
                    }
                },
                Some(&ProtocolNode::End) | None => {},
            }
        }
        written
    }

    /// The node at `state`.
    ///
    /// # Specification
    /// - requires: nothing — a state past the list is admissible input.
    /// - ensures: exactly the node at `state`.
    /// - fails: [`ProtocolError::MissingNode`] for a state past the list.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ProtocolError::MissingNode`] naming `state`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the root and a state past the list separate the
    ///   bound.
    /// - witness: `session::tests::states_past_the_protocol_are_refused`
    #[spec(ensures: |ret| match (self.nodes.get(state.0), ret) {
        | (Some(expected), Ok(actual)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(actual)),
        | (None, Err(ProtocolError::MissingNode(missing))) => missing == state,
        | _ => false,
    })]
    #[inline]
    pub fn node(
        &self,
        state: ProtocolState,
    ) -> Result<&ProtocolNode, ProtocolError>
    {
        self.nodes
            .get(state.0)
            .ok_or(ProtocolError::MissingNode(state))
    }

    /// The observable node `state` unfolds to, and its state.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `Mu` reads as its body and a `Recur` as its binder's body,
    ///   so the node returned is an action or `End`.
    /// - fails: [`ProtocolError::MissingNode`] for a state past the list.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`ProtocolError`] of the first state that names no node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `Mu`, a `Recur` and an action each reach the
    ///   observable node by their own number of steps.
    /// - witness: `session::tests::recursion_variables_resolve_to_their_own_binder`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|&(_, node)|
        !matches!(*node, ProtocolNode::Mu(_) | ProtocolNode::Recur(_))))]
    #[inline]
    pub fn head(
        &self,
        state: ProtocolState,
    ) -> Result<(ProtocolState, &ProtocolNode), ProtocolError>
    {
        // A contractive protocol reaches an action from a `Recur` through
        // its `Mu` in two steps, so the third read is observable.
        let mut current = state;
        for _step in 0 .. 3_u8 {
            match *self.node(current)? {
                ProtocolNode::Mu(next) | ProtocolNode::Recur(next) => current = next,
                ref observable @ (ProtocolNode::Send { .. }
                | ProtocolNode::Receive { .. }
                | ProtocolNode::Select(_)
                | ProtocolNode::Offer(_)
                | ProtocolNode::End) => return Ok((current, observable)),
            }
        }
        Err(ProtocolError::NonContractive(current))
    }

    /// The protocol the peer follows: every send a receive, every selection an
    /// offer, and the reverse.
    ///
    /// # Specification
    /// - ensures: node for node, send and receive swap and select and offer
    ///   swap; payload slots, continuations, labels, binders, `End` and the
    ///   root are kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a protocol with every former is dualised node for
    ///   node, and dualising twice gives the protocol back.
    /// - witness: `session::tests::dual_swaps_every_action_and_keeps_the_rest`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body maps every node once; the check compares each once"
        )
    )]
    #[spec(ensures: |ret| ret.root == self.root && ret.payloads == self.payloads
        && ret.nodes.len() == self.nodes.len()
        && self.nodes.iter().zip(ret.nodes.iter()).all(|(own, peer)| match (own, peer) {
            | (&ProtocolNode::Send { payload: a, next: x }, &ProtocolNode::Receive { payload: b, next: y })
            | (&ProtocolNode::Receive { payload: a, next: x }, &ProtocolNode::Send { payload: b, next: y }) => a == b && x == y,
            | (&ProtocolNode::Select(ref a), &ProtocolNode::Offer(ref b))
            | (&ProtocolNode::Offer(ref a), &ProtocolNode::Select(ref b)) => a == b,
            | (&ProtocolNode::Mu(a), &ProtocolNode::Mu(b)) | (&ProtocolNode::Recur(a), &ProtocolNode::Recur(b)) => a == b,
            | (&ProtocolNode::End, &ProtocolNode::End) => true,
            | _ => false,
        }))]
    #[inline]
    #[must_use]
    pub fn dual(&self) -> Self
    {
        let nodes = self
            .nodes
            .iter()
            .map(|node| match *node {
                ProtocolNode::Send { payload, next } => ProtocolNode::Receive { payload, next },
                ProtocolNode::Receive { payload, next } => ProtocolNode::Send { payload, next },
                ProtocolNode::Select(ref branches) => ProtocolNode::Offer(branches.clone()),
                ProtocolNode::Offer(ref branches) => ProtocolNode::Select(branches.clone()),
                ProtocolNode::End => ProtocolNode::End,
                ProtocolNode::Mu(body) => ProtocolNode::Mu(body),
                ProtocolNode::Recur(binder) => ProtocolNode::Recur(binder),
            })
            .collect();
        Self {
            nodes,
            root: self.root,
            payloads: self.payloads,
        }
    }
}

/// The action an endpoint takes, or the action a session state admits.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ActionKind
{
    /// Send a payload.
    Send,
    /// Receive a payload.
    Receive,
    /// Choose a label.
    Select,
    /// Handle the peer's label.
    Offer,
    /// Close the endpoint.
    Close,
}

/// The order a walk visits a node's children in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ChildOrder
{
    /// The canonical order: a fork's protocol, a payload, the arms in label
    /// order, a fork's child before its parent; payload slots ascending.
    Forward,
    /// The canonical order reversed, for a walk that pops a result stack.
    Reverse,
}

/// The type of an endpoint: a protocol, the payload types its sends and
/// receives carry, and the state the endpoint stands at.
///
/// # Specification
/// - provides: the payloads number exactly what the protocol reads, and the
///   state names a node of the protocol.
/// - panics: none.
/// - executable: none — the invariant is established by [`SessionType::new`]
///   and kept by every state move and payload map.
///
/// # Adequacy
/// - hypothesis: L3 — a payload list of the wrong length and a state past the
///   protocol are refused by exact variant.
/// - witness: `session::tests::states_past_the_protocol_are_refused`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SessionType<Id = ValueTypeId>
{
    /// The protocol, shared by every state of one endpoint and its peer's.
    protocol: Arc<Protocol>,
    /// The payload types, in slot order.
    payloads: Arc<[Id]>,
    /// The state the endpoint stands at.
    state: ProtocolState,
}

impl<Id: Copy> SessionType<Id>
{
    /// The session type at `protocol`'s root, reading `payloads`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the state is the protocol's root and the payloads are kept in
    ///   order.
    /// - fails: [`ProtocolError::PayloadCount`] when `payloads` does not number
    ///   what the protocol reads.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ProtocolError::PayloadCount`] with both counts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one payload short and the exact count separate the
    ///   check.
    /// - witness: `session::tests::states_past_the_protocol_are_refused`
    #[spec(
        captures: [root = protocol.root, reads = protocol.payloads, supplied = payloads.len()],
        ensures: |ret| match ret {
            | Ok(ref session) => session.state == root && session.payloads.len() == supplied,
            | Err(ProtocolError::PayloadCount { expected, found }) => expected == reads && found.0 == supplied && found != expected,
            | Err(_) => false,
        },
    )]
    #[inline]
    pub fn new(
        protocol: Arc<Protocol>,
        payloads: Arc<[Id]>,
    ) -> Result<Self, ProtocolError>
    {
        let found = PayloadCount(payloads.len());
        if found != protocol.payloads {
            return Err(ProtocolError::PayloadCount {
                expected: protocol.payloads,
                found,
            });
        }
        let state = protocol.root;
        Ok(Self {
            protocol,
            payloads,
            state,
        })
    }

    /// The protocol.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn protocol(&self) -> &Protocol
    {
        &self.protocol
    }

    /// The payload types, in slot order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn payloads(&self) -> &[Id]
    {
        &self.payloads
    }

    /// The state the endpoint stands at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn state(&self) -> ProtocolState
    {
        self.state
    }

    /// The same protocol and payloads at `state`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the protocol and payloads are shared, and the state is
    ///   `state`.
    /// - fails: [`ProtocolError::MissingNode`] for a state past the protocol.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ProtocolError::MissingNode`] naming `state`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the last node and the first state past it separate
    ///   the bound.
    /// - witness: `session::tests::states_past_the_protocol_are_refused`
    #[spec(ensures: |ret| match ret {
        | Ok(ref moved) => moved.state == state && Arc::ptr_eq(&moved.protocol, &self.protocol),
        | Err(error) => error == ProtocolError::MissingNode(state),
    })]
    #[inline]
    pub fn at(
        &self,
        state: ProtocolState,
    ) -> Result<Self, ProtocolError>
    {
        let _node = self.protocol.node(state)?;
        Ok(Self {
            protocol: Arc::clone(&self.protocol),
            payloads: Arc::clone(&self.payloads),
            state,
        })
    }

    /// The peer's session type: the dual protocol at the same state.
    ///
    /// # Specification
    /// - ensures: the protocol is [`Protocol::dual`] of this one; the payloads
    ///   and the state are kept.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the seat's session type and its operator's are each
    ///   other's dual, observed through the step each admits.
    /// - witness: `session::tests::dual_swaps_every_action_and_keeps_the_rest`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body dualises every node of the protocol once; the check dualises them once more and compares each once"
        )
    )]
    #[spec(ensures: |ret| ret.state == self.state && *ret.protocol == self.protocol.dual())]
    #[inline]
    #[must_use]
    pub fn dual(&self) -> Self
    {
        Self {
            protocol: Arc::new(self.protocol.dual()),
            payloads: Arc::clone(&self.payloads),
            state: self.state,
        }
    }

    /// What the endpoint at this state does next.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the state is unfolded past `mu` and its variables, and the
    ///   observable node read: a send or receive with its payload type and
    ///   continuation, a selection or offer with its branches, or `End`.
    /// - fails: [`ProtocolError::MissingNode`] or
    ///   [`ProtocolError::MissingPayload`] only for a session type that broke
    ///   its own invariant.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`ProtocolError`] of the broken reference.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every former is stepped, a recursion unfolds to its
    ///   body, and each continuation is asserted by state.
    /// - witness: `session::tests::stepping_reads_each_former_and_unfolds_recursion`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|step| match *step {
        | Step::Send { ref next, .. } | Step::Receive { ref next, .. } => Arc::ptr_eq(&next.protocol, &self.protocol),
        | Step::Select(ref branches) | Step::Offer(ref branches) => core::ptr::eq(core::ptr::from_ref(branches.session), core::ptr::from_ref(self)),
        | Step::End => true,
    }))]
    #[inline]
    pub fn step(&self) -> Result<Step<'_, Id>, ProtocolError>
    {
        let (_, node) = self.protocol.head(self.state)?;
        Ok(match *node {
            ProtocolNode::Send { payload, next } => Step::Send {
                payload: self.payload(payload)?,
                next: self.at(next)?,
            },
            ProtocolNode::Receive { payload, next } => Step::Receive {
                payload: self.payload(payload)?,
                next: self.at(next)?,
            },
            ProtocolNode::Select(ref branches) => Step::Select(Branches {
                session: self,
                branches,
            }),
            ProtocolNode::Offer(ref branches) => Step::Offer(Branches {
                session: self,
                branches,
            }),
            ProtocolNode::End => Step::End,
            ProtocolNode::Mu(_) | ProtocolNode::Recur(_) => {
                return Err(ProtocolError::NonContractive(self.state));
            },
        })
    }

    /// The payload type in `slot`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the payload at `slot`.
    /// - fails: [`ProtocolError::MissingPayload`] for a slot past the list.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ProtocolError::MissingPayload`] naming `slot`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a send's payload is read from its own slot.
    /// - witness: `session::tests::stepping_reads_each_former_and_unfolds_recursion`
    #[spec(ensures: |ret| match ret {
        | Ok(_) => slot.0 < self.payloads.len(),
        | Err(error) => error == ProtocolError::MissingPayload(slot),
    })]
    fn payload(
        &self,
        slot: PayloadSlot,
    ) -> Result<Id, ProtocolError>
    {
        self.payloads
            .get(slot.0)
            .copied()
            .ok_or(ProtocolError::MissingPayload(slot))
    }

    /// Rewrite every payload type through `map`, visiting slots in `order`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the protocol and the state are kept and each slot holds its
    ///   payload's image; an unchanged image keeps the payload list.
    /// - fails: propagates the first error `map` returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error of `map`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two distinct payloads mapped in reverse order land in
    ///   their own slots.
    /// - witness: `session::tests::payload_maps_keep_slots_in_either_order`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped|
        mapped.state == self.state && Arc::ptr_eq(&mapped.protocol, &self.protocol)
            && mapped.payloads.len() == self.payloads.len()))]
    #[inline]
    pub fn try_map_payloads<E, Map>(
        &self,
        order: ChildOrder,
        map: Map,
    ) -> Result<Self, E>
    where
        Id: Eq,
        Map: FnMut(Id) -> Result<Id, E>,
    {
        let payloads = mapped(&self.payloads, order, map)?;
        if *payloads == *self.payloads {
            return Ok(self.clone());
        }
        Ok(Self {
            protocol: Arc::clone(&self.protocol),
            payloads,
            state: self.state,
        })
    }

    /// The same session type over payload handles of another family.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the protocol and the state are kept and each slot holds its
    ///   payload's image, visited in slot order.
    /// - fails: propagates the first error `map` returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error of `map`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — relocating to positions and back is the identity on
    ///   the payloads.
    /// - witness: `session::tests::payload_maps_keep_slots_in_either_order`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped|
        mapped.state == self.state && mapped.payloads.len() == self.payloads.len()))]
    #[inline]
    pub fn try_relocate<To, E, Map>(
        &self,
        map: Map,
    ) -> Result<SessionType<To>, E>
    where
        To: Copy,
        Map: FnMut(Id) -> Result<To, E>,
    {
        Ok(SessionType {
            protocol: Arc::clone(&self.protocol),
            payloads: mapped(&self.payloads, ChildOrder::Forward, map)?,
            state: self.state,
        })
    }
}

/// The images of `payloads` under `map`, visited in `order`, kept in slot
/// order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one image per payload, at the payload's own slot.
/// - fails: propagates the first error `map` returns.
/// - panics: none.
///
/// # Errors
/// The first error of `map`.
///
/// # Adequacy
/// - hypothesis: L3 — a reverse visit records its calls last slot first and
///   still places each image at its own slot.
/// - witness: `session::tests::payload_maps_keep_slots_in_either_order`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|images| images.len() == payloads.len()))]
fn mapped<From, To, E, Map>(
    payloads: &[From],
    order: ChildOrder,
    mut map: Map,
) -> Result<Arc<[To]>, E>
where
    From: Copy,
    Map: FnMut(From) -> Result<To, E>,
{
    let mut images = Vec::with_capacity(payloads.len());
    match order {
        ChildOrder::Forward => {
            for &payload in payloads {
                images.push(map(payload)?);
            }
        },
        ChildOrder::Reverse => {
            for &payload in payloads.iter().rev() {
                images.push(map(payload)?);
            }
            images.reverse();
        },
    }
    Ok(Arc::from(images))
}

/// What an endpoint at a session state does next.
#[derive(Clone, Debug)]
pub enum Step<'session, Id = ValueTypeId>
{
    /// Send a payload of the type, then stand at `next`.
    Send
    {
        /// The payload type.
        payload: Id,
        /// The continuation.
        next: SessionType<Id>,
    },
    /// Receive a payload of the type, then stand at `next`.
    Receive
    {
        /// The payload type.
        payload: Id,
        /// The continuation.
        next: SessionType<Id>,
    },
    /// Choose one of the branches.
    Select(Branches<'session, Id>),
    /// Handle every branch the peer may choose.
    Offer(Branches<'session, Id>),
    /// Close.
    End,
}

impl<Id> Step<'_, Id>
{
    /// The action this step admits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn action(&self) -> ActionKind
    {
        match *self {
            Self::Send { .. } => ActionKind::Send,
            Self::Receive { .. } => ActionKind::Receive,
            Self::Select(_) => ActionKind::Select,
            Self::Offer(_) => ActionKind::Offer,
            Self::End => ActionKind::Close,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a choice has no branch under a label.
    pub mod branch {
        /// The reason a label names no branch.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The choice does not name the label.
            Unlabelled,
        }
    }
}

/// The branches of a selection or an offer, each a session type.
#[derive(Clone, Debug)]
pub struct Branches<'session, Id = ValueTypeId>
{
    /// The session type the choice stands in.
    session: &'session SessionType<Id>,
    /// The labels and the states they continue at.
    branches: &'session BTreeMap<FieldLabel, ProtocolState>,
}

impl<'session, Id: Copy> Branches<'session, Id>
{
    /// The labels, in label order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn labels(&self) -> impl ExactSizeIterator<Item = &'session FieldLabel> + 'session
    {
        self.branches.keys()
    }

    /// The branch under `label`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the session type at the state `label` continues at.
    /// - provides: [`branch::Absent::Unlabelled`] when the choice does not name
    ///   `label`.
    /// - fails: [`ProtocolError::MissingNode`] only for a protocol that broke
    ///   its invariant.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`ProtocolError`] of the broken reference.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a named label and an unnamed one separate the two
    ///   answers.
    /// - witness: `session::tests::stepping_reads_each_former_and_unfolds_recursion`
    #[spec(ensures: |ret| match ret {
        | Ok(Maybe::Present(ref branch)) => self.branches.get(label) == Some(&branch.state),
        | Ok(Maybe::Absent(_)) => !self.branches.contains_key(label),
        | Err(_) => true,
    })]
    #[inline]
    pub fn get(
        &self,
        label: &FieldLabel,
    ) -> Result<Maybe<SessionType<Id>, branch::Absent>, ProtocolError>
    {
        match self.branches.get(label) {
            Some(&state) => Ok(Maybe::Present(self.session.at(state)?)),
            None => Ok(Maybe::Absent(branch::Absent::Unlabelled)),
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an action names no endpoint.
    pub mod subject {
        /// The reason an action has no subject endpoint.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A fork binds two endpoints rather than acting on one.
            Fork,
        }
    }
}

/// A session action: one computation former whose cases act on an endpoint
/// named by its linear de Bruijn index, or fork a new pair of endpoints.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum SessionAction<V = ValueId, C = ComputationId, T = ValueTypeId>
{
    /// `send(c, v)`: send `payload`, returning the unit.
    Send
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// The payload.
        payload: V,
    },
    /// `recv(c) as x ; body`: receive a payload into one linear binder and
    /// run `body` under it.
    Receive
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// The rest of the block, under the payload's linear binder.
        body: C,
    },
    /// `select(c, l)`: choose `label`, returning the unit.
    Select
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// The label chosen.
        label: FieldLabel,
    },
    /// `offer(c) { l => … }`: run the arm of the label the peer chose.
    Offer
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// One arm per label, in label order.
        arms: BTreeMap<FieldLabel, C>,
    },
    /// `close(c)`: close the endpoint, returning the unit.
    Close
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
    },
    /// `fork (c : S) { t } as d ; u`: `child` runs with `c : S` and `parent`
    /// continues with `d : dual(S)`, each under one linear binder.
    Fork
    {
        /// The session type `S` of the child's end.
        protocol: T,
        /// The child, under its end's linear binder.
        child: C,
        /// The continuation, under the parent's end's linear binder.
        parent: C,
    },
}

impl<V: Copy, C: Copy, T: Copy> SessionAction<V, C, T>
{
    /// The endpoint the action acts on.
    ///
    /// # Specification
    /// - ensures: the linear index every action but a fork names.
    /// - provides: [`subject::Absent::Fork`] for a fork.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action's subject and the fork's absence are
    ///   asserted.
    /// - witness: `session::tests::actions_name_their_subject_and_children`
    #[spec(ensures: |ret| matches!(*self, Self::Fork { .. }) == matches!(ret, Maybe::Absent(_)))]
    #[inline]
    pub const fn endpoint(&self) -> Maybe<DeBruijnIndex, subject::Absent>
    {
        match *self {
            Self::Send { endpoint, .. }
            | Self::Receive { endpoint, .. }
            | Self::Select { endpoint, .. }
            | Self::Offer { endpoint, .. }
            | Self::Close { endpoint } => Maybe::Present(endpoint),
            Self::Fork { .. } => Maybe::Absent(subject::Absent::Fork),
        }
    }

    /// The action an endpoint takes, or the fork's absence of one.
    ///
    /// # Specification
    /// - ensures: each action names its own kind.
    /// - provides: [`subject::Absent::Fork`] for a fork.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action's kind is asserted.
    /// - witness: `session::tests::actions_name_their_subject_and_children`
    #[spec(ensures: |ret| matches!(*self, Self::Fork { .. }) == matches!(ret, Maybe::Absent(_)))]
    #[inline]
    pub const fn kind(&self) -> Maybe<ActionKind, subject::Absent>
    {
        match *self {
            Self::Send { .. } => Maybe::Present(ActionKind::Send),
            Self::Receive { .. } => Maybe::Present(ActionKind::Receive),
            Self::Select { .. } => Maybe::Present(ActionKind::Select),
            Self::Offer { .. } => Maybe::Present(ActionKind::Offer),
            Self::Close { .. } => Maybe::Present(ActionKind::Close),
            Self::Fork { .. } => Maybe::Absent(subject::Absent::Fork),
        }
    }

    /// The value children: a send's payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = V> + '_
    {
        match *self {
            Self::Send { payload, .. } => Some(payload),
            Self::Receive { .. }
            | Self::Select { .. }
            | Self::Offer { .. }
            | Self::Close { .. }
            | Self::Fork { .. } => None,
        }
        .into_iter()
    }

    /// The computation children in canonical order: a receive's body, an
    /// offer's arms in label order, a fork's child before its parent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computations(&self) -> impl DoubleEndedIterator<Item = C> + '_
    {
        let (arms, fork) = match *self {
            Self::Offer { ref arms, .. } => (Some(arms.values().copied()), None),
            Self::Fork { child, parent, .. } => (None, Some([Some(child), Some(parent)])),
            Self::Receive { body, .. } => (None, Some([Some(body), None])),
            Self::Send { .. } | Self::Select { .. } | Self::Close { .. } => (None, None),
        };
        arms.into_iter()
            .flatten()
            .chain(fork.into_iter().flatten().flatten())
    }

    /// The linear binders a computation child opens: one for a receive's
    /// body and for each half of a fork, none for an offer's arm.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn child_binders(&self) -> crate::Binders
    {
        match *self {
            Self::Receive { .. } | Self::Fork { .. } => crate::Binders::ONE,
            Self::Send { .. } | Self::Select { .. } | Self::Offer { .. } | Self::Close { .. } => {
                crate::Binders::NONE
            },
        }
    }

    /// The value-type children: a fork's protocol.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_types(&self) -> impl DoubleEndedIterator<Item = T> + '_
    {
        match *self {
            Self::Fork { protocol, .. } => Some(protocol),
            Self::Send { .. }
            | Self::Receive { .. }
            | Self::Select { .. }
            | Self::Offer { .. }
            | Self::Close { .. } => None,
        }
        .into_iter()
    }

    /// The action with every child erased: its kind, subject, label and arm
    /// labels, which is what two actions must share to be the same former.
    ///
    /// # Specification
    /// - ensures: the action with every child replaced by the unit, kept at its
    ///   position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sends on different endpoints differ in shape, two
    ///   sends of different payloads on one endpoint do not.
    /// - witness: `session::tests::actions_name_their_subject_and_children`
    #[spec(ensures: |ret| ret.kind() == self.kind() && ret.endpoint() == self.endpoint())]
    #[inline]
    #[must_use]
    pub fn shape(&self) -> SessionAction<(), (), ()>
    {
        match self.try_map(
            ChildOrder::Forward,
            &mut (),
            |&mut (), _| Ok::<_, core::convert::Infallible>(()),
            |&mut (), _| Ok(()),
            |&mut (), _| Ok(()),
        ) {
            Ok(shape) => shape,
            Err(never) => match never {},
        }
    }

    /// The same action over its children's images, the maps sharing `state`
    /// so a walk can feed them from one result stack.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: subjects, labels and the action are kept; each child is
    ///   replaced by its image at its own position; [`ChildOrder::Forward`]
    ///   visits the protocol, the payload, the arms in label order, then a
    ///   fork's child and parent, and [`ChildOrder::Reverse`] exactly the
    ///   reverse.
    /// - fails: propagates the first error a map returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error of a map.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an offer of two arms and a fork mapped in reverse
    ///   order keep each image at its own position, and the fork's visit order
    ///   crosses families.
    /// - witness: `session::tests::actions_name_their_subject_and_children`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|mapped| match (self, mapped) {
        | (&Self::Offer { ref arms, .. }, &SessionAction::Offer { arms: ref images, .. }) => arms.keys().eq(images.keys()),
        | (&Self::Send { endpoint: a, .. }, &SessionAction::Send { endpoint: b, .. })
        | (&Self::Receive { endpoint: a, .. }, &SessionAction::Receive { endpoint: b, .. })
        | (&Self::Close { endpoint: a }, &SessionAction::Close { endpoint: b }) => a == b,
        | (&Self::Select { endpoint: a, label: ref x }, &SessionAction::Select { endpoint: b, label: ref y }) => a == b && x == y,
        | (&Self::Fork { .. }, &SessionAction::Fork { .. }) => true,
        | _ => false,
    }))]
    #[inline]
    pub fn try_map<S, V2, C2, T2, E, Values, Computations, ValueTypes>(
        &self,
        order: ChildOrder,
        state: &mut S,
        mut value: Values,
        mut computation: Computations,
        mut value_type: ValueTypes,
    ) -> Result<SessionAction<V2, C2, T2>, E>
    where
        Values: FnMut(&mut S, V) -> Result<V2, E>,
        Computations: FnMut(&mut S, C) -> Result<C2, E>,
        ValueTypes: FnMut(&mut S, T) -> Result<T2, E>,
    {
        Ok(match *self {
            Self::Send { endpoint, payload } => SessionAction::Send {
                endpoint,
                payload: value(state, payload)?,
            },
            Self::Receive { endpoint, body } => SessionAction::Receive {
                endpoint,
                body: computation(state, body)?,
            },
            Self::Select {
                endpoint,
                ref label,
            } => SessionAction::Select {
                endpoint,
                label: label.clone(),
            },
            Self::Offer { endpoint, ref arms } => {
                let mut images = BTreeMap::new();
                match order {
                    ChildOrder::Forward => {
                        for (label, &arm) in arms {
                            let _first = images.insert(label.clone(), computation(state, arm)?);
                        }
                    },
                    ChildOrder::Reverse => {
                        for (label, &arm) in arms.iter().rev() {
                            let _first = images.insert(label.clone(), computation(state, arm)?);
                        }
                    },
                }
                SessionAction::Offer {
                    endpoint,
                    arms: images,
                }
            },
            Self::Close { endpoint } => SessionAction::Close { endpoint },
            Self::Fork {
                protocol,
                child,
                parent,
            } => match order {
                ChildOrder::Forward => {
                    let protocol = value_type(state, protocol)?;
                    let child = computation(state, child)?;
                    SessionAction::Fork {
                        protocol,
                        child,
                        parent: computation(state, parent)?,
                    }
                },
                ChildOrder::Reverse => {
                    let parent = computation(state, parent)?;
                    let child = computation(state, child)?;
                    SessionAction::Fork {
                        protocol: value_type(state, protocol)?,
                        child,
                        parent,
                    }
                },
            },
        })
    }
}

/// The identity a session statement claims between two session codes.
///
/// `bisim(a, b)` inhabits `Path(Type, a, b)` and `sim(a, b)` inhabits
/// `Flow(Type, a, b)`. The checker decides the statement with the session
/// engine and the kernel replays it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SessionRelation
{
    /// Bisimilar protocols: the same endpoint behaviour, either way round.
    Equivalence,
    /// Gay–Hole subtyping: fewer selections, more offers.
    Subtyping,
}

quenchant_shape::reason_enum! {
    /// Why a recorded move carries no payload.
    pub mod carried {
        /// The reason a move has no payload value.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A choice carries a label, not a value.
            Choice,
            /// A close carries nothing.
            Close,
        }
    }
}

/// One move of a recorded run, read from the side of the endpoint that
/// recorded it; the checker replays a run's moves against a protocol with the
/// session monitor.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum RecordedMove<V = ValueId>
{
    /// `sent(v)`: the endpoint sent `v`.
    Sent(V),
    /// `received(v)`: the endpoint received `v`.
    Received(V),
    /// `selected(l)`: the endpoint chose `l`.
    Selected(FieldLabel),
    /// `offered(l)`: the endpoint offered a choice and the peer chose `l`.
    Offered(FieldLabel),
    /// `closed`: the endpoint closed.
    Closed,
}

impl<V: Copy> RecordedMove<V>
{
    /// The action the move takes.
    ///
    /// # Specification
    /// - ensures: a sent move sends, a received one receives, a selected one
    ///   selects, an offered one offers and a closed one closes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every move kind is asserted.
    /// - witness: `session::tests::recorded_moves_name_their_payload_and_action`
    #[spec(ensures: |ret| matches!((self, ret),
        (&Self::Sent(_), ActionKind::Send) | (&Self::Received(_), ActionKind::Receive)
        | (&Self::Selected(_), ActionKind::Select) | (&Self::Offered(_), ActionKind::Offer)
        | (&Self::Closed, ActionKind::Close)))]
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> ActionKind
    {
        match *self {
            Self::Sent(_) => ActionKind::Send,
            Self::Received(_) => ActionKind::Receive,
            Self::Selected(_) => ActionKind::Select,
            Self::Offered(_) => ActionKind::Offer,
            Self::Closed => ActionKind::Close,
        }
    }

    /// The payload value a send or a receive carries.
    ///
    /// # Specification
    /// - ensures: the value of a sent or received move.
    /// - provides: [`carried::Absent::Choice`] for a choice and
    ///   [`carried::Absent::Close`] for a close.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every move kind's payload or absence is asserted.
    /// - witness: `session::tests::recorded_moves_name_their_payload_and_action`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) == matches!(*self, Self::Sent(_) | Self::Received(_)))]
    #[inline]
    pub const fn payload(&self) -> Maybe<V, carried::Absent>
    {
        match *self {
            Self::Sent(value) | Self::Received(value) => Maybe::Present(value),
            Self::Selected(_) | Self::Offered(_) => Maybe::Absent(carried::Absent::Choice),
            Self::Closed => Maybe::Absent(carried::Absent::Close),
        }
    }

    /// The same move carrying `payload` in place of its own, when it carries
    /// one.
    ///
    /// # Specification
    /// - ensures: the action and label are kept; a send or receive carries
    ///   `payload`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rewritten send keeps its action and a choice keeps
    ///   its label.
    /// - witness: `session::tests::recorded_moves_name_their_payload_and_action`
    #[spec(ensures: |ret| ret.kind() == self.kind())]
    #[inline]
    #[must_use]
    pub fn carrying<W>(
        &self,
        payload: W,
    ) -> RecordedMove<W>
    where
        W: Copy,
    {
        match *self {
            Self::Sent(_) => RecordedMove::Sent(payload),
            Self::Received(_) => RecordedMove::Received(payload),
            Self::Selected(ref label) => RecordedMove::Selected(label.clone()),
            Self::Offered(ref label) => RecordedMove::Offered(label.clone()),
            Self::Closed => RecordedMove::Closed,
        }
    }

    /// The same move, its payload mapped by `mapper`.
    ///
    /// # Specification
    /// - ensures: the action and label are kept; a send or receive carries what
    ///   `mapper` returns for its payload, and `mapper` runs for no other move.
    /// - fails: the first error `mapper` returns.
    /// - panics: none.
    ///
    /// # Errors
    /// The first error `mapper` returns, for a send's or a receive's payload.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mapped send and receive carry the image and a
    ///   choice and a close never call the mapper.
    /// - witness: `session::tests::recorded_moves_name_their_payload_and_action`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |moved| moved.kind() == self.kind()))]
    #[inline]
    pub fn try_map<W, E, Mapper>(
        &self,
        mapper: Mapper,
    ) -> Result<RecordedMove<W>, E>
    where
        W: Copy,
        Mapper: FnOnce(V) -> Result<W, E>,
    {
        Ok(match *self {
            Self::Sent(payload) => RecordedMove::Sent(mapper(payload)?),
            Self::Received(payload) => RecordedMove::Received(mapper(payload)?),
            Self::Selected(ref label) => RecordedMove::Selected(label.clone()),
            Self::Offered(ref label) => RecordedMove::Offered(label.clone()),
            Self::Closed => RecordedMove::Closed,
        })
    }
}

impl CoreArena
{
    /// Mint the endpoint type `session`.
    ///
    /// # Specification
    /// - requires: every payload resolves in this arena.
    /// - ensures: the node is `session` as given.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted session type reads back with its protocol,
    ///   payloads and state.
    /// - witness: `session::tests::stepping_reads_each_former_and_unfolds_recursion`
    #[spec(requires: session.payloads().iter().all(|&payload| self.value_type(payload).is_some()),
        ensures: |ret| matches!(self.value_type(ret), Some(ValueType::Session(_))))]
    #[inline]
    pub fn value_type_session(
        &mut self,
        session: SessionType,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Session(session))
    }

    /// Mint the session action `action`.
    ///
    /// # Specification
    /// - requires: every child of `action` resolves in this arena.
    /// - ensures: the node is `action` as given.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a minted fork reads back with its protocol, child and
    ///   parent.
    /// - witness: `session::tests::actions_name_their_subject_and_children`
    #[spec(requires: action.values().all(|value| self.value(value).is_some())
            && action.computations().all(|computation| self.computation(computation).is_some())
            && action.value_types().all(|ty| self.value_type(ty).is_some()),
        ensures: |ret| matches!(self.computation(ret), Some(Computation::Session(_))))]
    #[inline]
    pub fn computation_session(
        &mut self,
        action: SessionAction,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Session(action))
    }
}

#[cfg(test)]
mod tests;
