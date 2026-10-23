//! Binary sessions in the judgement: the endpoints a fork or a receive binds
//! into the linear zone, the actions that advance them, and the refusals that
//! name them.
//!
//! # An endpoint is a linear slot that changes type
//!
//! `fork (c : S) { t } as d ; u` opens one slot of the linear zone `Σ` at `S`
//! for the child `t` and, once the child is checked, one at `dual(S)` for the
//! parent `u`. Each action names its endpoint by its linear index and moves
//! the slot along the protocol: `send`, `recv` and `select` rebind the slot
//! at the continuation, `offer` rebinds it at each arm's branch, and `close`
//! consumes it at `end`. The zone's own discipline — one consumption, no
//! weakening — is then the endpoint's: a slot still available when the half
//! or the body that bound it finishes is a leftover endpoint, an action on a
//! consumed slot is an action after `close`.
//!
//! The rules run as frames of the judgement's one machine, as the rest of
//! the judgement does:
//!
//! |rule|frame|what it waits on|
//! |---|---|---|
//! |send|`SessionSend`|the payload's check, then advances the endpoint|
//! |receive|`ReceiveBody`|the body's judgement with the payload bound, then requires a received endpoint spent|
//! |offer|`OfferArm`|each arm's check, from the zone as the offer found it|
//! |fork|`ForkProtocol`|the protocol annotation's formation|
//! |fork|`ForkChild`|the child's check against `F 1`|
//! |fork|`ForkParent`|the parent's judgement in the fork's direction|
//!
//! **Choice.** `send`, `select` and `close` are computations returning the
//! unit, sequenced by the ordinary bind; `recv` carries the rest of its block
//! as its body under one linear binder, as a fork carries its parent.
//! **Alternative.** A receive returning its payload to a bind, which binds the
//! payload intuitionistically and so can never hold an endpoint.
//! **Reversal.** A payload whose zone the checker cannot fix at the receive,
//! which no payload type is.
//!
//! # Delegation: a payload is placed by its type
//!
//! A send whose payload is a linear variable naming an endpoint consumes
//! that endpoint's slot: the endpoint leaves the sender, its session type
//! converted to the payload type (Honda, Vasconcelos and Kubo). The receive
//! places its payload in its linear binder by the payload type: a session
//! type opens an endpoint, available, which the body must act on and close
//! like an end a fork binds; any other type opens a received value already
//! spent, whose reads copy, so it leaves no residue.
//!
//! # The fork splits the zone by what the child names
//!
//! The child's share of the enclosing endpoints is exactly the linear indices
//! it reads free; the parent may name none of them, and the child must
//! consume every one of them as well as its own end before the parent runs.
//! A received value the child reads is shared, since its reads copy.
//! The child is checked against the pure returner of the unit, and the fork
//! itself must stand at a pure returner, so no operation a handler could
//! resume twice runs while an endpoint is live.
//!
//! # Branches agree on the zone
//!
//! An offer checks each arm from the zone as the offer found it, its endpoint
//! advanced to the arm's branch, and requires every arm to leave the zone as
//! the first arm did: the same slots consumed, and every slot still available
//! at an equivalent session type. Every other branching former — a case, a
//! lazy product, a fold, a handler — refuses an endpoint its branches name, as
//! do a thunk and a fixpoint, whose bodies run any number of times, and a
//! first-class stack. **Reversal.** Checking a case's branches as an offer's
//! arms needs only the offer's frame at each branching rule.
//!
//! # One relation engine
//!
//! Session types are compared through `gandr-core-session`'s engine: the
//! protocol graph maps node for node onto the engine's syntax, every payload
//! given one opaque identity, and the payload types of every send and
//! receive pair the engine visits are then compared by the judgement's own
//! conversion, invariantly. Subtyping is Gay and Hole's: fewer selections,
//! more offers.
//!
//! # Where an endpoint may not stand
//!
//! An endpoint lives only in the linear zone a fork or a receive opened. A
//! declaration whose type is a session type is refused as
//! [`LinearityDefect::Unrestricted`] at its signature: a top-level name is
//! unrestricted, so its endpoint could be used any number of times. An
//! endpoint read anywhere but as the subject of an action or as a payload
//! sent whole is [`LinearityDefect::AsValue`].
//!
//! The kernel has no channels; readmission erases the discipline and the
//! kernel replays what a session computes. A session type crosses as the
//! kernel's session code rooted at the state it stands at, where a session
//! statement relates it ([`crate::flow`]). A send crosses as its payload
//! returned, a select and a close as the unit, a fork as its child and then
//! its parent. A receive, an offer and a linear variable are still refused as
//! [`crate::bridge::Refusal::Session`], and a declaration holding one stays
//! on the checker's side, accepted and not re-derived.
//!
//! # References
//!
//! - Luís Caires and Frank Pfenning. "Session Types as Intuitionistic Linear
//!   Propositions." _CONCUR 2010_, LNCS 6269. <https://doi.org/10.1007/978-3-642-15375-4_16>
//!   — endpoints as linear hypotheses, the fork as a cut splitting the linear
//!   context.
//! - Frank Pfenning and Dennis Griffith. "Polarized Substructural Session
//!   Types." _Foundations of Software Science and Computation Structures
//!   2015_, LNCS 9034. <https://doi.org/10.1007/978-3-662-46678-0_1>
//!   — sessions in a polarized, call-by-push-value setting.
//! - Simon Gay and Malcolm Hole. "Subtyping for Session Types in the Pi
//!   Calculus." _Acta Informatica_ 42 (2005). <https://doi.org/10.1007/s00236-005-0177-z>
//!   — the coinductive subtyping the engine decides.
//! - Kohei Honda, Vasco T. Vasconcelos and Makoto Kubo. "Language
//!   Primitives and Type Discipline for Structured Communication-Based
//!   Programming." _ESOP 1998_, LNCS 1381. <https://doi.org/10.1007/BFb0053567>
//!   — delegation: a channel sent over a channel leaves the sender.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_session::Label;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Relation;
use gandr_core_session::RelationResult;
use gandr_core_session::Session;
use gandr_core_term::ComputationId;
use gandr_core_term::LinearUse;
use gandr_core_term::ValueTypeId;
use gandr_core_term::session::ActionKind;
use gandr_core_term::session::ProtocolNode;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::SessionType;
use quenchant_shape::shape::Maybe;

use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

/// Which binder of an endpoint bound it: a half of a fork, or a receive.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ForkSide
{
    /// The child's end, at the annotated session type.
    Child,
    /// The parent's end, at its dual.
    Parent,
    /// An end sent over another endpoint, bound by the receive that took it.
    Received,
}

/// An endpoint, named by the fork or the receive that bound it and its side.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Endpoint
{
    /// The fork, or for [`ForkSide::Received`] the receive.
    pub fork: ComputationId,
    /// The side.
    pub side: ForkSide,
}

/// What an endpoint's session state refuses of an action on it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ProtocolDefect
{
    /// The action is not the one the state admits.
    Action
    {
        /// The action the state admits.
        expected: ActionKind,
        /// The action taken.
        observed: ActionKind,
    },
    /// A selection names a label the state does not offer.
    Label,
    /// An offer's arms are not exactly the labels the state offers.
    Arms,
}

/// What may run an endpoint's use other than exactly once.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Capture
{
    /// A thunk, forced any number of times.
    Thunk,
    /// A fixpoint's body, run once per call.
    Recursion,
    /// A branch of a case, a lazy product, or a fold.
    Branch,
    /// A first-class stack.
    Stack,
    /// A continuation a handler or a shift may resume any number of times.
    Continuation,
    /// A forked task, which runs as a peer no region bounds.
    Task,
}

/// How an endpoint escaped its one linear use.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LinearityDefect
{
    /// A half of a fork finished with the endpoint unconsumed.
    Residue
    {
        /// The endpoint.
        endpoint: Endpoint,
        /// Its session type when the half finished.
        state: ValueTypeId,
    },
    /// The endpoint was acted on after it was closed.
    Closed
    {
        /// The endpoint.
        endpoint: Endpoint,
    },
    /// The endpoint was used twice in one action: sent over itself, or named
    /// by both halves of a fork.
    UsedTwice
    {
        /// The endpoint.
        endpoint: Endpoint,
    },
    /// The endpoint was named where its use may run other than once.
    Captured
    {
        /// The endpoint.
        endpoint: Endpoint,
        /// What may run it.
        by: Capture,
    },
    /// The endpoint was read as a value outside an action.
    AsValue
    {
        /// The endpoint.
        endpoint: Endpoint,
    },
    /// Two arms of an offer left the endpoint in different states.
    ArmsDisagree
    {
        /// The endpoint.
        endpoint: Endpoint,
        /// The first arm.
        first: ComputationId,
        /// The arm that disagrees with it.
        other: ComputationId,
    },
    /// A declaration's type is a session type: an endpoint outside the
    /// linear zone.
    Unrestricted,
    /// An action names a linear index no fork or receive bound.
    Unbound
    {
        /// The index.
        index: gandr_kernel_term::DeBruijnIndex,
    },
    /// A buffer placed live — by a receive, a placement or an operation
    /// clause's mint — reached the end of its scope never returned, or one arm
    /// of a branch returned it where another kept it.
    BufferUnreturned
    {
        /// The computation that placed the buffer live.
        site: ComputationId,
    },
    /// A buffer was returned a second time.
    BufferReturnedTwice
    {
        /// The computation that placed the buffer live.
        site: ComputationId,
    },
    /// A buffer was read other than by the send, the resumption or the
    /// operation that returns it, or a buffer never placed live was returned.
    BufferRead
    {
        /// The computation that placed the buffer live, or the action that
        /// returned a buffer no slot holds.
        site: ComputationId,
    },
    /// An operation clause whose continuation holds an obligation finished
    /// without resuming or abandoning it.
    ContinuationUnspent
    {
        /// The clause's body.
        clause: ComputationId,
    },
    /// A continuation holding an obligation was resumed or abandoned a second
    /// time.
    ContinuationUsedTwice
    {
        /// The clause's body.
        clause: ComputationId,
    },
    /// A continuation holding an obligation was named where its end may run
    /// other than once.
    ContinuationCaptured
    {
        /// The clause's body.
        clause: ComputationId,
        /// What may run it.
        by: Capture,
    },
    /// A continuation holding an obligation was read as a value, other than as
    /// what a resumption or an abandonment ends.
    ContinuationAsValue
    {
        /// The clause's body.
        clause: ComputationId,
    },
}

/// An endpoint the linear zone held when a run refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LiveEndpoint
{
    /// The endpoint.
    pub endpoint: Endpoint,
    /// Its session type.
    pub state: ValueTypeId,
    /// Whether it was still unconsumed.
    pub use_state: LinearUse,
}

quenchant_shape::reason_enum! {
    /// Why two session types relate by no relation.
    pub(crate) mod related {
        /// The reason no relation holds.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// Some reachable action, label set or continuation disagrees.
            Unrelated,
        }
    }
}

/// The session type `ty` names at its own node.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the session type held at `ty`, shared.
/// - fails: [`CheckRefusal::MachineInvariant`] for a node of another former;
///   the view's refusal for a dangling id.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — every action rule reads its endpoint's state through
///   this, so the seat exchange observes it at each action.
/// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
#[spec(ensures: |ret| ret.is_err() || matches!(value_type_view(context.arena(), ty), Ok(ValueTypeView::Session(_))))]
pub(crate) fn session_at(
    context: &CheckingContext<'_>,
    ty: ValueTypeId,
) -> Result<SessionType, CheckRefusal>
{
    match value_type_view(context.arena(), ty)? {
        ValueTypeView::Session(session) => Ok(session.clone()),
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => Err(CheckRefusal::MachineInvariant),
    }
}

/// Refuse a declaration whose formed type `declared` is a session type at its
/// weak head: an endpoint exists only in the linear zone a fork opens.
///
/// # Specification
/// - requires: `declared` is formed.
/// - ensures: nothing changes.
/// - fails: [`CheckRefusal::Linearity`] naming
///   [`LinearityDefect::Unrestricted`] at `declared`; the unfolding's refusal
///   when a decode does not unfold.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration at a written session type and one at a type
///   alias of it are both refused, and a declaration at a thunk type is not.
/// - witness: `judgement::session::tests::an_endpoint_at_a_top_level_declaration_is_refused`
#[spec(ensures: |ret| match ret {
    | Err(CheckRefusal::Linearity { at, defect: LinearityDefect::Unrestricted }) => {
        at == crate::refusal::CoreNode::Type(crate::refusal::TypeNode::Value(declared))
    },
    | _ => true,
})]
pub(crate) fn unrestricted(
    context: &mut CheckingContext<'_>,
    declared: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    let head = match value_type_view(context.arena(), declared)? {
        ValueTypeView::Element { .. } => context.whnf_value_type(declared)?,
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Session(_)
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => declared,
    };
    match value_type_view(context.arena(), head)? {
        // A buffer, like an endpoint, exists only where a receive places it.
        ValueTypeView::Session(_) | ValueTypeView::Buffer => Err(CheckRefusal::Linearity {
            at: crate::refusal::CoreNode::Type(crate::refusal::TypeNode::Value(declared)),
            defect: LinearityDefect::Unrestricted,
        }),
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => Ok(()),
    }
}

/// The engine's syntax for `session`'s protocol, node for node, every payload
/// given one identity.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one engine node per protocol node at the same position, rooted at
///   the protocol's root.
/// - fails: [`CheckRefusal::MachineInvariant`] when the engine refuses the
///   translation, which a validated protocol never gives it.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a recursive protocol, related to itself past its root and
///   to a differing one, separates a node mistranslated.
/// - witness: `session::tests::equivalence_sees_through_unfolding_and_payloads`
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|refusal| *refusal == CheckRefusal::MachineInvariant))]
pub(crate) fn engine(session: &SessionType) -> Result<Session, CheckRefusal>
{
    let payload = gandr_core_session::ValueTypeId([0_u8; 32]);
    let id = |state: ProtocolState| NodeId(usize::from(state));
    let labels =
        |branches: &alloc::collections::BTreeMap<gandr_kernel_term::FieldLabel, ProtocolState>| {
            branches
                .iter()
                .map(|(label, &state)| (Label::from(label.as_ref()), id(state)))
                .collect()
        };
    let nodes = session
        .protocol()
        .nodes()
        .iter()
        .map(|node| match *node {
            ProtocolNode::Send { next, .. } => Node::Send(payload, id(next)),
            ProtocolNode::Receive { next, .. } => Node::Receive(payload, id(next)),
            ProtocolNode::Select(ref branches) => Node::Select(labels(branches)),
            ProtocolNode::Offer(ref branches) => Node::Offer(labels(branches)),
            ProtocolNode::End => Node::End,
            ProtocolNode::Mu(body) => Node::Mu(id(body)),
            ProtocolNode::Recur(binder) => Node::Var(id(binder)),
        })
        .collect();
    Session::new(nodes, id(session.protocol().root()))
        .map_err(|_fault| CheckRefusal::MachineInvariant)
}

/// One send or receive pair the engine visited: the payload slot each
/// protocol names there and the type it holds, left first.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PayloadPair
{
    /// The two payload slots, the kernel's numbering of each session's
    /// payloads.
    pub slots: (
        gandr_kernel_term::session::PayloadSlot,
        gandr_kernel_term::session::PayloadSlot,
    ),
    /// The two payload types.
    pub types: (ValueTypeId, ValueTypeId),
}

/// Two session types the engine related: the candidate evidence the kernel
/// replays, and the payload pairs conversion still compares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Related
{
    /// The engine's coinductive pairs, over the protocols' node positions.
    pub evidence: gandr_kernel_term::session::Evidence,
    /// Every send and receive pair, in the order of the engine's pairs.
    pub payloads: Vec<PayloadPair>,
}

/// Relate the session types `left` and `right` by `relation`: the engine's
/// decision over their protocols from their states, with the payload pairs
/// still to compare.
///
/// # Specification
/// - requires: both are session types of the context's arena.
/// - ensures: the payload types of every send and receive pair the engine
///   visited, left first, when the protocols relate; unrelated otherwise.
/// - provides: the session half of conversion and of an offer's agreement.
/// - fails: [`CheckRefusal::MachineInvariant`] for a node of another former or
///   a payload slot past a session type's payloads.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — two foldings of one recursive protocol relate with their
///   payload pairs, a differing payload pair is handed back for conversion to
///   refuse, a narrower selection is a subtype and not an equivalent.
/// - witness: `session::tests::equivalence_sees_through_unfolding_and_payloads`
/// - witness: `session::tests::subtyping_follows_gay_and_hole_at_endpoints`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref pairs)) => pairs.iter().all(|pair| {
        session_at(context, left).is_ok_and(|session| session.payloads().contains(&pair.types.0))
            && session_at(context, right).is_ok_and(|session| session.payloads().contains(&pair.types.1))
    }),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
pub(crate) fn relate(
    context: &CheckingContext<'_>,
    left: ValueTypeId,
    right: ValueTypeId,
    relation: Relation,
) -> Result<Maybe<Vec<PayloadPair>, related::Absent>, CheckRefusal>
{
    let left = session_at(context, left)?;
    let right = session_at(context, right)?;
    Ok(match related(&left, &right, relation)? {
        Maybe::Present(decided) => Maybe::Present(decided.payloads),
        Maybe::Absent(absent) => Maybe::Absent(absent),
    })
}

/// Relate the session types `left` and `right` by `relation`, keeping the
/// engine's evidence beside the payload pairs.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`relate`], with the engine's pairs: they contain the pair of
///   the two states' heads and are the evidence the kernel replays over
///   protocols erased node for node.
/// - provides: the decision a session statement records.
/// - fails: as [`relate`].
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a widened selection relates by subtyping with evidence
///   the kernel replays, and not by equivalence.
/// - witness: `flow::tests::statements_decide_by_the_engine_and_replay`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(ref decided)) => !decided.evidence.pairs.is_empty(),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
pub(crate) fn related(
    left: &SessionType,
    right: &SessionType,
    relation: Relation,
) -> Result<Maybe<Related, related::Absent>, CheckRefusal>
{
    let state = |session: &SessionType| NodeId(usize::from(session.state()));
    let decided = gandr_core_session::relate_states(
        &engine(left)?,
        state(left),
        &engine(right)?,
        state(right),
        relation,
    )
    .map_err(|_fault| CheckRefusal::MachineInvariant)?;
    let RelationResult::Related(evidence) = decided
    else {
        return Ok(Maybe::Absent(related::Absent::Unrelated));
    };
    let payload = |session: &SessionType, position: usize| match session
        .protocol()
        .node(ProtocolState::from(position))
    {
        Ok(&(ProtocolNode::Send { payload, .. } | ProtocolNode::Receive { payload, .. })) => {
            let slot = usize::from(payload);
            session
                .payloads()
                .get(slot)
                .map(|&ty| Some((gandr_kernel_term::session::PayloadSlot(slot), ty)))
                .ok_or(CheckRefusal::MachineInvariant)
        },
        Ok(_) => Ok(None),
        Err(_) => Err(CheckRefusal::MachineInvariant),
    };
    let mut payloads = Vec::new();
    for pair in &evidence.pairs {
        if let (Some((left_slot, a)), Some((right_slot, b))) = (
            payload(left, pair.source.0)?,
            payload(right, pair.target.0)?,
        ) {
            payloads.push(PayloadPair {
                slots: (left_slot, right_slot),
                types: (a, b),
            });
        }
    }
    Ok(Maybe::Present(Related { evidence, payloads }))
}

#[cfg(test)]
mod tests;
