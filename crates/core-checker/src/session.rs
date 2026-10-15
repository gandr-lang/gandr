//! Binary sessions in the judgement: the endpoint a fork binds into the
//! linear zone, the actions that advance it, and the refusals that name it.
//!
//! # An endpoint is a linear slot that changes type
//!
//! `fork (c : S) { t } as d ; u` opens one slot of the linear zone `Σ` at `S`
//! for the child `t` and, once the child is checked, one at `dual(S)` for the
//! parent `u`; nothing else binds an endpoint. Each action names its endpoint
//! by its linear index and moves the slot along the protocol: `send`, `recv`
//! and `select` rebind the slot at the continuation, `offer` rebinds it at
//! each arm's branch, and `close` consumes it at `end`. The zone's own
//! discipline — one consumption, no weakening — is then the endpoint's: a
//! slot still available when its fork's half finishes is a leftover endpoint,
//! an action on a consumed slot is an action after `close`.
//!
//! The rules run as frames of the judgement's one machine, as the rest of
//! the judgement does:
//!
//! |rule|frame|what it waits on|
//! |---|---|---|
//! |send|`SessionSend`|the payload's check, then advances the endpoint|
//! |offer|`OfferArm`|each arm's check, from the zone as the offer found it|
//! |fork|`ForkProtocol`|the protocol annotation's formation|
//! |fork|`ForkChild`|the child's check against `F 1`|
//! |fork|`ForkParent`|the parent's judgement in the fork's direction|
//! |formation|`FormSession`|each payload type's formation, refusing a session type|
//!
//! **Choice.** An action is a computation that returns the unit or the
//! payload, sequenced by the ordinary bind, so the bind's body frame is the
//! session continuation. **Alternative.** A continuation-carrying action —
//! `send c v; S` as one former whose frame holds the rest — which needs a
//! second sequencing form beside bind. **Reversal.** Delegation, where an
//! action must hand back the endpoint as a value.
//!
//! # The fork splits the zone by what the child names
//!
//! The child's share of the enclosing endpoints is exactly the linear indices
//! it reads free; the parent may name none of them, and the child must
//! consume every one of them as well as its own end before the parent runs.
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
//! lazy pair, a fold, a handler — refuses an endpoint its branches name, as
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
//! An endpoint lives only in the linear zone a fork opened. A declaration
//! whose type is a session type is refused as [`LinearityDefect::Unrestricted`]
//! at its signature: a top-level name is unrestricted, so its endpoint could be
//! used any number of times. A payload whose type is a session type, or an
//! endpoint named as a payload, is [`LinearityDefect::Delegated`]: binary
//! sessions here carry values, never channels. An endpoint read anywhere but as
//! the subject of an action is [`LinearityDefect::AsValue`]. **Reversal.**
//! Delegation needs an action that consumes the sent endpoint's slot and a
//! receive that binds a fresh one; the frames above take both without a new
//! machine.
//!
//! The kernel has no channels: a session type crosses only as a code, at its
//! protocol's root, where a session statement relates it
//! ([`crate::flow`]). The bridge refuses a declaration that holds an action,
//! a session past its root or a linear variable as
//! [`crate::bridge::Refusal::Session`], and the declaration stays on the
//! checker's side, accepted and not re-derived.
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

/// Which half of a fork an endpoint belongs to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ForkSide
{
    /// The child's end, at the annotated session type.
    Child,
    /// The parent's end, at its dual.
    Parent,
}

/// An endpoint, named by the fork that bound it and its side.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Endpoint
{
    /// The fork.
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
    /// A branch of a case, a lazy pair, or a fold.
    Branch,
    /// A first-class stack.
    Stack,
    /// A continuation a handler or a shift may resume any number of times.
    Continuation,
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
    /// An endpoint, or a session type, was sent as a payload: delegation.
    Delegated,
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
    /// An action names a linear index no fork bound.
    Unbound
    {
        /// The index.
        index: gandr_kernel_term::DeBruijnIndex,
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
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
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
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Session(_)
        | ValueTypeView::Unknown => declared,
    };
    match value_type_view(context.arena(), head)? {
        ValueTypeView::Session(_) => Err(CheckRefusal::Linearity {
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
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
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
        | ValueTypeView::Capability { .. }
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

/// Two session types the engine related: the candidate evidence the kernel
/// replays, and the payload pairs conversion still compares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Related
{
    /// The engine's coinductive pairs, over the protocols' node positions.
    pub evidence: gandr_kernel_term::session::Evidence,
    /// The payload types of every send and receive pair, left first.
    pub payloads: Vec<(ValueTypeId, ValueTypeId)>,
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
    | Ok(Maybe::Present(ref pairs)) => pairs.iter().all(|&(first, second)| {
        session_at(context, left).is_ok_and(|session| session.payloads().contains(&first))
            && session_at(context, right).is_ok_and(|session| session.payloads().contains(&second))
    }),
    | Ok(Maybe::Absent(_)) | Err(_) => true,
})]
pub(crate) fn relate(
    context: &CheckingContext<'_>,
    left: ValueTypeId,
    right: ValueTypeId,
    relation: Relation,
) -> Result<Maybe<Vec<(ValueTypeId, ValueTypeId)>, related::Absent>, CheckRefusal>
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
            session
                .payloads()
                .get(usize::from(payload))
                .copied()
                .map(Some)
                .ok_or(CheckRefusal::MachineInvariant)
        },
        Ok(_) => Ok(None),
        Err(_) => Err(CheckRefusal::MachineInvariant),
    };
    let mut payloads = Vec::new();
    for pair in &evidence.pairs {
        if let (Some(a), Some(b)) = (
            payload(left, pair.source.0)?,
            payload(right, pair.target.0)?,
        ) {
            payloads.push((a, b));
        }
    }
    Ok(Maybe::Present(Related { evidence, payloads }))
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;

    use gandr_core_session::Relation;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::PayloadSlot;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::RecursionIndex;
    use gandr_core_term::session::SessionType;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::FieldLabel;
    use quenchant_shape::shape::Maybe;

    use super::relate;
    use crate::CheckBudget;
    use crate::CheckingContext;

    /// The session type over `syntax` rooted at its first node, its payloads
    /// `payloads`, at `state`.
    ///
    /// # Specification
    /// trivial.
    fn session(
        arena: &mut CoreArena,
        syntax: Vec<ProtocolSyntax>,
        payloads: &[ValueTypeId],
        state: ProtocolState,
    ) -> ValueTypeId
    {
        let protocol = Protocol::new(
            syntax,
            ProtocolState::from(0_usize),
            PayloadCount::from(payloads.len()),
        )
        .unwrap();
        let session = SessionType::new(Arc::new(protocol), Arc::from(payloads))
            .unwrap()
            .at(state)
            .unwrap();
        arena.value_type_session(session)
    }

    #[test]
    fn equivalence_sees_through_unfolding_and_payloads()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        // mu t. !Integer. t
        let folded = |arena: &mut CoreArena, payload| {
            session(
                arena,
                alloc::vec![
                    ProtocolSyntax::Mu(ProtocolState::from(1_usize)),
                    ProtocolSyntax::Send {
                        payload: PayloadSlot::from(0_usize),
                        next: ProtocolState::from(2_usize),
                    },
                    ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
                ],
                &[payload],
                ProtocolState::from(0_usize),
            )
        };
        let left = folded(&mut arena, integer);
        let right = folded(&mut arena, string);
        // !Integer. mu t. !Integer. t, past its first send
        let unfolded = session(
            &mut arena,
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(1_usize),
                    next: ProtocolState::from(3_usize),
                },
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ],
            &[string, integer],
            ProtocolState::from(1_usize),
        );
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            relate(&context, left, unfolded, Relation::Equivalent),
            Ok(Maybe::Present(alloc::vec![(integer, integer)])),
            "the binder past the prefix unfolds to the folded body, payload by payload"
        );
        assert_eq!(
            relate(&context, left, right, Relation::Equivalent),
            Ok(Maybe::Present(alloc::vec![(integer, string)])),
            "the shapes relate and the differing payload pair is handed to conversion"
        );
    }

    #[test]
    fn subtyping_follows_gay_and_hole_at_endpoints()
    {
        let mut arena = CoreArena::new();
        let choice = |arena: &mut CoreArena, labels: &[&str]| {
            let mut syntax = alloc::vec![ProtocolSyntax::Select(
                labels
                    .iter()
                    .enumerate()
                    .map(|(position, &label)| {
                        (
                            FieldLabel::from(alloc::string::String::from(label)),
                            ProtocolState::from(position.saturating_add(1)),
                        )
                    })
                    .collect::<BTreeMap<_, _>>()
            )];
            syntax.extend(labels.iter().map(|_| ProtocolSyntax::End));
            session(arena, syntax, &[], ProtocolState::from(0_usize))
        };
        let narrow = choice(&mut arena, &["a"]);
        let wide = choice(&mut arena, &["a", "b"]);
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            relate(&context, narrow, wide, Relation::Subtype),
            Ok(Maybe::Present(Vec::new())),
            "fewer selections substitute for more"
        );
        assert_eq!(
            relate(&context, wide, narrow, Relation::Subtype),
            Ok(Maybe::Absent(super::related::Absent::Unrelated)),
            "more selections do not substitute for fewer"
        );
        assert_eq!(
            relate(&context, narrow, wide, Relation::Equivalent),
            Ok(Maybe::Absent(super::related::Absent::Unrelated)),
            "equivalence requires equal widths"
        );
    }
}
