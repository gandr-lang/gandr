//! Candidate code export and recorded-run transport through kernel `Flow_U`.
//!
//! The producer retains its finite search; the kernel independently replays
//! its relation. Recorded bodies stay opaque. This module checks the binding
//! between monitor identities and native payload codes before using a Flow.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_core::Convertibility;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::convertible_value_types;
use gandr_kernel_core::flow_universe::Certificate;
use gandr_kernel_core::flow_universe::CertificateType;
use gandr_kernel_core::flow_universe::Family;
use gandr_kernel_core::flow_universe::Flow;
use gandr_kernel_core::flow_universe::FlowError;
use gandr_kernel_core::flow_universe::Flows;
use gandr_kernel_core::flow_universe::form_certificate;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId as CodeType;
use gandr_kernel_term::session::Graph;
use gandr_kernel_term::session::Label as CodeLabel;
use gandr_kernel_term::session::Node as CodeNode;
use gandr_kernel_term::session::PayloadSlot;
use gandr_kernel_term::session::State;
use gandr_kernel_term::session::StatePair;

use crate::Move;
use crate::MoveIndex;
use crate::Node;
use crate::Payload;
use crate::Refusal;
use crate::ReplayError;
use crate::Session;
use crate::TypeError;
use crate::ValueTypeId;
use crate::replay;

/// Native type codes assigned to the monitor's opaque payload identities.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct PayloadCodes(pub BTreeMap<ValueTypeId, CodeType>);

/// A monitor protocol claimed to denote one quoted native session code.
///
/// Fields are untrusted input, not a cached certificate. Every transport
/// validates the full binding against the current native arena.
#[derive(Clone, Copy)]
pub struct Protocol<'protocol>
{
    /// The endpoint-local protocol the independent monitor reads.
    pub session: &'protocol Session,
    /// Quoted native session code.
    pub code: ValueId,
    /// Payload identities interpreted as native codes.
    pub payloads: &'protocol PayloadCodes,
}

/// Code export, certificate replay, binding or recorded-run refusal.
#[derive(Debug)]
pub enum TransportError
{
    /// A protocol payload has no native code assignment.
    MissingPayload(ValueTypeId),
    /// The monitor protocol does not denote the supplied native code.
    CodeBinding,
    /// The supplied protocol order disagrees with the certified Flow direction.
    Direction,
    /// A recorded run requires a direct session simulation introduction.
    ExpectedSessionFlow,
    /// Kernel certificate formation refused.
    Flow(FlowError),
    /// A monitor type invariant failed.
    Type(TypeError),
    /// Kernel graph inspection refused.
    Session(gandr_kernel_core::session::SessionError),
    /// The source or target monitor refused the recorded skeleton.
    Replay(ReplayError),
    /// A move is not covered by the directional relation or target choice.
    Move
    {
        /// First refused move position.
        at: MoveIndex,
        /// Named action refusal.
        reason: Refusal,
    },
}

impl core::fmt::Display for TransportError
{
    /// Render the named boundary refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::MissingPayload(_) => {
                f.write_str("recorded payload identity has no native code")
            },
            | Self::CodeBinding => f.write_str("monitor protocol and native session code disagree"),
            | Self::Direction => f.write_str("session Flow direction mismatch"),
            | Self::ExpectedSessionFlow => {
                f.write_str("recorded run requires a session Flow introduction")
            },
            | Self::Flow(ref error) => core::fmt::Display::fmt(error, f),
            | Self::Type(ref error) => core::fmt::Display::fmt(error, f),
            | Self::Session(ref error) => core::fmt::Display::fmt(error, f),
            | Self::Replay(ref error) => core::fmt::Display::fmt(error, f),
            | Self::Move { at, reason } => {
                let reason = match reason {
                    | Refusal::ResumeAfterEnd => "resume after end",
                    | Refusal::WrongLabel => "wrong label",
                    | Refusal::WrongDirection => "wrong direction",
                    | Refusal::WrongPayloadIdentity => "wrong payload identity",
                };
                write!(f, "unmapped session move {}: {reason}", at.0)
            },
        }
    }
}
impl core::error::Error for TransportError
{
}

/// Export finite native syntax with payload identities replaced by code slots.
///
/// # Specification
/// - ensures: preserves every action, label, binder and continuation; sorted
///   payload identities determine telescope slots. No proof verdict is minted.
/// - fails: `MissingPayload` if any action lacks a native type assignment.
/// - panics: none.
///
/// # Errors
/// `TransportError::MissingPayload`.
///
/// # Adequacy
/// - hypothesis: L1 ordinary kernel admission rechecks exported code; L3
///   incomplete payload assignments and tampered bindings refuse.
/// - witness: `tests::certified::recorded_runs_transport_only_forward`
#[spec(ensures: |ret| match ret {
    Ok(code) => matches!(arena.value(code), Some(&Value::Quote(ty))
        if matches!(arena.value_type(ty), Some(gandr_kernel_term::ValueType::Session { graph, .. })
            if graph.root.0 == session.root().0 && graph.nodes.len() == session.nodes().len())),
    Err(TransportError::MissingPayload(identity)) => !payloads.0.contains_key(&identity),
    Err(_) => false,
})]
#[inline]
pub fn encode(
    arena: &mut TermArena,
    session: &Session,
    payloads: &PayloadCodes,
) -> Result<ValueId, TransportError>
{
    let slots: BTreeMap<_, _> = payloads
        .0
        .keys()
        .enumerate()
        .map(|(index, identity)| (*identity, PayloadSlot(index)))
        .collect();
    let mut nodes = Vec::with_capacity(session.nodes().len());
    for node in session.nodes() {
        nodes.push(match *node {
            | Node::Send(identity, next) | Node::Receive(identity, next) => {
                let slot = *slots
                    .get(&identity)
                    .ok_or(TransportError::MissingPayload(identity))?;
                if matches!(*node, Node::Send(..)) {
                    CodeNode::Send(slot, State(next.0))
                }
                else {
                    CodeNode::Receive(slot, State(next.0))
                }
            },
            | Node::Select(ref branches) | Node::Offer(ref branches) => {
                let branches = branches
                    .iter()
                    .map(|(label, next)| (CodeLabel(label.0.clone()), State(next.0)))
                    .collect();
                if matches!(*node, Node::Select(_)) {
                    CodeNode::Select(branches)
                }
                else {
                    CodeNode::Offer(branches)
                }
            },
            | Node::End => CodeNode::End,
            | Node::Mu(body) => CodeNode::Mu(State(body.0)),
            | Node::Var(binder) => CodeNode::Var(State(binder.0)),
        });
    }
    let mut telescope = arena.value_type_unit();
    for &code in payloads.0.values().rev() {
        telescope = arena.value_type_product(code, telescope);
    }
    let graph = Arc::new(Graph {
        nodes,
        root: State(session.root().0),
    });
    let code = arena.value_type_session(graph, telescope);
    Ok(arena.value_quote(code))
}

/// Verify the entire monitor/code binding, not merely the current action.
///
/// # Specification
/// - ensures: graph positions, binding, labels, directions and every payload
///   assignment agree with the monitor protocol.
/// - fails: a malformed code or any binding mismatch is named.
/// - panics: none.
///
/// # Errors
/// `CodeBinding`, `MissingPayload`, or `Session`.
///
/// # Adequacy
/// - hypothesis: L3 swapping a monitor's payload assignment or protocol cannot
///   reuse another protocol's certified code.
/// - witness: `tests::certified::recorded_runs_transport_only_forward`
#[spec(ensures: |ret| match ret {
    Ok(code) => matches!(arena.value(protocol.code), Some(&Value::Quote(quoted)) if quoted == code),
    Err(TransportError::MissingPayload(identity)) => !protocol.payloads.0.contains_key(&identity),
    Err(_) => true,
})]
fn binding(
    arena: &TermArena,
    protocol: Protocol<'_>,
) -> Result<CodeType, TransportError>
{
    let Some(&Value::Quote(code)) = arena.value(protocol.code)
    else {
        return Err(TransportError::CodeBinding);
    };
    let (graph, fields) =
        gandr_kernel_core::session::view(arena, code).map_err(TransportError::Session)?;
    let fields = gandr_kernel_core::session::payload_codes(arena, fields)
        .map_err(TransportError::Session)?;
    if graph.root.0 != protocol.session.root().0
        || graph.nodes.len() != protocol.session.nodes().len()
    {
        return Err(TransportError::CodeBinding);
    }
    for (native, local) in graph.nodes.iter().zip(protocol.session.nodes()) {
        if let CodeNode::Select(ref branches) | CodeNode::Offer(ref branches) = *native {
            let local = match *local {
                | Node::Select(ref branches) if matches!(*native, CodeNode::Select(_)) => branches,
                | Node::Offer(ref branches) if matches!(*native, CodeNode::Offer(_)) => branches,
                | _ => return Err(TransportError::CodeBinding),
            };
            if branches.len() != local.len()
                || !branches
                    .iter()
                    .zip(local)
                    .all(|((a, x), (b, y))| a.0 == b.0 && x.0 == y.0)
            {
                return Err(TransportError::CodeBinding);
            }
            continue;
        }
        match (native, local) {
            | (&CodeNode::Send(slot, next), &Node::Send(identity, continuation))
            | (&CodeNode::Receive(slot, next), &Node::Receive(identity, continuation)) => {
                let expected = *protocol
                    .payloads
                    .0
                    .get(&identity)
                    .ok_or(TransportError::MissingPayload(identity))?;
                let actual = *fields.get(slot.0).ok_or(TransportError::CodeBinding)?;
                if next.0 != continuation.0
                    || convertible_value_types(arena, expected, actual)
                        != Convertibility::Convertible
                {
                    return Err(TransportError::CodeBinding);
                }
            },
            | (&CodeNode::Mu(a), &Node::Mu(b)) | (&CodeNode::Var(a), &Node::Var(b)) if a.0 == b.0 =>
                {},
            | (&CodeNode::End, &Node::End) => {},
            | _ => return Err(TransportError::CodeBinding),
        }
    }
    Ok(code)
}

/// Transport a complete recorded skeleton along a freshly replayed `Flow_U`.
///
/// # Specification
/// - ensures: both monitors accept; each move follows a supplied related pair;
///   labels and payload digests are unchanged, while payload identities use the
///   target protocol's certified code assignment. Native intermediates are
///   truncated on every exit. No payload body is read.
/// - fails: wrong family, simulation, direction, code binding or source run; a
///   source-only offered label also refuses, since width subtyping narrows the
///   target peer's choices. There is no inverse operation.
/// - panics: none.
///
/// # Errors
/// `TransportError` names the certificate, binding, monitor or move boundary.
///
/// # Adequacy
/// - hypothesis: L1 the target monitor checks transported `SeatEnd` runs; L3
///   backward pause, removed offers, changed digests and wrong bindings
///   distinguish direction, skeleton preservation and endpoint commitment.
/// - witness: `tests::certified::recorded_runs_transport_only_forward`
#[spec(captures: before = arena.watermark(), ensures: |ret| arena.watermark() == before && ret.as_ref().map_or(true, |output| {
    output.len() == moves.len() && output.iter().zip(moves).all(|(after, before)| match (after, before) {
        (&Move::Send(a), &Move::Send(b)) | (&Move::Receive(a), &Move::Receive(b)) => a.digest == b.digest,
        (&Move::Select(ref a), &Move::Select(ref b)) | (&Move::Offer(ref a), &Move::Offer(ref b)) => a == b,
        (&Move::End, &Move::End) => true,
        _ => false,
    })
}))]
#[inline]
pub fn transport(
    arena: &mut TermArena,
    flows: &Flows,
    certificate: Certificate,
    protocols: (Protocol<'_>, Protocol<'_>),
    moves: &[Move],
    budget: ReplayBudget,
) -> Result<Vec<Move>, TransportError>
{
    let watermark = arena.watermark();
    let result = checked_transport(arena, flows, certificate, protocols, moves, budget);
    arena.truncate_to(watermark);
    result
}

/// Replay inside the watermark boundary, then advance both finite states.
///
/// # Specification
/// - requires: caller restores the entry arena watermark on every exit.
/// - ensures: the public transport's output and refusals, retaining temporary
///   native proof classifiers until the caller restores its watermark.
/// - fails: the public transport's named errors.
/// - panics: none.
///
/// # Errors
/// `TransportError`.
///
/// # Adequacy
/// - hypothesis: L1 target-monitor acceptance is independent of move mapping.
/// - witness: `tests::certified::recorded_runs_transport_only_forward`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |output| replay(protocols.0.session, moves) == Ok(crate::Completion)
    && replay(protocols.1.session, output) == Ok(crate::Completion)))]
fn checked_transport(
    arena: &mut TermArena,
    flows: &Flows,
    certificate: Certificate,
    protocols: (Protocol<'_>, Protocol<'_>),
    moves: &[Move],
    budget: ReplayBudget,
) -> Result<Vec<Move>, TransportError>
{
    let classifier = form_certificate(arena, flows, certificate, Family::Flow, budget)
        .map_err(TransportError::Flow)?;
    let CertificateType::Flow(classifier) = classifier
    else {
        return Err(TransportError::ExpectedSessionFlow);
    };
    let Certificate::Flow(id) = certificate
    else {
        return Err(TransportError::ExpectedSessionFlow);
    };
    let Flow::Session { ref evidence, .. } = *flows.get(id).map_err(TransportError::Flow)?
    else {
        return Err(TransportError::ExpectedSessionFlow);
    };
    let (source, target) = protocols;
    let source_code = binding(arena, source)?;
    let target_code = binding(arena, target)?;
    if convertible_value_types(arena, classifier.source, source_code) != Convertibility::Convertible
        || convertible_value_types(arena, classifier.target, target_code)
            != Convertibility::Convertible
    {
        return Err(TransportError::Direction);
    }
    replay(source.session, moves).map_err(TransportError::Replay)?;
    let mut source_state = source.session.root();
    let mut target_state = target.session.root();
    let mut output = Vec::with_capacity(moves.len());
    for (index, movement) in moves.iter().enumerate() {
        let (left, a) = source
            .session
            .head(source_state)
            .map_err(TransportError::Type)?;
        let (right, b) = target
            .session
            .head(target_state)
            .map_err(TransportError::Type)?;
        let refusal = |reason| TransportError::Move {
            at: MoveIndex(index),
            reason,
        };
        if !evidence.pairs.contains(&StatePair {
            source: State(left.0),
            target: State(right.0),
        }) {
            return Err(refusal(Refusal::WrongDirection));
        }
        if let Move::Select(ref label) | Move::Offer(ref label) = *movement {
            let source = match *a {
                | Node::Select(ref labels) if matches!(*movement, Move::Select(_)) => labels,
                | Node::Offer(ref labels) if matches!(*movement, Move::Offer(_)) => labels,
                | _ => return Err(refusal(Refusal::WrongDirection)),
            };
            let target = match *b {
                | Node::Select(ref labels) if matches!(*movement, Move::Select(_)) => labels,
                | Node::Offer(ref labels) if matches!(*movement, Move::Offer(_)) => labels,
                | _ => return Err(refusal(Refusal::WrongDirection)),
            };
            source_state = *source
                .get(label)
                .ok_or_else(|| refusal(Refusal::WrongLabel))?;
            target_state = *target
                .get(label)
                .ok_or_else(|| refusal(Refusal::WrongLabel))?;
            output.push(movement.clone());
            continue;
        }
        let mapped = match (a, b, movement) {
            | (&Node::Send(_, next_a), &Node::Send(identity, next_b), &Move::Send(payload)) => {
                source_state = next_a;
                target_state = next_b;
                Move::Send(Payload {
                    identity,
                    digest: payload.digest,
                })
            },
            | (
                &Node::Receive(_, next_a),
                &Node::Receive(identity, next_b),
                &Move::Receive(payload),
            ) => {
                source_state = next_a;
                target_state = next_b;
                Move::Receive(Payload {
                    identity,
                    digest: payload.digest,
                })
            },
            | (&Node::End, &Node::End, &Move::End) => Move::End,
            | _ => return Err(refusal(Refusal::WrongDirection)),
        };
        output.push(mapped);
    }
    replay(target.session, &output).map_err(TransportError::Replay)?;
    Ok(output)
}
