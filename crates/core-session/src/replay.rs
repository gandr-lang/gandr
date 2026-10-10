//! Deterministic replay of endpoint-local recorded moves.

use crate::Action;
use crate::Label;
use crate::Node;
use crate::Session;
use crate::TypeError;
use crate::ValueTypeId;

/// An opaque value-body digest; replay never opens or interprets it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PayloadDigest(pub [u8; 32]);

/// A recorded payload's type identity and opaque body reference.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Payload
{
    /// The abstract payload type named by the protocol.
    pub identity: ValueTypeId,
    /// The body reference, carried without dereferencing.
    pub digest: PayloadDigest,
}

/// One action observed at the endpoint whose type is replayed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Move
{
    /// Send a typed digest.
    Send(Payload),
    /// Receive a typed digest.
    Receive(Payload),
    /// Choose a local branch.
    Select(Label),
    /// Observe the peer's branch choice.
    Offer(Label),
    /// Close the endpoint at `End`.
    End,
}

/// A zero-based move position, or the length of an incomplete run.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MoveIndex(pub usize);

/// Why an observed move cannot advance the expected state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// A move occurs at `End` other than its initial close, or after closure.
    ResumeAfterEnd,
    /// The current choice does not contain this label.
    WrongLabel,
    /// The observed action kind or direction differs from the expected action.
    WrongDirection,
    /// The payload's type identity differs from the expected identity.
    WrongPayloadIdentity,
}

/// A replay refusal carrying its position and expected observation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplayError
{
    /// An observed move violates the current state.
    Refused
    {
        /// Position of the refused move.
        at: MoveIndex,
        /// The expected endpoint action.
        expected: Action,
        /// The recorded action, including its opaque digest when present.
        observed: Move,
        /// The distinguishing refusal class.
        reason: Refusal,
    },
    /// The run stops without closing the endpoint.
    IncompleteRun
    {
        /// The next move's position.
        at: MoveIndex,
        /// The action still owed by the endpoint.
        expected: Action,
    },
    /// An internal type invariant was violated.
    InvalidType(TypeError),
}

impl core::fmt::Display for ReplayError
{
    /// Describe the refusal while leaving payload bodies opaque.
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
            | Self::Refused {
                at: MoveIndex(at),
                reason,
                ..
            } => {
                let reason = match reason {
                    | Refusal::ResumeAfterEnd => "resume after end",
                    | Refusal::WrongLabel => "wrong label",
                    | Refusal::WrongDirection => "wrong direction",
                    | Refusal::WrongPayloadIdentity => "wrong payload identity",
                };
                write!(f, "move {at}: {reason}")
            },
            | Self::IncompleteRun {
                at: MoveIndex(at), ..
            } => write!(f, "incomplete run at move {at}"),
            | Self::InvalidType(ref error) => core::fmt::Display::fmt(error, f),
        }
    }
}

impl core::error::Error for ReplayError
{
}

/// A run reached `End`, closed it, and contained no later moves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Completion;

/// Replay an endpoint-local run against a validated session type.
///
/// # Specification
/// - ensures: accepts exactly runs whose directions, labels, and payload-type
///   identities follow the protocol and whose last move closes `End`.
/// - provides: conformance of the recorded skeleton; digests remain opaque.
/// - fails: wrong labels, directions, payload identities, incomplete runs, and
///   actions after end have distinct errors carrying the first failed position.
/// - panics: none.
///
/// # Errors
/// Returns [`ReplayError::Refused`] at the first violating move,
/// [`ReplayError::IncompleteRun`] if a close is still owed, or
/// [`ReplayError::InvalidType`] for a broken internal session invariant.
///
/// # Adequacy
/// - hypothesis: L2 generator and seat traces pin accepted actions; L3 each
///   direction, label, payload, truncation, and post-end twin pins its refusal
///   and position. Varying body digests preserves skeleton acceptance.
/// - witness: `tests::protocols::generator_duality_and_two_yields`
/// - witness: `tests::protocols::seat_duality_report_and_handoff`
/// - witness: `tests::monitor::refusals_preserve_the_accepted_prefix`
/// - witness: `tests::monitor::end_and_incomplete_runs_are_distinct`
#[inline]
pub fn replay(
    session: &Session,
    moves: &[Move],
) -> Result<Completion, ReplayError>
{
    let mut current = session.root();
    let mut closed = false;
    for (index, movement) in moves.iter().enumerate() {
        let (id, node) = session.head(current).map_err(ReplayError::InvalidType)?;
        let expected = node.action(id).map_err(ReplayError::InvalidType)?;
        let refused = |reason| ReplayError::Refused {
            at: MoveIndex(index),
            expected,
            observed: movement.clone(),
            reason,
        };
        if closed {
            return Err(refused(Refusal::ResumeAfterEnd));
        }
        match (node, movement) {
            | (&Node::Send(identity, next), &Move::Send(payload))
            | (&Node::Receive(identity, next), &Move::Receive(payload)) => {
                if identity != payload.identity {
                    return Err(refused(Refusal::WrongPayloadIdentity));
                }
                current = next;
            },
            | (&Node::Select(ref branches), &Move::Select(ref label))
            | (&Node::Offer(ref branches), &Move::Offer(ref label)) => {
                let Some(&next) = branches.get(label)
                else {
                    return Err(refused(Refusal::WrongLabel));
                };
                current = next;
            },
            | (&Node::End, &Move::End) => closed = true,
            | (&Node::End, _) => return Err(refused(Refusal::ResumeAfterEnd)),
            | _ => return Err(refused(Refusal::WrongDirection)),
        }
    }
    if closed {
        return Ok(Completion);
    }
    let (id, node) = session.head(current).map_err(ReplayError::InvalidType)?;
    let expected = node.action(id).map_err(ReplayError::InvalidType)?;
    Err(ReplayError::IncompleteRun {
        at: MoveIndex(moves.len()),
        expected,
    })
}
