//! The refusals of the formation and the replay of a finite session.

use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::session::PayloadSlot;
use gandr_kernel_term::session::State;
use gandr_kernel_term::session::StatePair;

/// A finite session formation or replay refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SessionError
{
    /// A native reference does not resolve.
    Arena,
    /// An endpoint is not a session code.
    ExpectedSession(ValueTypeId),
    /// A graph edge is out of bounds.
    MissingState(State),
    /// A structural edge repeats a syntax occurrence.
    RepeatedState(State),
    /// A variable escapes its lexical binder.
    UnboundVariable(State),
    /// A Mu body exposes no action before another administrative edge.
    NonContractive(State),
    /// The graph contains unreachable syntax.
    UnreachableState(State),
    /// The payload-code telescope is not a product spine ending in Unit.
    PayloadTelescope,
    /// A payload slot is outside that telescope.
    MissingPayload(PayloadSlot),
    /// The supplied relation omits a required observable pair.
    MissingPair(StatePair),
    /// A supplied pair names Mu or Var instead of its resolved action.
    AdministrativePair(StatePair),
    /// The two actions have different kinds or directions.
    WrongAction(StatePair),
    /// A required label is missing or bisimulation widths differ.
    WrongLabels(StatePair),
    /// Different payload codes have no supplied native path obligation.
    PayloadMismatch(StatePair),
    /// A payload obligation is duplicated.
    DuplicatePayloadPath(PayloadSlot, PayloadSlot),
}

impl core::fmt::Display for SessionError
{
    /// Render a named refusal with the offending position.
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
            Self::Arena => f.write_str("unreadable session payload code"),
            Self::ExpectedSession(_) => f.write_str("expected a session code"),
            Self::MissingState(State(state)) => write!(f, "missing session state {state}"),
            Self::RepeatedState(State(state)) => write!(f, "repeated session occurrence {state}"),
            Self::UnboundVariable(State(state)) => {
                write!(f, "unbound session variable at {state}")
            },
            Self::NonContractive(State(state)) => {
                write!(f, "noncontractive session binder at {state}")
            },
            Self::UnreachableState(State(state)) => {
                write!(f, "unreachable session occurrence {state}")
            },
            Self::PayloadTelescope => f.write_str("session payload telescope must end in Unit"),
            Self::MissingPayload(PayloadSlot(slot)) => {
                write!(f, "missing session payload slot {slot}")
            },
            Self::MissingPair(pair) => write!(
                f,
                "missing session pair ({}, {})",
                pair.source.0, pair.target.0
            ),
            Self::AdministrativePair(pair) => write!(
                f,
                "session pair ({}, {}) is not observable",
                pair.source.0, pair.target.0
            ),
            Self::WrongAction(pair) => write!(
                f,
                "session action mismatch at ({}, {})",
                pair.source.0, pair.target.0
            ),
            Self::WrongLabels(pair) => write!(
                f,
                "session label mismatch at ({}, {})",
                pair.source.0, pair.target.0
            ),
            Self::PayloadMismatch(pair) => write!(
                f,
                "session payload mismatch at ({}, {})",
                pair.source.0, pair.target.0
            ),
            Self::DuplicatePayloadPath(PayloadSlot(source), PayloadSlot(target)) => {
                write!(f, "duplicate session payload path ({source}, {target})")
            },
        }
    }
}

impl core::error::Error for SessionError
{
}
