//! A traced run's record of its channels: each channel's play, the moves its
//! two ends made in the order the run made them, a dialogue whose
//! [`DialogueWeb`] its causal web is.
//!
//! A run records only when its caller asks ([`crate::RunInputs::traced`]);
//! otherwise the scheduler keeps no play, and a run pays nothing for one. A
//! channel's left endpoint is the end its fork's child holds, at the fork's
//! protocol, and its right the forking task's, at the dual, as a dialogue
//! literal names them. A payload is recorded as the value it moves into the
//! caller's store, and an end sent as a payload as the channel and the side it
//! names.

use alloc::vec::Vec;

use gandr_core_sequent::CommandId;
use gandr_core_sequent::HeapValueId;
use gandr_core_session::DialogueWeb;
use gandr_core_session::Facing;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;

/// A task of a traced run: the root, numbered zero, or a fork's child,
/// numbered in the order its fork ran.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TaskNumber(pub usize);

/// A channel of a traced run, numbered in the order its fork ran.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChannelNumber(pub usize);

/// What a send carried and its receipt took.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Carried
{
    /// A value, as it moved into the caller's store.
    Value(HeapValueId),
    /// An end of a channel, delegated.
    End
    {
        /// The channel.
        channel: ChannelNumber,
        /// Its end.
        side: Endpoint,
    },
}

/// One move of a channel's play: the task that made it, the end it made it
/// at, and the move.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Played
{
    /// The task.
    pub task: TaskNumber,
    /// The end.
    pub side: Endpoint,
    /// The move.
    pub movement: RecordedMove<Carried>,
}

/// One channel's play: the fork that opened it and every move its ends made,
/// in the order the run made them.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Play
{
    /// The fork.
    pub fork: CommandId,
    /// The moves.
    pub moves: Vec<Played>,
}

impl Play
{
    /// The causal web of the play: each end's own order, and each move out
    /// of one end before the matching move into the other.
    ///
    /// # Specification
    /// - ensures: [`DialogueWeb::of`] over the moves' ends and the ways they
    ///   face the channel, in the order played.
    /// - panics: none.
    /// - executable: none — the clause is the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run whose two children each send once and receive
    ///   once decomposes each channel to the web its order forces, and the
    ///   corpus's traced runs settle the webs their sources state.
    /// - witness: `tests::sessions::a_traced_run_plays_each_channel_as_its_dialogue`
    #[inline]
    #[must_use]
    pub fn web(&self) -> DialogueWeb
    {
        DialogueWeb::of(
            self.moves
                .iter()
                .map(|played| (played.side, Facing::of(&played.movement))),
        )
    }
}

/// A traced run's plays, one per channel, in the order its fork ran; a
/// traced run of several commands, a thunk forced after its return, appends
/// each command's.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Trace
{
    /// The plays.
    pub plays: Vec<Play>,
}
