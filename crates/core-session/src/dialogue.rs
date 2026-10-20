//! A binary session's recorded dialogue: both endpoints' moves in the one
//! order a recorder saw them.
//!
//! A dialogue's logical time is a web, not its recorded order. Its events are
//! the endpoints' moves. Its green edges are each endpoint's own order and,
//! for every message, the send before its receipt: the `k`-th send or
//! selection one endpoint makes precedes the `k`-th receipt or offer the other
//! observes. Every other pair of events is independent. [`admit`] builds that
//! web from the two endpoints' moves and admits the dialogue exactly when each
//! endpoint's moves replay against its protocol and the recorded order is one
//! linearization of the web, the slice rule's reading of a partial order as
//! the set of its linear extensions. Every recorder's interleaving of one run
//! is admitted alike, and the answer's [`DialogueWeb::relation`] reads
//! `a ≺ b` on any two of its events.

use alloc::vec::Vec;

use gandr_theory_deep_inference::DependenceBits;
use gandr_theory_deep_inference::LinearizationRefusal;
use gandr_theory_deep_inference::WebRelation;
use gandr_theory_deep_inference::WebVertex;
use gandr_theory_deep_inference::WebVertexCount;

use crate::replay::Move;
use crate::replay::MoveIndex;
use crate::replay::ReplayError;
use crate::replay::replay;
use crate::session::Session;

/// Which endpoint of a binary session moved.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Side
{
    /// The first endpoint of the pair [`admit`] reads.
    Left,
    /// The second.
    Right,
}

/// One recorded move and the endpoint that made it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Turn
{
    /// The endpoint.
    pub side: Side,
    /// Its move.
    pub movement: Move,
}

/// One event of a dialogue: an endpoint's move, placed among that endpoint's
/// own moves.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Event
{
    /// The endpoint.
    pub side: Side,
    /// The move's position among the endpoint's own moves.
    pub at: MoveIndex,
}

/// Why a recorded dialogue is not a run of its session.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DialogueRefusal
{
    /// One endpoint's moves do not replay against its protocol.
    Replay
    {
        /// The endpoint.
        side: Side,
        /// The replay's refusal, its positions the endpoint's own.
        error: ReplayError,
    },
    /// A send or a selection with no receipt or offer on the other endpoint
    /// that agrees with it, or a receipt or an offer with no send or
    /// selection to match.
    Unmatched
    {
        /// The unmatched event.
        event: Event,
    },
    /// The dialogue records `later` before `earlier`, where the session's web
    /// orders `earlier` first: the green edge the recorded order inverts.
    Inverted
    {
        /// The edge's source, recorded second.
        earlier: Event,
        /// The edge's target, recorded first.
        later: Event,
    },
    /// The recorded order does not name the web's events once each. A
    /// dialogue's own events build its web, so [`admit`] never answers this;
    /// it carries the web's refusal.
    Uncovered(LinearizationRefusal),
}

/// The causal web of an admitted dialogue: its events and their precedence.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DialogueWeb
{
    /// How many moves the left endpoint made; its events are the web's first
    /// vertices, the right endpoint's after them.
    left: usize,
    /// How many moves the right endpoint made.
    right: usize,
    /// The transitive precedence over the events.
    precedes: DependenceBits,
}

impl DialogueWeb
{
    /// The web's vertex for `event`.
    ///
    /// # Specification
    /// - ensures: the left endpoint's events first, in their own order, then
    ///   the right endpoint's; an event past its endpoint's moves maps past the
    ///   web's vertices.
    /// - panics: none.
    /// - executable: none — the clause is the body's arithmetic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a send and its receipt on opposite endpoints read as
    ///   one green edge, and the last events of the two endpoints as
    ///   independent.
    /// - witness: `tests::dialogue::the_seat_and_operator_dialogue_is_one_linearization_of_its_web`
    fn vertex(
        &self,
        event: Event,
    ) -> WebVertex
    {
        let MoveIndex(at) = event.at;
        WebVertex::from(match event.side {
            Side::Left if at < self.left => at,
            Side::Right if at < self.right => self.left.saturating_add(at),
            Side::Left | Side::Right => self.left.saturating_add(self.right),
        })
    }

    /// The event at `vertex`, the inverse of [`Self::vertex`] inside the web.
    ///
    /// # Specification
    /// - ensures: [`Self::vertex`] of the answer is `vertex` for a vertex
    ///   inside the web.
    /// - panics: none.
    /// - executable: none — the clause is the body's arithmetic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an inverted receipt names the operator's send and the
    ///   seat's receipt, each at its own position.
    /// - witness: `tests::dialogue::a_receipt_recorded_before_its_send_is_refused_by_the_edge`
    fn event(
        &self,
        vertex: WebVertex,
    ) -> Event
    {
        let vertex = usize::from(vertex);
        if vertex < self.left {
            Event {
                side: Side::Left,
                at: MoveIndex(vertex),
            }
        }
        else {
            Event {
                side: Side::Right,
                at: MoveIndex(vertex.saturating_sub(self.left)),
            }
        }
    }

    /// The temporal judgement between two events: whether `first` happens
    /// before `second`, after it, or independently of it.
    ///
    /// # Specification
    /// - ensures: [`WebRelation::Precedes`] when a chain of the endpoints' own
    ///   orders and sends before receipts leads from `first` to `second`,
    ///   [`WebRelation::Follows`] for the converse,
    ///   [`WebRelation::Independent`] for two distinct events with neither, and
    ///   [`WebRelation::Missing`] for an event the dialogue lacks or one event
    ///   read against itself.
    /// - panics: none.
    /// - executable: none — the clause would read the same two bits.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a send precedes its receipt, a receipt follows its
    ///   send, two closings on opposite endpoints are independent, and an event
    ///   past an endpoint's moves is missing.
    /// - witness: `tests::dialogue::the_seat_and_operator_dialogue_is_one_linearization_of_its_web`
    #[inline]
    #[must_use]
    pub fn relation(
        &self,
        first: Event,
        second: Event,
    ) -> WebRelation
    {
        let count = self.left.saturating_add(self.right);
        let (from, to) = (self.vertex(first), self.vertex(second));
        if usize::from(from) >= count || usize::from(to) >= count || from == to {
            return WebRelation::Missing;
        }
        if bool::from(self.precedes.contains(from, to)) {
            WebRelation::Precedes
        }
        else if bool::from(self.precedes.contains(to, from)) {
            WebRelation::Follows
        }
        else {
            WebRelation::Independent
        }
    }
}

/// Admit `dialogue` as a run of the binary session `protocols` types: the
/// left endpoint's protocol first.
///
/// # Specification
/// - ensures: on success the dialogue's web; each endpoint's moves, in the
///   dialogue's order, replay to completion against its protocol, every send
///   and selection is matched by the other endpoint's receipt or offer of the
///   same payload digest or label, in order, and the dialogue records each send
///   before its receipt.
/// - fails: [`DialogueRefusal::Replay`] for the left endpoint and then the
///   right whose moves do not replay; [`DialogueRefusal::Unmatched`] for the
///   first unmatched send or selection, left endpoint first, or the first
///   receipt or offer past the other endpoint's sends and selections;
///   [`DialogueRefusal::Inverted`] for the first edge, in recorded order of its
///   later-recorded end, that the dialogue records backwards.
/// - panics: none.
/// - executable: none — the clause would project and replay the dialogue again.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the seat and the operator's dialogue is admitted in two
///   interleavings; a receipt recorded before its send is refused by that edge;
///   a receipt of another digest is unmatched; and a move off its endpoint's
///   protocol is refused by its replay.
/// - witness: `tests::dialogue::the_seat_and_operator_dialogue_is_one_linearization_of_its_web`
/// - witness: `tests::dialogue::a_receipt_recorded_before_its_send_is_refused_by_the_edge`
/// - witness: `tests::dialogue::a_receipt_that_disagrees_with_its_send_is_unmatched`
/// - witness: `tests::dialogue::a_move_off_its_protocol_is_refused_by_its_replay`
#[inline]
pub fn admit(
    protocols: (&Session, &Session),
    dialogue: &[Turn],
) -> Result<DialogueWeb, DialogueRefusal>
{
    let mut left = Vec::new();
    let mut right = Vec::new();
    for turn in dialogue {
        match turn.side {
            Side::Left => left.push(turn.movement.clone()),
            Side::Right => right.push(turn.movement.clone()),
        }
    }
    let _completion = replay(protocols.0, &left).map_err(|error| DialogueRefusal::Replay {
        side: Side::Left,
        error,
    })?;
    let _completion = replay(protocols.1, &right).map_err(|error| DialogueRefusal::Replay {
        side: Side::Right,
        error,
    })?;
    let mut web = DialogueWeb {
        left: left.len(),
        right: right.len(),
        precedes: DependenceBits::closure(WebVertexCount::from(0_usize), &[]),
    };
    let mut edges = Vec::with_capacity(left.len().saturating_add(right.len()).saturating_mul(2));
    for (side, moves) in [(Side::Left, &left), (Side::Right, &right)] {
        for at in 1 .. moves.len() {
            edges.push((
                web.vertex(Event {
                    side,
                    at: MoveIndex(at.saturating_sub(1)),
                }),
                web.vertex(Event {
                    side,
                    at: MoveIndex(at),
                }),
            ));
        }
    }
    for (sender, sent, receiver, received) in [
        (Side::Left, &left, Side::Right, &right),
        (Side::Right, &right, Side::Left, &left),
    ] {
        let outputs = sent
            .iter()
            .enumerate()
            .filter(|&(_, movement)| matches!(*movement, Move::Send(_) | Move::Select(_)));
        let mut inputs = received
            .iter()
            .enumerate()
            .filter(|&(_, movement)| matches!(*movement, Move::Receive(_) | Move::Offer(_)));
        for (out, output) in outputs {
            let unmatched = DialogueRefusal::Unmatched {
                event: Event {
                    side: sender,
                    at: MoveIndex(out),
                },
            };
            let Some((into, input)) = inputs.next()
            else {
                return Err(unmatched);
            };
            // The receipt observes what the send put on the wire: the sent
            // payload, or the selected label.
            let agrees = match (output, input) {
                (&Move::Send(sent), &Move::Receive(received)) => sent == received,
                (&Move::Select(ref chosen), &Move::Offer(ref observed)) => chosen == observed,
                (
                    &(Move::Send(_)
                    | Move::Receive(_)
                    | Move::Select(_)
                    | Move::Offer(_)
                    | Move::End),
                    &(Move::Send(_)
                    | Move::Receive(_)
                    | Move::Select(_)
                    | Move::Offer(_)
                    | Move::End),
                ) => false,
            };
            if !agrees {
                return Err(unmatched);
            }
            edges.push((
                web.vertex(Event {
                    side: sender,
                    at: MoveIndex(out),
                }),
                web.vertex(Event {
                    side: receiver,
                    at: MoveIndex(into),
                }),
            ));
        }
        if let Some((into, _)) = inputs.next() {
            return Err(DialogueRefusal::Unmatched {
                event: Event {
                    side: receiver,
                    at: MoveIndex(into),
                },
            });
        }
    }
    web.precedes = DependenceBits::closure(
        WebVertexCount::from(web.left.saturating_add(web.right)),
        &edges,
    );
    let (mut lefts, mut rights) = (0_usize, 0_usize);
    let mut run = Vec::with_capacity(dialogue.len());
    for turn in dialogue {
        let count = match turn.side {
            Side::Left => &mut lefts,
            Side::Right => &mut rights,
        };
        run.push(web.vertex(Event {
            side: turn.side,
            at: MoveIndex(*count),
        }));
        *count = count.saturating_add(1);
    }
    match web.precedes.linearizes(&run) {
        Ok(()) => Ok(web),
        Err(LinearizationRefusal::Inverted { earlier, later }) => Err(DialogueRefusal::Inverted {
            earlier: web.event(earlier),
            later: web.event(later),
        }),
        Err(
            refusal @ (LinearizationRefusal::Unknown { .. }
            | LinearizationRefusal::Repeated { .. }
            | LinearizationRefusal::Omitted { .. }),
        ) => Err(DialogueRefusal::Uncovered(refusal)),
    }
}
