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
//!
//! The web depends on which way each move faces the channel and on nothing
//! else, so [`DialogueWeb::of`] builds it from the moves' [`Facing`] alone, as
//! a run reads it from a dialogue already admitted, and
//! [`DialogueWeb::decompose`] reads its modular decomposition back as the
//! nodes a gandr program sees: series, parallel and prime, over events named
//! by their endpoint and their position among its moves.

use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::session::Endpoint;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::WebPiece;
use gandr_theory_deep_inference::DecompositionRefusal;
use gandr_theory_deep_inference::DependenceBits;
use gandr_theory_deep_inference::LinearizationRefusal;
use gandr_theory_deep_inference::ModularNode;
use gandr_theory_deep_inference::WebRelation;
use gandr_theory_deep_inference::WebVertex;
use gandr_theory_deep_inference::WebVertexCount;
use quenchant_shape::shape::Maybe;

use crate::replay::Move;
use crate::replay::MoveIndex;
use crate::replay::ReplayError;
use crate::replay::replay;
use crate::session::Session;

/// Which way a move faces the channel.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Facing
{
    /// A send or a selection: out to the other endpoint.
    Out,
    /// A receipt or an offer: in from the other endpoint.
    In,
    /// A close: neither.
    Neither,
}

impl Facing
{
    /// The way the recorded move `movement` faces the channel.
    ///
    /// # Specification
    /// - ensures: [`Facing::Out`] for a send and a selection, [`Facing::In`]
    ///   for a receipt and an offer, [`Facing::Neither`] for a close.
    /// - panics: none.
    /// - executable: none — the clause is the body's table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dialogue's sends and receipts read as the edges its
    ///   decomposition orders.
    /// - witness: `tests::dialogue::one_message_decomposes_as_its_send_before_both_tails`
    #[inline]
    #[must_use]
    pub const fn of<V>(movement: &RecordedMove<V>) -> Self
    {
        match *movement {
            RecordedMove::Sent(_) | RecordedMove::Selected(_) => Self::Out,
            RecordedMove::Received(_) | RecordedMove::Offered(_) => Self::In,
            RecordedMove::Closed => Self::Neither,
        }
    }

    /// The way the replayed move `movement` faces the channel.
    ///
    /// # Specification
    /// - ensures: as [`Facing::of`], a replayed end a close.
    /// - panics: none.
    /// - executable: none — the clause is the body's table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`admit`].
    /// - witness: `tests::dialogue::the_seat_and_operator_dialogue_is_one_linearization_of_its_web`
    const fn of_move(movement: &Move) -> Self
    {
        match *movement {
            Move::Send(_) | Move::Select(_) => Self::Out,
            Move::Receive(_) | Move::Offer(_) => Self::In,
            Move::End => Self::Neither,
        }
    }
}

/// One recorded move and the endpoint that made it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Turn
{
    /// The endpoint.
    pub side: Endpoint,
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
    pub side: Endpoint,
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
        side: Endpoint,
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

/// The causal web of a dialogue: its events and their precedence.
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
    /// The causal web of a dialogue whose moves, in the order logged, face
    /// the channel as `turns` do: each endpoint's own order, and the `k`-th
    /// move out of one endpoint before the `k`-th move into the other.
    ///
    /// # Specification
    /// - ensures: one vertex per turn, the left endpoint's first; an edge from
    ///   each of an endpoint's moves to its next, and from the `k`-th move out
    ///   of one endpoint to the `k`-th move into the other, closed under
    ///   transitivity; a move out or in with no partner on the other endpoint
    ///   bears no cross edge.
    /// - panics: none.
    /// - executable: none — the clause would build the same edges again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one message decomposes to its send before the two
    ///   endpoints' tails side by side, and two sends queued before the first
    ///   receipt leave a prime node.
    /// - witness: `tests::dialogue::one_message_decomposes_as_its_send_before_both_tails`
    /// - witness: `tests::dialogue::queued_sends_leave_a_prime_node`
    #[inline]
    #[must_use]
    pub fn of<Turns>(turns: Turns) -> Self
    where
        Turns: IntoIterator<Item = (Endpoint, Facing)>,
    {
        let (mut left, mut right) = (Vec::new(), Vec::new());
        for (endpoint, facing) in turns {
            match endpoint {
                Endpoint::Left => left.push(facing),
                Endpoint::Right => right.push(facing),
            }
        }
        let mut web = Self {
            left: left.len(),
            right: right.len(),
            precedes: DependenceBits::closure(WebVertexCount::from(0_usize), &[]),
        };
        let mut edges =
            Vec::with_capacity(left.len().saturating_add(right.len()).saturating_mul(2));
        for (side, facings) in [(Endpoint::Left, &left), (Endpoint::Right, &right)] {
            for at in 1 .. facings.len() {
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
            (Endpoint::Left, &left, Endpoint::Right, &right),
            (Endpoint::Right, &right, Endpoint::Left, &left),
        ] {
            let outputs = sent
                .iter()
                .enumerate()
                .filter(|&(_, &facing)| facing == Facing::Out);
            let inputs = received
                .iter()
                .enumerate()
                .filter(|&(_, &facing)| facing == Facing::In);
            for ((out, _), (into, _)) in outputs.zip(inputs) {
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
        }
        web.precedes = DependenceBits::closure(
            WebVertexCount::from(web.left.saturating_add(web.right)),
            &edges,
        );
        web
    }

    /// The modular decomposition of the web, its nodes in preorder: each
    /// series, parallel or prime node before its factors, an event as its
    /// endpoint and its position among that endpoint's moves.
    ///
    /// # Specification
    /// - ensures: one piece per node of the decomposition of the web's
    ///   precedence, in its factor order (parallel and prime factors by least
    ///   event, the left endpoint's events before the right's; series factors
    ///   earliest first); no piece for a web of no event.
    /// - fails: [`DecompositionRefusal::Cyclic`] for a web whose edges close a
    ///   cycle, which no admitted dialogue's do.
    /// - panics: none.
    /// - executable: none — the clause would decompose the web again.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one message decomposes to its send before the two
    ///   endpoints' tails side by side, two sends queued before the first
    ///   receipt leave a prime node over the rest, and a deadlocked shape is
    ///   refused by its cycle.
    /// - witness: `tests::dialogue::one_message_decomposes_as_its_send_before_both_tails`
    /// - witness: `tests::dialogue::queued_sends_leave_a_prime_node`
    /// - witness: `tests::dialogue::a_deadlocked_shape_has_no_decomposition`
    #[inline]
    pub fn decompose(&self) -> Result<Arc<[WebPiece]>, DecompositionRefusal>
    {
        let tree = self.precedes.decompose()?;
        let Maybe::Present(root) = tree.root()
        else {
            return Ok(Arc::from([]));
        };
        let mut pieces = Vec::with_capacity(usize::from(tree.node_count()));
        let mut pending = Vec::from([root]);
        while let Some(id) = pending.pop() {
            let Maybe::Present(node) = tree.node(id)
            else {
                return Err(DecompositionRefusal::Malformed);
            };
            let (piece, factors) = match *node {
                ModularNode::Event(vertex) => {
                    let Event {
                        side,
                        at: MoveIndex(index),
                    } = self.event(vertex);
                    pieces.push(WebPiece::Event {
                        endpoint: side,
                        index,
                    });
                    continue;
                },
                ModularNode::Par(ref factors) => (WebPiece::Parallel(factors.len()), factors),
                ModularNode::Seq(ref factors) => (WebPiece::Series(factors.len()), factors),
                ModularNode::Prime { ref factors, .. } => (WebPiece::Prime(factors.len()), factors),
            };
            pieces.push(piece);
            pending.extend(factors.iter().rev().copied());
        }
        Ok(Arc::from(pieces))
    }

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
            Endpoint::Left if at < self.left => at,
            Endpoint::Right if at < self.right => self.left.saturating_add(at),
            Endpoint::Left | Endpoint::Right => self.left.saturating_add(self.right),
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
                side: Endpoint::Left,
                at: MoveIndex(vertex),
            }
        }
        else {
            Event {
                side: Endpoint::Right,
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
            Endpoint::Left => left.push(turn.movement.clone()),
            Endpoint::Right => right.push(turn.movement.clone()),
        }
    }
    let _completion = replay(protocols.0, &left).map_err(|error| DialogueRefusal::Replay {
        side: Endpoint::Left,
        error,
    })?;
    let _completion = replay(protocols.1, &right).map_err(|error| DialogueRefusal::Replay {
        side: Endpoint::Right,
        error,
    })?;
    for (sender, sent, receiver, received) in [
        (Endpoint::Left, &left, Endpoint::Right, &right),
        (Endpoint::Right, &right, Endpoint::Left, &left),
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
            let Some((_, input)) = inputs.next()
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
    let web = DialogueWeb::of(
        dialogue
            .iter()
            .map(|turn| (turn.side, Facing::of_move(&turn.movement))),
    );
    let (mut lefts, mut rights) = (0_usize, 0_usize);
    let mut run = Vec::with_capacity(dialogue.len());
    for turn in dialogue {
        let count = match turn.side {
            Endpoint::Left => &mut lefts,
            Endpoint::Right => &mut rights,
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
