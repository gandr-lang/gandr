//! A recorded dialogue of the seat and the operator, admitted by its logical
//! time: each endpoint's moves replay against its protocol, and the recorded
//! order is one linearization of the session's causal web.

use gandr_core_session::DialogueRefusal;
use gandr_core_session::Event;
use gandr_core_session::Move;
use gandr_core_session::MoveIndex;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Payload;
use gandr_core_session::PayloadDigest;
use gandr_core_session::Refusal;
use gandr_core_session::ReplayError;
use gandr_core_session::Side;
use gandr_core_session::Turn;
use gandr_core_session::admit;
use gandr_theory_deep_inference::WebRelation;

use crate::common::DISPATCH;
use crate::common::REPORT;
use crate::common::operator;
use crate::common::payload;
use crate::common::seat;
use crate::common::session;

/// The operator's move, the left endpoint's.
///
/// # Specification
/// trivial.
fn operator_moves(movement: Move) -> Turn
{
    Turn {
        side: Side::Left,
        movement,
    }
}

/// The seat's move, the right endpoint's.
///
/// # Specification
/// trivial.
fn seat_moves(movement: Move) -> Turn
{
    Turn {
        side: Side::Right,
        movement,
    }
}

/// The event at `at` among `side`'s own moves.
///
/// # Specification
/// trivial.
fn event(
    side: Side,
    at: MoveIndex,
) -> Event
{
    Event { side, at }
}

/// One turn of the seat and the operator: the operator dispatches, the seat
/// reports, the operator retires it, and both close, as a recorder that saw
/// the operator close last writes it.
///
/// # Specification
/// trivial.
fn retired() -> Vec<Turn>
{
    vec![
        operator_moves(Move::Send(payload(DISPATCH))),
        seat_moves(Move::Receive(payload(DISPATCH))),
        seat_moves(Move::Select("report".into())),
        operator_moves(Move::Offer("report".into())),
        seat_moves(Move::Send(payload(REPORT))),
        operator_moves(Move::Receive(payload(REPORT))),
        operator_moves(Move::Select("retire".into())),
        seat_moves(Move::Offer("retire".into())),
        seat_moves(Move::End),
        operator_moves(Move::End),
    ]
}

#[test]
fn the_seat_and_operator_dialogue_is_one_linearization_of_its_web()
{
    let web = admit((&operator(), &seat()), &retired()).expect("the dialogue is a run");
    let (sent, received) = (
        event(Side::Left, MoveIndex(0)),
        event(Side::Right, MoveIndex(0)),
    );
    assert_eq!(WebRelation::Precedes, web.relation(sent, received));
    assert_eq!(WebRelation::Follows, web.relation(received, sent));
    let (operator_closed, seat_offered, seat_closed) = (
        event(Side::Left, MoveIndex(4)),
        event(Side::Right, MoveIndex(3)),
        event(Side::Right, MoveIndex(4)),
    );
    assert_eq!(
        WebRelation::Independent,
        web.relation(operator_closed, seat_closed)
    );
    assert_eq!(
        WebRelation::Independent,
        web.relation(operator_closed, seat_offered)
    );
    // The dispatch reaches the seat's last move through every message between.
    assert_eq!(WebRelation::Precedes, web.relation(sent, seat_closed));
    assert_eq!(
        WebRelation::Missing,
        web.relation(sent, event(Side::Right, MoveIndex(5)))
    );
    assert_eq!(WebRelation::Missing, web.relation(sent, sent));

    // A recorder that saw the operator close before the seat took its offer
    // writes another linearization of the same web.
    let mut closed_first = retired();
    let operator_end = closed_first.pop().expect("the operator closes last");
    closed_first.insert(7, operator_end);
    assert_eq!(
        Ok(web),
        admit((&operator(), &seat()), &closed_first),
        "every interleaving of one run is admitted with one web"
    );
}

#[test]
fn a_receipt_recorded_before_its_send_is_refused_by_the_edge()
{
    let mut early = retired();
    early.swap(0, 1);
    assert_eq!(
        Err(DialogueRefusal::Inverted {
            earlier: event(Side::Left, MoveIndex(0)),
            later: event(Side::Right, MoveIndex(0)),
        }),
        admit((&operator(), &seat()), &early)
    );
    // The retirement offered before the operator selected it.
    let mut unasked = retired();
    unasked.swap(6, 7);
    assert_eq!(
        Err(DialogueRefusal::Inverted {
            earlier: event(Side::Left, MoveIndex(3)),
            later: event(Side::Right, MoveIndex(3)),
        }),
        admit((&operator(), &seat()), &unasked)
    );
}

#[test]
fn a_receipt_that_disagrees_with_its_send_is_unmatched()
{
    let mut forged = retired();
    let receipt = forged.get_mut(1).expect("the seat receives the dispatch");
    receipt.movement = Move::Receive(Payload {
        identity: DISPATCH,
        digest: PayloadDigest([7; 32]),
    });
    assert_eq!(
        Err(DialogueRefusal::Unmatched {
            event: event(Side::Left, MoveIndex(0)),
        }),
        admit((&operator(), &seat()), &forged)
    );
}

#[test]
fn a_move_off_its_protocol_is_refused_by_its_replay()
{
    let mut wrong = retired();
    let choice = wrong.get_mut(2).expect("the seat chooses to report");
    choice.movement = Move::Select("resign".into());
    let Err(DialogueRefusal::Replay {
        side: Side::Right,
        error: ReplayError::Refused { at, reason, .. },
    }) = admit((&operator(), &seat()), &wrong)
    else {
        panic!("the seat's replay refuses the label its protocol lacks");
    };
    assert_eq!((MoveIndex(1), Refusal::WrongLabel), (at, reason));
}

#[test]
fn the_left_endpoint_replays_first()
{
    let mut wrong = retired();
    let dispatch = wrong.get_mut(0).expect("the operator dispatches");
    dispatch.movement = Move::Send(payload(REPORT));
    let choice = wrong.get_mut(2).expect("the seat chooses to report");
    choice.movement = Move::Select("resign".into());
    let Err(DialogueRefusal::Replay {
        side: Side::Left,
        error: ReplayError::Refused { at, reason, .. },
    }) = admit((&operator(), &seat()), &wrong)
    else {
        panic!("the operator's replay refuses before the seat's is read");
    };
    assert_eq!((MoveIndex(0), Refusal::WrongPayloadIdentity), (at, reason));
}

#[test]
fn a_message_without_its_counterpart_is_unmatched()
{
    let sends = session(vec![Node::Send(REPORT, NodeId(1)), Node::End]);
    let receives = session(vec![Node::Receive(REPORT, NodeId(1)), Node::End]);
    let offers = session(vec![
        Node::Offer([("report".into(), NodeId(1))].into()),
        Node::End,
    ]);
    let closes = session(vec![Node::End]);
    let sent = vec![
        operator_moves(Move::Send(payload(REPORT))),
        operator_moves(Move::End),
    ];
    for (protocols, dialogue, unmatched, what) in [
        (
            (&sends, &closes),
            [sent.as_slice(), &[seat_moves(Move::End)]].concat(),
            event(Side::Left, MoveIndex(0)),
            "a send nobody receives",
        ),
        (
            (&closes, &receives),
            vec![
                operator_moves(Move::End),
                seat_moves(Move::Receive(payload(REPORT))),
                seat_moves(Move::End),
            ],
            event(Side::Right, MoveIndex(0)),
            "a receipt nobody sent",
        ),
        (
            (&sends, &offers),
            [sent.as_slice(), &[
                seat_moves(Move::Offer("report".into())),
                seat_moves(Move::End),
            ]]
            .concat(),
            event(Side::Left, MoveIndex(0)),
            "a send observed as an offer",
        ),
    ] {
        assert_eq!(
            Err(DialogueRefusal::Unmatched { event: unmatched }),
            admit(protocols, &dialogue),
            "{what} is unmatched"
        );
    }
}
