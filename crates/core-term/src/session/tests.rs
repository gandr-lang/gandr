use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use quenchant_shape::shape::Maybe;

use super::ActionKind;
use super::ChildOrder;
use super::PayloadCount;
use super::PayloadSlot;
use super::Protocol;
use super::ProtocolError;
use super::ProtocolNode;
use super::ProtocolState;
use super::ProtocolSyntax;
use super::RecordedMove;
use super::RecursionIndex;
use super::SessionAction;
use super::SessionType;
use super::Step;
use super::carried;
use crate::Computation;
use crate::CoreArena;
use crate::ValueId;
use crate::ValueType;

/// A label as a test spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spelled(&'static str);

/// The label `spelled` names.
///
/// # Specification
/// trivial.
fn label(Spelled(text): Spelled) -> FieldLabel
{
    FieldLabel::from(String::from(text))
}

/// `?Dispatch. mu turn. +{ report : !Report. &{ next : turn, retire : end
/// }, handoff : !Handoff. end }`, payload slots in that order.
///
/// # Specification
/// trivial.
fn seat() -> Protocol
{
    Protocol::new(
        alloc::vec![
            ProtocolSyntax::Receive {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
            ProtocolSyntax::Select(BTreeMap::from([
                (label(Spelled("report")), ProtocolState::from(3_usize)),
                (label(Spelled("handoff")), ProtocolState::from(7_usize)),
            ])),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(1_usize),
                next: ProtocolState::from(4_usize),
            },
            ProtocolSyntax::Offer(BTreeMap::from([
                (label(Spelled("next")), ProtocolState::from(5_usize)),
                (label(Spelled("retire")), ProtocolState::from(6_usize)),
            ])),
            ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ProtocolSyntax::End,
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(2_usize),
                next: ProtocolState::from(8_usize),
            },
            ProtocolSyntax::End,
        ],
        ProtocolState::from(0_usize),
        PayloadCount::from(3_usize),
    )
    .expect("the seat exchange is a closed, contractive protocol")
}

/// The seat's session type over three distinct payloads of `arena`.
///
/// # Specification
/// trivial.
fn seat_session(arena: &mut CoreArena) -> SessionType
{
    let dispatch = arena.value_type_base(BaseType::Integer);
    let report = arena.value_type_base(BaseType::String);
    let handoff = arena.value_type_unit();
    SessionType::new(Arc::new(seat()), Arc::from([dispatch, report, handoff]))
        .expect("three payloads for three slots")
}

#[test]
fn malformed_protocols_are_refused_by_rule()
{
    let end = ProtocolState::from(0_usize);
    let none = PayloadCount::default();
    let cases = [
        (
            alloc::vec![ProtocolSyntax::End],
            ProtocolState::from(1_usize),
            none,
            ProtocolError::MissingNode(ProtocolState::from(1_usize)),
        ),
        (
            alloc::vec![
                ProtocolSyntax::Select(BTreeMap::from([
                    (label(Spelled("a")), ProtocolState::from(1_usize)),
                    (label(Spelled("b")), ProtocolState::from(1_usize)),
                ])),
                ProtocolSyntax::End,
            ],
            end,
            none,
            ProtocolError::RepeatedNode(ProtocolState::from(1_usize)),
        ),
        (
            alloc::vec![ProtocolSyntax::Recur(RecursionIndex::from(0_usize))],
            end,
            none,
            ProtocolError::UnboundRecursion(end),
        ),
        (
            alloc::vec![
                ProtocolSyntax::Mu(ProtocolState::from(1_usize)),
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ],
            end,
            none,
            ProtocolError::NonContractive(end),
        ),
        (
            alloc::vec![
                ProtocolSyntax::Mu(ProtocolState::from(1_usize)),
                ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
                ProtocolSyntax::End,
            ],
            end,
            none,
            ProtocolError::NonContractive(end),
        ),
        (
            alloc::vec![ProtocolSyntax::End, ProtocolSyntax::End],
            end,
            none,
            ProtocolError::UnreachableNode(ProtocolState::from(1_usize)),
        ),
        (
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(1_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::End,
            ],
            end,
            PayloadCount::from(1_usize),
            ProtocolError::MissingPayload(PayloadSlot::from(1_usize)),
        ),
    ];
    for (syntax, root, payloads, refusal) in cases {
        assert_eq!(
            Protocol::new(syntax, root, payloads),
            Err(refusal),
            "each malformation is refused by its own rule"
        );
    }
    let sibling_escape = Protocol::new(
        alloc::vec![
            ProtocolSyntax::Select(BTreeMap::from([
                (label(Spelled("a")), ProtocolState::from(1_usize)),
                (label(Spelled("b")), ProtocolState::from(3_usize)),
            ])),
            ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
            ProtocolSyntax::End,
            ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
        ],
        end,
        none,
    );
    assert_eq!(
        sibling_escape,
        Err(ProtocolError::UnboundRecursion(ProtocolState::from(
            3_usize
        ))),
        "a binder scopes its own body, never a sibling branch"
    );
}

#[test]
fn recursion_variables_resolve_to_their_own_binder()
{
    // mu s. !A. mu t. +{ outer : s, inner : t }
    let protocol = Protocol::new(
        alloc::vec![
            ProtocolSyntax::Mu(ProtocolState::from(1_usize)),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(2_usize),
            },
            ProtocolSyntax::Mu(ProtocolState::from(3_usize)),
            ProtocolSyntax::Select(BTreeMap::from([
                (label(Spelled("outer")), ProtocolState::from(4_usize)),
                (label(Spelled("inner")), ProtocolState::from(5_usize)),
            ])),
            ProtocolSyntax::Recur(RecursionIndex::from(1_usize)),
            ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
        ],
        ProtocolState::from(0_usize),
        PayloadCount::from(1_usize),
    )
    .expect("both variables are bound");
    let written = protocol.syntax();
    assert_eq!(
        (written.get(4), written.get(5)),
        (
            Some(&ProtocolSyntax::Recur(RecursionIndex::from(1_usize))),
            Some(&ProtocolSyntax::Recur(RecursionIndex::from(0_usize)))
        ),
        "the written form counts each variable out to its own binder again"
    );
    assert_eq!(
        Protocol::new(
            written,
            ProtocolState::from(0_usize),
            PayloadCount::from(1_usize)
        ),
        Ok(protocol.clone()),
        "the written form validates to the same protocol"
    );
    assert_eq!(
        protocol.node(ProtocolState::from(4_usize)),
        Ok(&ProtocolNode::Recur(ProtocolState::from(0_usize))),
        "the outer variable names the outer binder"
    );
    assert_eq!(
        protocol.node(ProtocolState::from(5_usize)),
        Ok(&ProtocolNode::Recur(ProtocolState::from(2_usize))),
        "the inner variable names the inner binder"
    );
    assert_eq!(
        protocol
            .head(ProtocolState::from(4_usize))
            .map(|(state, _)| state),
        Ok(ProtocolState::from(1_usize)),
        "the outer variable unfolds to the send"
    );
    assert_eq!(
        protocol
            .head(ProtocolState::from(5_usize))
            .map(|(state, _)| state),
        Ok(ProtocolState::from(3_usize)),
        "the inner variable unfolds to the selection"
    );
    assert_eq!(
        protocol
            .head(ProtocolState::from(3_usize))
            .map(|(state, _)| state),
        Ok(ProtocolState::from(3_usize)),
        "an observable node is its own head"
    );
}

#[test]
fn states_past_the_protocol_are_refused()
{
    let mut arena = CoreArena::new();
    let protocol = Arc::new(seat());
    let integer = arena.value_type_base(BaseType::Integer);
    assert_eq!(
        SessionType::new(Arc::clone(&protocol), Arc::from([integer, integer])),
        Err(ProtocolError::PayloadCount {
            expected: PayloadCount::from(3_usize),
            found: PayloadCount::from(2_usize),
        }),
        "two payloads for three slots are refused"
    );
    let session = seat_session(&mut arena);
    assert_eq!(
        session
            .at(ProtocolState::from(8_usize))
            .map(|moved| moved.state()),
        Ok(ProtocolState::from(8_usize)),
        "the last node is a state"
    );
    assert_eq!(
        session.at(ProtocolState::from(9_usize)),
        Err(ProtocolError::MissingNode(ProtocolState::from(9_usize))),
        "the first position past it is not"
    );
    assert_eq!(
        protocol.node(ProtocolState::from(9_usize)),
        Err(ProtocolError::MissingNode(ProtocolState::from(9_usize))),
        "nor is it a node"
    );
}

#[test]
fn stepping_reads_each_former_and_unfolds_recursion()
{
    let mut arena = CoreArena::new();
    let session = seat_session(&mut arena);
    let [dispatch, report, handoff] = *session.payloads()
    else {
        panic!("three payloads");
    };
    let id = arena.value_type_session(session.clone());
    assert_eq!(
        arena.value_type(id),
        Some(&ValueType::Session(session.clone())),
        "the minted endpoint type reads back whole"
    );
    let Ok(Step::Receive { payload, next }) = session.step()
    else {
        panic!("the seat first receives");
    };
    assert_eq!(payload, dispatch, "the dispatch is the first payload");
    assert_eq!(
        next.state(),
        ProtocolState::from(1_usize),
        "the receive continues at the recursion"
    );
    let step = next.step().expect("the recursion unfolds");
    assert_eq!(step.action(), ActionKind::Select, "to the selection");
    let Step::Select(branches) = step
    else {
        panic!("the selection");
    };
    assert_eq!(
        branches.labels().map(AsRef::as_ref).collect::<Vec<&str>>(),
        ["handoff", "report"],
        "both labels, in label order"
    );
    assert!(
        matches!(
            branches.get(&label(Spelled("missing"))),
            Ok(Maybe::Absent(_))
        ),
        "an unnamed label has no branch"
    );
    let Ok(Maybe::Present(reporting)) = branches.get(&label(Spelled("report")))
    else {
        panic!("report is a branch");
    };
    let Ok(Step::Send { payload, next }) = reporting.step()
    else {
        panic!("reporting sends");
    };
    assert_eq!(payload, report, "the report payload");
    let Ok(Step::Offer(offered)) = next.step()
    else {
        panic!("then offers");
    };
    let Ok(Maybe::Present(again)) = offered.get(&label(Spelled("next")))
    else {
        panic!("next is offered");
    };
    assert_eq!(
        again.step().map(|step| step.action()),
        Ok(ActionKind::Select),
        "next unfolds to the selection again"
    );
    let Ok(Maybe::Present(retired)) = offered.get(&label(Spelled("retire")))
    else {
        panic!("retire is offered");
    };
    assert_eq!(
        retired.step().map(|step| step.action()),
        Ok(ActionKind::Close),
        "retire closes"
    );
    let Ok(Maybe::Present(handing)) = branches.get(&label(Spelled("handoff")))
    else {
        panic!("handoff is a branch");
    };
    let Ok(Step::Send { payload, .. }) = handing.step()
    else {
        panic!("handing off sends");
    };
    assert_eq!(payload, handoff, "the handoff payload");
}

#[test]
fn dual_swaps_every_action_and_keeps_the_rest()
{
    let mut arena = CoreArena::new();
    let session = seat_session(&mut arena);
    let operator = session.dual();
    assert_eq!(operator.state(), session.state(), "the state is kept");
    assert_eq!(
        operator.payloads(),
        session.payloads(),
        "so are the payloads"
    );
    assert_eq!(
        operator.step().map(|step| step.action()),
        Ok(ActionKind::Send),
        "the operator sends the dispatch the seat receives"
    );
    let Ok(Step::Send { next, .. }) = operator.step()
    else {
        panic!("the operator sends");
    };
    assert_eq!(
        next.step().map(|step| step.action()),
        Ok(ActionKind::Offer),
        "and offers what the seat selects"
    );
    assert_eq!(
        operator.dual(),
        session,
        "the dual of the dual is the session type"
    );
    let nodes = seat().dual();
    assert!(
        matches!(
            nodes.node(ProtocolState::from(4_usize)),
            Ok(ProtocolNode::Select(_))
        ),
        "an offer becomes a selection"
    );
    assert_eq!(
        nodes.node(ProtocolState::from(5_usize)),
        Ok(&ProtocolNode::Recur(ProtocolState::from(1_usize))),
        "a variable keeps its binder"
    );
}

#[test]
fn payload_maps_keep_slots_in_either_order()
{
    let mut arena = CoreArena::new();
    let session = seat_session(&mut arena);
    let original: Vec<_> = session.payloads().to_vec();
    let mut visited = Vec::new();
    let positions = session
        .try_relocate(|payload| {
            visited.push(payload);
            Ok::<_, ()>(original.iter().position(|&held| held == payload))
        })
        .expect("relocation succeeds");
    assert_eq!(visited, original, "relocation visits slots in order");
    assert_eq!(
        positions.payloads(),
        [Some(0_usize), Some(1_usize), Some(2_usize)],
        "each image stands at its own slot"
    );
    let mut reversed = Vec::new();
    let swapped = session
        .try_map_payloads(ChildOrder::Reverse, |payload| {
            reversed.push(payload);
            Ok::<_, ()>(payload)
        })
        .expect("the identity map succeeds");
    assert_eq!(
        reversed,
        original.iter().rev().copied().collect::<Vec<_>>(),
        "a reverse visit starts at the last slot"
    );
    assert_eq!(swapped, session, "and keeps every payload at its slot");
    let failed = session.try_map_payloads(ChildOrder::Forward, |_| Err::<_, &str>("refused"));
    assert_eq!(failed, Err("refused"), "the map's error comes back");
    let unit = arena.value_type_unit();
    let replaced = session
        .try_map_payloads(ChildOrder::Forward, |_| Ok::<_, ()>(unit))
        .expect("a total map succeeds");
    assert_eq!(
        replaced.payloads(),
        [unit, unit, unit],
        "a map that moves a payload writes its image at the slot"
    );
}

#[test]
fn a_protocol_holds_one_node_per_written_state()
{
    assert_eq!(9, seat().nodes().len());
}

#[test]
fn actions_name_their_subject_and_children()
{
    let mut arena = CoreArena::new();
    let endpoint = DeBruijnIndex::from(1_u32);
    let payload = arena.value_unit();
    let first = arena.computation_return(payload);
    let second = arena.computation_return(payload);
    let session = seat_session(&mut arena);
    let protocol = arena.value_type_session(session);
    let send: SessionAction = SessionAction::Send { endpoint, payload };
    assert_eq!(
        send.endpoint(),
        Maybe::Present(endpoint),
        "a send names its endpoint"
    );
    assert_eq!(
        send.kind(),
        Maybe::Present(ActionKind::Send),
        "and its kind"
    );
    assert_eq!(
        send.values().collect::<Vec<_>>(),
        [payload],
        "its payload is a child"
    );
    let other = arena.value_tuple(&[payload, payload]);
    assert_eq!(
        send.shape(),
        SessionAction::<ValueId>::Send {
            endpoint,
            payload: other
        }
        .shape(),
        "two payloads on one endpoint are one shape"
    );
    assert_ne!(
        send.shape(),
        SessionAction::<ValueId>::Send {
            endpoint: DeBruijnIndex::from(0_u32),
            payload,
        }
        .shape(),
        "two endpoints are not"
    );
    let offer: SessionAction = SessionAction::Offer {
        endpoint,
        arms: BTreeMap::from([(label(Spelled("b")), second), (label(Spelled("a")), first)]),
    };
    assert_eq!(
        offer.computations().collect::<Vec<_>>(),
        [first, second],
        "the arms in label order"
    );
    let fork = SessionAction::Fork {
        protocol,
        child: first,
        parent: second,
    };
    assert!(
        matches!(fork.endpoint(), Maybe::Absent(_)),
        "a fork acts on no endpoint"
    );
    assert!(
        matches!(fork.kind(), Maybe::Absent(_)),
        "and is no endpoint action"
    );
    assert_eq!(
        fork.value_types().collect::<Vec<_>>(),
        [protocol],
        "its protocol is a child"
    );
    let mut seen = Vec::new();
    let mapped = fork
        .try_map(
            ChildOrder::Reverse,
            &mut seen,
            |_, value| Ok::<_, ()>(value),
            |seen: &mut Vec<&str>, computation| {
                seen.push(if computation == first {
                    "child"
                }
                else {
                    "parent"
                });
                Ok(computation)
            },
            |seen, ty| {
                seen.push("protocol");
                Ok(ty)
            },
        )
        .expect("identity maps succeed");
    assert_eq!(
        seen,
        ["parent", "child", "protocol"],
        "a reverse map is the canonical order reversed, across families"
    );
    assert_eq!(mapped, fork, "and keeps each child in its place");
    let minted = arena.computation_session(fork.clone());
    assert_eq!(
        arena.computation(minted),
        Some(&Computation::Session(fork)),
        "a minted fork reads back whole"
    );
}

#[test]
fn recorded_moves_name_their_payload_and_action()
{
    let mut arena = CoreArena::new();
    let first = arena.value_unit();
    let second = arena.value_variable(crate::Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let moves = [
        RecordedMove::Sent(first),
        RecordedMove::Received(first),
        RecordedMove::Selected(label(Spelled("report"))),
        RecordedMove::Offered(label(Spelled("next"))),
        RecordedMove::Closed,
    ];
    let read: Vec<_> = moves
        .iter()
        .map(|movement| (movement.kind(), movement.payload()))
        .collect();
    assert_eq!(
        read,
        [
            (ActionKind::Send, Maybe::Present(first)),
            (ActionKind::Receive, Maybe::Present(first)),
            (ActionKind::Select, Maybe::Absent(carried::Absent::Choice)),
            (ActionKind::Offer, Maybe::Absent(carried::Absent::Choice)),
            (ActionKind::Close, Maybe::Absent(carried::Absent::Close)),
        ],
        "each move names its own action and only a send or receive carries a value"
    );
    let carried: Vec<_> = moves
        .iter()
        .map(|movement| movement.carrying(second))
        .collect();
    assert_eq!(
        carried,
        [
            RecordedMove::Sent(second),
            RecordedMove::Received(second),
            RecordedMove::Selected(label(Spelled("report"))),
            RecordedMove::Offered(label(Spelled("next"))),
            RecordedMove::Closed,
        ],
        "a rewritten move keeps its action and its label"
    );
    let mut called = 0_u32;
    let mapped: Result<Vec<_>, ()> = moves
        .iter()
        .map(|movement| {
            movement.try_map(|payload| {
                called = called.saturating_add(1);
                Ok(payload == first)
            })
        })
        .collect();
    assert_eq!(
        (mapped, called),
        (
            Ok(alloc::vec![
                RecordedMove::Sent(true),
                RecordedMove::Received(true),
                RecordedMove::Selected(label(Spelled("report"))),
                RecordedMove::Offered(label(Spelled("next"))),
                RecordedMove::Closed,
            ]),
            2
        ),
        "a mapped move carries the image, and only a send or receive calls the mapper"
    );
    assert_eq!(
        RecordedMove::Sent(first).try_map(|_payload| Err::<bool, _>("refused")),
        Err("refused"),
        "the mapper's error is the move's"
    );
    let minted = arena.value_recorded(Arc::from(moves.to_vec()));
    assert_eq!(
        arena.value(minted),
        Some(&crate::Value::Recorded(Arc::from(moves.to_vec()))),
        "a minted run reads back whole"
    );
}

#[test]
fn every_malformation_renders_its_rule()
{
    let at = ProtocolState::from(2_usize);
    let rendered: Vec<String> = [
        ProtocolError::MissingNode(at),
        ProtocolError::RepeatedNode(at),
        ProtocolError::UnboundRecursion(at),
        ProtocolError::NonContractive(at),
        ProtocolError::UnreachableNode(at),
        ProtocolError::MissingPayload(PayloadSlot::from(2_usize)),
        ProtocolError::PayloadCount {
            expected: PayloadCount::from(3_usize),
            found: PayloadCount::from(2_usize),
        },
    ]
    .iter()
    .map(alloc::string::ToString::to_string)
    .collect();
    assert_eq!(
        rendered,
        [
            "missing protocol node 2",
            "protocol node 2 reached twice",
            "unbound recursion variable at node 2",
            "non-contractive recursion at node 2",
            "protocol node 2 is unreachable",
            "missing payload slot 2",
            "the protocol reads 3 payload types, 2 supplied",
        ],
        "each malformation names its rule and position"
    );
}
