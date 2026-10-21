//! End-to-end finite evidence, native admission and recorded-run transport.

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_session::Completion;
use gandr_core_session::Move;
use gandr_core_session::MoveIndex;
use gandr_core_session::Node;
use gandr_core_session::NodeId;
use gandr_core_session::Payload;
use gandr_core_session::PayloadDigest;
use gandr_core_session::Refusal;
use gandr_core_session::Relation;
use gandr_core_session::RelationResult;
use gandr_core_session::ReplayError;
use gandr_core_session::Session;
use gandr_core_session::TypeError;
use gandr_core_session::certified::PayloadCodes;
use gandr_core_session::certified::Protocol;
use gandr_core_session::certified::TransportError;
use gandr_core_session::certified::encode;
use gandr_core_session::certified::transport;
use gandr_core_session::relate;
use gandr_core_session::replay;
use gandr_kernel_core::Convertibility;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::convertible_value_types;
use gandr_kernel_core::flow_universe::Family;
use gandr_kernel_core::flow_universe::form_certificate;
use gandr_kernel_core::session::SessionError;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::session::Evidence;
use gandr_kernel_term::session::State;
use gandr_kernel_term::session::StatePair;

use crate::common::DISPATCH;
use crate::common::HANDOFF;
use crate::common::REPORT;
use crate::common::YIELD;
use crate::common::consumer;
use crate::common::generator;
use crate::common::payload;
use crate::common::seat;
use crate::common::session;

/// Assign distinct native code atoms to the monitor's identities.
///
/// # Specification
/// trivial.
fn codes(arena: &mut TermArena) -> PayloadCodes
{
    PayloadCodes(
        [
            (DISPATCH, arena.value_type_base(BaseType::Integer)),
            (REPORT, arena.value_type_base(BaseType::String)),
            (HANDOFF, arena.value_type_base(BaseType::Numeric)),
            (YIELD, arena.value_type_unit()),
        ]
        .into(),
    )
}

/// `SeatEnd` with `pause : !Report.turn` added to the recursive selection.
///
/// # Specification
/// trivial.
fn widened() -> Session
{
    session(vec![
        Node::Receive(DISPATCH, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Select(
            [
                ("report".into(), NodeId(3)),
                ("handoff".into(), NodeId(7)),
                ("pause".into(), NodeId(9)),
            ]
            .into(),
        ),
        Node::Send(REPORT, NodeId(4)),
        Node::Offer([("next".into(), NodeId(5)), ("retire".into(), NodeId(6))].into()),
        Node::Var(NodeId(1)),
        Node::End,
        Node::Send(HANDOFF, NodeId(8)),
        Node::End,
        Node::Send(REPORT, NodeId(10)),
        Node::Var(NodeId(1)),
    ])
}

/// Extract candidate data, never a trusted kernel verdict.
///
/// # Specification
/// trivial.
fn evidence(
    source: &Session,
    target: &Session,
    relation: Relation,
) -> Evidence
{
    match relate(source, target, relation).expect("valid finite arenas") {
        RelationResult::Related(evidence) => evidence,
        RelationResult::Unrelated => panic!("fixture relation must hold"),
    }
}

/// Admit an engine bisimulation through the ordinary native choke point.
///
/// # Specification
/// trivial.
fn assert_admission(
    source: &Session,
    target: &Session,
    evidence: Evidence,
    expected: &Result<(), KernelError>,
)
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let payloads = codes(arena);
    let source = encode(arena, source, &payloads).expect("source export");
    let target = encode(arena, target, &payloads).expect("target export");
    let classifier = arena.value_type_path_universe(source, target);
    let proofs = arena.value_unit();
    let path = arena.value_session_path(classifier, Arc::new(evidence), proofs);
    let staged = staging.def(LevelSignature::monomorphic(), classifier, path);
    assert_eq!(&environment.add_decl(staged).map(|_| ()), expected);
}

/// Mint a candidate simulation as a native `Flow_U` introduction.
///
/// # Specification
/// trivial.
fn native_flow(
    arena: &mut TermArena,
    codes: (gandr_kernel_term::ValueId, gandr_kernel_term::ValueId),
    evidence: Evidence,
) -> gandr_kernel_term::ValueId
{
    let classifier = arena.value_type_flow_universe(codes.0, codes.1);
    let proofs = arena.value_unit();
    arena.value_session_flow(classifier, Arc::new(evidence), proofs)
}

#[test]
fn seat_and_generator_identity_witnesses()
{
    let old = seat();
    let wide = widened();
    assert_admission(
        &old,
        &old,
        evidence(&old, &old, Relation::Equivalent),
        &Ok(()),
    );
    let simulation = evidence(&old, &wide, Relation::Subtype);
    assert_admission(
        &old,
        &wide,
        simulation,
        &Err(KernelError::Session(SessionError::WrongLabels(StatePair {
            source: State(2),
            target: State(2),
        }))),
    );
    assert_eq!(
        relate(&old, &wide, Relation::Equivalent),
        Ok(RelationResult::Unrelated)
    );
    let recurring = session(vec![
        Node::Mu(NodeId(1)),
        Node::Send(YIELD, NodeId(2)),
        Node::Var(NodeId(0)),
    ]);
    let unfolded = session(vec![
        Node::Send(YIELD, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Send(YIELD, NodeId(3)),
        Node::Var(NodeId(1)),
    ]);
    assert_admission(
        &recurring,
        &unfolded,
        evidence(&recurring, &unfolded, Relation::Equivalent),
        &Ok(()),
    );
    let generator = generator();
    let peer = consumer();
    assert_admission(
        &generator,
        &peer.dual(),
        evidence(&generator, &peer.dual(), Relation::Equivalent),
        &Ok(()),
    );
    assert_eq!(
        relate(&generator, &peer, Relation::Equivalent),
        Ok(RelationResult::Unrelated)
    );

    // Bisimulation is an identity action on recorded skeletons in both directions.
    let mut arena = TermArena::new();
    let payloads = codes(&mut arena);
    let gen_code = encode(&mut arena, &generator, &payloads).expect("generator code");
    let twice = peer.dual();
    let peer_code = encode(&mut arena, &twice, &payloads).expect("dual peer code");
    let forward = native_flow(
        &mut arena,
        (gen_code, peer_code),
        evidence(&generator, &twice, Relation::Subtype),
    );
    let backward = native_flow(
        &mut arena,
        (peer_code, gen_code),
        evidence(&twice, &generator, Relation::Subtype),
    );
    let gen_protocol = Protocol {
        session: &generator,
        code: gen_code,
        payloads: &payloads,
    };
    let peer_protocol = Protocol {
        session: &twice,
        code: peer_code,
        payloads: &payloads,
    };
    let run = [
        Move::Offer("next".into()),
        Move::Send(payload(YIELD)),
        Move::Offer("stop".into()),
        Move::End,
    ];
    let out = transport(
        &mut arena,
        forward,
        (gen_protocol, peer_protocol),
        &run,
        ReplayBudget::DEFAULT,
    )
    .expect("forward generator run");
    let back = transport(
        &mut arena,
        backward,
        (peer_protocol, gen_protocol),
        &out,
        ReplayBudget::DEFAULT,
    )
    .expect("backward generator run");
    assert_eq!(back, run);
}

#[test]
fn recorded_runs_transport_only_forward()
{
    let old = seat();
    let wide = widened();
    let mut arena = TermArena::new();
    let payloads = codes(&mut arena);
    let old_code = encode(&mut arena, &old, &payloads).expect("old code");
    let wide_code = encode(&mut arena, &wide, &payloads).expect("wide code");
    let old_protocol = Protocol {
        session: &old,
        code: old_code,
        payloads: &payloads,
    };
    let wide_protocol = Protocol {
        session: &wide,
        code: wide_code,
        payloads: &payloads,
    };
    let evidence = evidence(&old, &wide, Relation::Subtype);
    let flow = native_flow(&mut arena, (old_code, wide_code), evidence.clone());
    let runs = [
        vec![
            Move::Receive(payload(DISPATCH)),
            Move::Select("report".into()),
            Move::Send(Payload {
                identity: REPORT,
                digest: PayloadDigest([17; 32]),
            }),
            Move::Offer("next".into()),
            Move::Select("report".into()),
            Move::Send(Payload {
                identity: REPORT,
                digest: PayloadDigest([29; 32]),
            }),
            Move::Offer("retire".into()),
            Move::End,
        ],
        vec![
            Move::Receive(payload(DISPATCH)),
            Move::Select("handoff".into()),
            Move::Send(payload(HANDOFF)),
            Move::End,
        ],
    ];
    for run in &runs {
        let before = arena.watermark();
        let out = transport(
            &mut arena,
            flow,
            (old_protocol, wide_protocol),
            run,
            ReplayBudget::DEFAULT,
        )
        .expect("forward recorded run");
        assert_eq!(&out, run);
        assert_eq!(replay(&wide, &out), Ok(Completion));
        assert_eq!(arena.watermark(), before);
    }
    let pause = [
        Move::Receive(payload(DISPATCH)),
        Move::Select("pause".into()),
        Move::Send(payload(REPORT)),
        Move::Select("handoff".into()),
        Move::Send(payload(HANDOFF)),
        Move::End,
    ];
    assert_eq!(replay(&wide, &pause), Ok(Completion));
    assert!(matches!(
        transport(
            &mut arena,
            flow,
            (wide_protocol, old_protocol),
            &pause,
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::Direction)
    ));
    let inverse = Evidence {
        pairs: evidence
            .pairs
            .iter()
            .map(|pair| StatePair {
                source: pair.target,
                target: pair.source,
            })
            .collect(),
        payloads: Vec::new(),
    };
    let reverse = native_flow(&mut arena, (wide_code, old_code), inverse);
    assert!(matches!(
        transport(
            &mut arena,
            reverse,
            (wide_protocol, old_protocol),
            &pause,
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::Flow(KernelError::Session(
            SessionError::WrongLabels(StatePair {
                source: State(2),
                target: State(2)
            })
        )))
    ));
    let empty = PayloadCodes::default();
    assert!(matches!(
        encode(&mut arena, &old, &empty),
        Err(TransportError::MissingPayload(DISPATCH))
    ));
    let mut wrong_payloads = payloads.clone();
    wrong_payloads.0.insert(DISPATCH, arena.value_type_unit());
    let wrong = Protocol {
        session: &old,
        code: old_code,
        payloads: &wrong_payloads,
    };
    assert!(matches!(
        transport(
            &mut arena,
            flow,
            (wrong, wide_protocol),
            &runs[0],
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::CodeBinding)
    ));
    let wrong = Protocol {
        session: &wide,
        code: old_code,
        payloads: &payloads,
    };
    assert!(matches!(
        transport(
            &mut arena,
            flow,
            (wrong, wide_protocol),
            &runs[0],
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::CodeBinding)
    ));

    // Offers reverse width: a source-only peer choice cannot migrate.
    let source = session(vec![
        Node::Offer([("keep".into(), NodeId(1)), ("removed".into(), NodeId(2))].into()),
        Node::End,
        Node::End,
    ]);
    let target = session(vec![
        Node::Offer([("keep".into(), NodeId(1))].into()),
        Node::End,
    ]);
    let source_code = encode(&mut arena, &source, &payloads).expect("offers source");
    let target_code = encode(&mut arena, &target, &payloads).expect("offers target");
    let relation = self::evidence(&source, &target, Relation::Subtype);
    let flow = native_flow(&mut arena, (source_code, target_code), relation);
    let protocols = (
        Protocol {
            session: &source,
            code: source_code,
            payloads: &payloads,
        },
        Protocol {
            session: &target,
            code: target_code,
            payloads: &payloads,
        },
    );
    let accepted = transport(
        &mut arena,
        flow,
        protocols,
        &[Move::Offer("keep".into()), Move::End],
        ReplayBudget::DEFAULT,
    )
    .expect("common peer choice");
    assert_eq!(accepted, [Move::Offer("keep".into()), Move::End]);
    assert!(matches!(
        transport(
            &mut arena,
            flow,
            protocols,
            &[Move::Offer("removed".into()), Move::End],
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::Move {
            at: MoveIndex(0),
            reason: Refusal::WrongLabel
        })
    ));
    let classifier = form_certificate(&mut arena, flow, Family::Flow, ReplayBudget::DEFAULT)
        .expect("offer flow remains formed");
    let gandr_kernel_core::flow_universe::CertificateType::Flow(classifier) = classifier
    else {
        panic!("flow family")
    };
    assert_eq!(
        convertible_value_types(&arena, classifier.source, classifier.target),
        Convertibility::Distinct
    );
}

#[test]
fn a_code_binds_only_the_graph_it_was_encoded_from()
{
    let mut arena = TermArena::new();
    let payloads = codes(&mut arena);
    let offer = |branches: &[(&str, usize)]| {
        Node::Offer(
            branches
                .iter()
                .map(|&(label, next)| (label.into(), NodeId(next)))
                .collect(),
        )
    };
    let select = |branches: &[(&str, usize)]| {
        Node::Select(
            branches
                .iter()
                .map(|&(label, next)| (label.into(), NodeId(next)))
                .collect(),
        )
    };
    let fork = [("keep", 1), ("stop", 2)];
    let offered = session(vec![offer(&fork), Node::End, Node::End]);
    let selected = session(vec![select(&fork), Node::End, Node::End]);
    let run = [Move::Offer("keep".into()), Move::End];
    let chosen = [Move::Select("keep".into()), Move::End];
    for (encoded, local, moves, what) in [
        (
            &offered,
            selected.clone(),
            chosen.as_slice(),
            "a select read as an offer",
        ),
        (
            &selected,
            offered.clone(),
            run.as_slice(),
            "an offer read as a select",
        ),
        (
            &offered,
            session(vec![
                offer(&[("keep", 2), ("stop", 1)]),
                Node::End,
                Node::End,
            ]),
            run.as_slice(),
            "a label bound to another continuation",
        ),
    ] {
        let code = encode(&mut arena, encoded, &payloads).expect("the encoded graph");
        let flow = native_flow(
            &mut arena,
            (code, code),
            evidence(encoded, encoded, Relation::Subtype),
        );
        let honest = Protocol {
            session: encoded,
            code,
            payloads: &payloads,
        };
        let misbound = Protocol {
            session: &local,
            code,
            payloads: &payloads,
        };
        assert!(
            matches!(
                transport(
                    &mut arena,
                    flow,
                    (misbound, honest),
                    moves,
                    ReplayBudget::DEFAULT
                ),
                Err(TransportError::CodeBinding)
            ),
            "{what} does not bind"
        );
    }
}

#[test]
fn a_flow_transports_only_between_the_codes_it_relates()
{
    let old = seat();
    let wide = widened();
    let mut arena = TermArena::new();
    let payloads = codes(&mut arena);
    let old_code = encode(&mut arena, &old, &payloads).expect("old code");
    let wide_code = encode(&mut arena, &wide, &payloads).expect("wide code");
    let flow = native_flow(
        &mut arena,
        (old_code, wide_code),
        evidence(&old, &wide, Relation::Subtype),
    );
    let old_protocol = Protocol {
        session: &old,
        code: old_code,
        payloads: &payloads,
    };
    let run = [
        Move::Receive(payload(DISPATCH)),
        Move::Select("handoff".into()),
        Move::Send(payload(HANDOFF)),
        Move::End,
    ];
    assert!(
        matches!(
            transport(
                &mut arena,
                flow,
                (old_protocol, old_protocol),
                &run,
                ReplayBudget::DEFAULT
            ),
            Err(TransportError::Direction)
        ),
        "a right source with a wrong target is refused"
    );
}

#[test]
fn a_choice_advances_only_onto_a_choice_of_its_own_kind()
{
    let fork = |kind: fn(alloc::collections::BTreeMap<_, NodeId>) -> Node| {
        session(vec![kind([("keep".into(), NodeId(1))].into()), Node::End])
    };
    let offered = fork(Node::Offer);
    let selected = fork(Node::Select);
    let paired = Evidence {
        pairs: [0, 1]
            .map(|state| StatePair {
                source: State(state),
                target: State(state),
            })
            .into_iter()
            .collect(),
        payloads: Vec::new(),
    };
    for (source, target, choice) in [
        (&selected, &offered, Move::Select("keep".into())),
        (&offered, &selected, Move::Offer("keep".into())),
    ] {
        assert!(matches!(
            gandr_core_session::certified::advance((source, target), &paired, &[choice, Move::End]),
            Err(TransportError::Move {
                at: MoveIndex(0),
                reason: Refusal::WrongDirection
            })
        ));
    }
}

#[test]
fn every_transport_refusal_reads_as_its_boundary()
{
    let wrong_labels = || {
        SessionError::WrongLabels(StatePair {
            source: State(2),
            target: State(2),
        })
    };
    let missing = TypeError::MissingNode(NodeId(3));
    let unreadable = ReplayError::InvalidType(missing);
    let moved = |at, reason| TransportError::Move {
        at: MoveIndex(at),
        reason,
    };
    for (error, reads) in [
        (
            TransportError::MissingPayload(DISPATCH),
            "recorded payload identity has no native code".to_owned(),
        ),
        (
            TransportError::CodeBinding,
            "monitor protocol and native session code disagree".to_owned(),
        ),
        (
            TransportError::Direction,
            "session Flow direction mismatch".to_owned(),
        ),
        (
            TransportError::ExpectedSessionFlow,
            "recorded run requires a session Flow introduction".to_owned(),
        ),
        (
            TransportError::Flow(KernelError::Session(wrong_labels())),
            KernelError::Session(wrong_labels()).to_string(),
        ),
        (TransportError::Type(missing), missing.to_string()),
        (
            TransportError::Session(wrong_labels()),
            wrong_labels().to_string(),
        ),
        (
            TransportError::Replay(unreadable.clone()),
            unreadable.to_string(),
        ),
        (
            moved(4, Refusal::ResumeAfterEnd),
            "unmapped session move 4: resume after end".to_owned(),
        ),
        (
            moved(0, Refusal::WrongLabel),
            "unmapped session move 0: wrong label".to_owned(),
        ),
        (
            moved(1, Refusal::WrongDirection),
            "unmapped session move 1: wrong direction".to_owned(),
        ),
        (
            moved(2, Refusal::WrongPayloadIdentity),
            "unmapped session move 2: wrong payload identity".to_owned(),
        ),
    ] {
        assert_eq!(error.to_string(), reads, "{error:?}");
    }
}

#[test]
fn a_stay_relates_no_recorded_run()
{
    let old = seat();
    let mut arena = TermArena::new();
    let payloads = codes(&mut arena);
    let code = encode(&mut arena, &old, &payloads).expect("seat code");
    let stay = arena.value_stay(code);
    let protocol = Protocol {
        session: &old,
        code,
        payloads: &payloads,
    };
    let run = [
        Move::Receive(payload(DISPATCH)),
        Move::Select("handoff".into()),
        Move::Send(payload(HANDOFF)),
        Move::End,
    ];
    let before = arena.watermark();
    assert!(matches!(
        transport(
            &mut arena,
            stay,
            (protocol, protocol),
            &run,
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::ExpectedSessionFlow)
    ));
    assert_eq!(
        arena.watermark(),
        before,
        "the refusal leaves the arena as it was"
    );
}

#[test]
fn a_protocol_binds_only_a_quoted_code_with_every_payload_coded()
{
    let old = seat();
    let mut arena = TermArena::new();
    let payloads = codes(&mut arena);
    let code = encode(&mut arena, &old, &payloads).expect("seat code");
    let flow = native_flow(
        &mut arena,
        (code, code),
        evidence(&old, &old, Relation::Subtype),
    );
    let honest = Protocol {
        session: &old,
        code,
        payloads: &payloads,
    };
    let run = [
        Move::Receive(payload(DISPATCH)),
        Move::Select("handoff".into()),
        Move::Send(payload(HANDOFF)),
        Move::End,
    ];
    let unquoted = arena.value_unit();
    let mut uncoded = payloads.clone();
    uncoded.0.remove(&DISPATCH);
    // The seat with its first receipt read as a send: the node count, root
    // and payload agree with the code, the first node's direction does not.
    let reversed = session(vec![
        Node::Send(DISPATCH, NodeId(1)),
        Node::Mu(NodeId(2)),
        Node::Select([("report".into(), NodeId(3)), ("handoff".into(), NodeId(7))].into()),
        Node::Send(REPORT, NodeId(4)),
        Node::Offer([("next".into(), NodeId(5)), ("retire".into(), NodeId(6))].into()),
        Node::Var(NodeId(1)),
        Node::End,
        Node::Send(HANDOFF, NodeId(8)),
        Node::End,
    ]);
    for (protocol, refusal) in [
        (
            Protocol {
                code: unquoted,
                ..honest
            },
            "a value that is no quoted code",
        ),
        (
            Protocol {
                session: &reversed,
                ..honest
            },
            "a receipt read as a send",
        ),
    ] {
        assert!(
            matches!(
                transport(
                    &mut arena,
                    flow,
                    (protocol, honest),
                    &run,
                    ReplayBudget::DEFAULT
                ),
                Err(TransportError::CodeBinding)
            ),
            "{refusal} does not bind"
        );
    }
    assert!(matches!(
        transport(
            &mut arena,
            flow,
            (
                Protocol {
                    payloads: &uncoded,
                    ..honest
                },
                honest
            ),
            &run,
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::MissingPayload(DISPATCH))
    ));
}

#[test]
fn a_move_advances_only_along_a_related_pair_of_its_own_kind()
{
    let sending = session(vec![Node::Send(REPORT, NodeId(1)), Node::End]);
    let receiving = session(vec![Node::Receive(REPORT, NodeId(1)), Node::End]);
    let run = [Move::Send(payload(REPORT)), Move::End];
    let paired = |pairs: &[(usize, usize)]| Evidence {
        pairs: pairs
            .iter()
            .map(|&(source, target)| StatePair {
                source: State(source),
                target: State(target),
            })
            .collect(),
        payloads: Vec::new(),
    };
    let Ok(moved) = gandr_core_session::certified::advance(
        (&sending, &sending),
        &paired(&[(0, 0), (1, 1)]),
        &run,
    )
    else {
        panic!("a related send advances");
    };
    assert_eq!(moved, run);
    for (target, evidence, what) in [
        (&sending, paired(&[(1, 1)]), "a pair the evidence omits"),
        (
            &receiving,
            paired(&[(0, 0), (1, 1)]),
            "a send paired with a receipt",
        ),
    ] {
        assert!(
            matches!(
                gandr_core_session::certified::advance((&sending, target), &evidence, &run),
                Err(TransportError::Move {
                    at: MoveIndex(0),
                    reason: Refusal::WrongDirection
                })
            ),
            "{what} refuses the first move"
        );
    }
}
