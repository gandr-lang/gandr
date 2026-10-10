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
use gandr_core_session::Session;
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
use gandr_kernel_core::flow_universe::Certificate;
use gandr_kernel_core::flow_universe::Family;
use gandr_kernel_core::flow_universe::Flow;
use gandr_kernel_core::flow_universe::FlowError;
use gandr_kernel_core::flow_universe::Flows;
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
        | RelationResult::Related(evidence) => evidence,
        | RelationResult::Unrelated => panic!("fixture relation must hold"),
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
    let mut flows = Flows::new();
    let proofs = arena.value_unit();
    let forward = flows
        .push(Flow::Session {
            source: gen_code,
            target: peer_code,
            evidence: Arc::new(evidence(&generator, &twice, Relation::Subtype)),
            payload_paths: proofs,
        })
        .expect("forward simulation");
    let backward = flows
        .push(Flow::Session {
            source: peer_code,
            target: gen_code,
            evidence: Arc::new(evidence(&twice, &generator, Relation::Subtype)),
            payload_paths: proofs,
        })
        .expect("independently produced backward simulation");
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
        &flows,
        Certificate::Flow(forward),
        (gen_protocol, peer_protocol),
        &run,
        ReplayBudget::DEFAULT,
    )
    .expect("forward generator run");
    let back = transport(
        &mut arena,
        &flows,
        Certificate::Flow(backward),
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
    let proofs = arena.value_unit();
    let mut flows = Flows::new();
    let flow = flows
        .push(Flow::Session {
            source: old_code,
            target: wide_code,
            evidence: Arc::new(evidence.clone()),
            payload_paths: proofs,
        })
        .expect("candidate simulation");
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
            &flows,
            Certificate::Flow(flow),
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
            &flows,
            Certificate::Flow(flow),
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
    let reverse = flows
        .push(Flow::Session {
            source: wide_code,
            target: old_code,
            evidence: Arc::new(inverse),
            payload_paths: proofs,
        })
        .expect("raw reverse request");
    assert!(matches!(
        transport(
            &mut arena,
            &flows,
            Certificate::Flow(reverse),
            (wide_protocol, old_protocol),
            &pause,
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::Flow(FlowError::Session(
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
            &flows,
            Certificate::Flow(flow),
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
            &flows,
            Certificate::Flow(flow),
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
    let flow = flows
        .push(Flow::Session {
            source: source_code,
            target: target_code,
            evidence: Arc::new(relation),
            payload_paths: proofs,
        })
        .expect("offer simulation");
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
        &flows,
        Certificate::Flow(flow),
        protocols,
        &[Move::Offer("keep".into()), Move::End],
        ReplayBudget::DEFAULT,
    )
    .expect("common peer choice");
    assert_eq!(accepted, [Move::Offer("keep".into()), Move::End]);
    assert!(matches!(
        transport(
            &mut arena,
            &flows,
            Certificate::Flow(flow),
            protocols,
            &[Move::Offer("removed".into()), Move::End],
            ReplayBudget::DEFAULT
        ),
        Err(TransportError::Move {
            at: MoveIndex(0),
            reason: Refusal::WrongLabel
        })
    ));
    let classifier = form_certificate(
        &mut arena,
        &flows,
        Certificate::Flow(flow),
        Family::Flow,
        ReplayBudget::DEFAULT,
    )
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
