//! Native admission, finite formation refusals and malicious relation data.

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_term::BaseType;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;
use gandr_kernel_term::session::Evidence;
use gandr_kernel_term::session::Graph;
use gandr_kernel_term::session::Label;
use gandr_kernel_term::session::Node;
use gandr_kernel_term::session::PayloadSlot;
use gandr_kernel_term::session::State;
use gandr_kernel_term::session::StatePair;

use super::SessionError;
use crate::Environment;
use crate::KernelError;
use crate::ReplayBudget;
use crate::check::check_closed_value;
use crate::check::synth_closed_value;
use crate::flow_universe::Certificate;
use crate::flow_universe::Family;
use crate::flow_universe::Flow;
use crate::flow_universe::FlowError;
use crate::flow_universe::Flows;
use crate::flow_universe::form_certificate;

/// Quote one graph with one payload-code field.
///
/// # Specification
/// trivial.
fn code(
    arena: &mut TermArena,
    nodes: Vec<Node>,
    payload: ValueTypeId,
) -> ValueId
{
    let unit = arena.value_type_unit();
    let payloads = arena.value_type_product(payload, unit);
    let ty = arena.value_type_session(
        Arc::new(Graph {
            nodes,
            root: State(0),
        }),
        payloads,
    );
    arena.value_quote(ty)
}

/// Package a candidate relation at native `Path_U`.
///
/// # Specification
/// trivial.
fn path(
    arena: &mut TermArena,
    codes: (ValueId, ValueId),
    evidence: Evidence,
    proofs: ValueId,
) -> (ValueTypeId, ValueId)
{
    let ty = arena.value_type_path_universe(codes.0, codes.1);
    let value = arena.value_session_path(ty, Arc::new(evidence), proofs);
    (ty, value)
}

/// One observable related pair.
///
/// # Specification
/// trivial.
fn pair(
    source: State,
    target: State,
) -> StatePair
{
    StatePair { source, target }
}

#[test]
fn session_codes_are_closed_and_contractive()
{
    let mut arena = TermArena::new();
    let payload = arena.value_type_base(BaseType::Integer);
    let cases = [
        (vec![], SessionError::MissingState(State(0))),
        (
            vec![Node::Send(PayloadSlot(0), State(2))],
            SessionError::MissingState(State(2)),
        ),
        (
            vec![Node::Send(PayloadSlot(0), State(0))],
            SessionError::RepeatedState(State(0)),
        ),
        (
            vec![Node::Var(State(0))],
            SessionError::UnboundVariable(State(0)),
        ),
        (
            vec![Node::Mu(State(1)), Node::Var(State(0))],
            SessionError::NonContractive(State(0)),
        ),
        (
            vec![Node::Mu(State(1)), Node::Mu(State(2)), Node::End],
            SessionError::NonContractive(State(0)),
        ),
        (
            vec![Node::End, Node::End],
            SessionError::UnreachableState(State(1)),
        ),
        (
            vec![Node::Send(PayloadSlot(1), State(1)), Node::End],
            SessionError::MissingPayload(PayloadSlot(1)),
        ),
    ];
    for (nodes, error) in cases {
        let quoted = code(&mut arena, nodes, payload);
        assert_eq!(
            synth_closed_value(&mut arena, quoted),
            Err(KernelError::Session(error))
        );
    }
    let graph = Arc::new(Graph {
        nodes: vec![Node::End],
        root: State(0),
    });
    let ty = arena.value_type_session(graph, payload);
    let quoted = arena.value_quote(ty);
    assert_eq!(
        synth_closed_value(&mut arena, quoted),
        Err(KernelError::Session(SessionError::PayloadTelescope))
    );
    // Payload formation is the ordinary universe checker, not a base-code
    // whitelist.
    let universe = arena.value_type_universe(
        gandr_kernel_term::GroundSort::Value,
        gandr_kernel_strata::Level::zero(),
    );
    let quoted = code(
        &mut arena,
        vec![Node::Send(PayloadSlot(0), State(1)), Node::End],
        universe,
    );
    let classifier = synth_closed_value(&mut arena, quoted).expect("higher payload code");
    assert_eq!(
        arena.value_type(classifier),
        Some(&gandr_kernel_term::ValueType::Universe {
            sort: gandr_kernel_term::GroundSort::Value,
            level: gandr_kernel_strata::Level::zero()
                .succ()
                .expect("level one")
        })
    );
    let proofs = arena.value_unit();
    let evidence = Evidence {
        pairs: [pair(State(0), State(0)), pair(State(1), State(1))].into(),
        payloads: Vec::new(),
    };
    let (path_type, value) = path(&mut arena, (quoted, quoted), evidence, proofs);
    assert_eq!(check_closed_value(&mut arena, value, path_type), Ok(()));
    let list = arena.value_type_list(payload);
    let quoted = code(
        &mut arena,
        vec![Node::Receive(PayloadSlot(0), State(1)), Node::End],
        list,
    );
    let reflexive = arena.value_path_refl(quoted);
    let classifier = arena.value_type_path_universe(quoted, quoted);
    assert_eq!(
        check_closed_value(&mut arena, reflexive, classifier),
        Ok(())
    );
    // A surrounding function binder must not close an open session payload code.
    let variable = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
    let open = arena.value_type_element(variable, gandr_kernel_strata::Level::zero());
    let quoted = code(
        &mut arena,
        vec![Node::Send(PayloadSlot(0), State(1)), Node::End],
        open,
    );
    let body = arena.computation_return(quoted);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let result = arena.comp_type_returner(universe);
    let function = arena.comp_type_arrow(universe, result);
    let expected = arena.value_type_thunk(function);
    assert_eq!(
        check_closed_value(&mut arena, body, expected),
        Err(KernelError::UnboundVariable {
            index: gandr_kernel_term::DeBruijnIndex::from(0_u32)
        })
    );
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let payload = arena.value_type_base(BaseType::Integer);
    let quoted = code(
        arena,
        vec![
            Node::Mu(State(1)),
            Node::Receive(PayloadSlot(0), State(2)),
            Node::Var(State(0)),
        ],
        payload,
    );
    let classifier = synth_closed_value(arena, quoted).expect("closed session universe code");
    let staged = staging.def(LevelSignature::monomorphic(), classifier, quoted);
    environment
        .add_decl(staged)
        .expect("ordinary admission rechecks session formation");
}

#[test]
fn session_relations_replay_without_search()
{
    let mut arena = TermArena::new();
    let payload = arena.value_type_base(BaseType::Integer);
    let source = code(
        &mut arena,
        vec![
            Node::Mu(State(1)),
            Node::Send(PayloadSlot(0), State(2)),
            Node::Var(State(0)),
        ],
        payload,
    );
    let target = code(
        &mut arena,
        vec![
            Node::Send(PayloadSlot(0), State(1)),
            Node::Mu(State(2)),
            Node::Send(PayloadSlot(0), State(3)),
            Node::Var(State(1)),
        ],
        payload,
    );
    let evidence = Evidence {
        pairs: [pair(State(1), State(0)), pair(State(1), State(2))].into(),
        payloads: Vec::new(),
    };
    let proofs = arena.value_unit();
    let (ty, value) = path(&mut arena, (source, target), evidence.clone(), proofs);
    assert_eq!(check_closed_value(&mut arena, value, ty), Ok(()));
    let actual = synth_closed_value(&mut arena, value).expect("synthesized native Path_U");
    assert_eq!(
        crate::convertible_value_types(&arena, ty, actual),
        crate::Convertibility::Convertible
    );
    let mut missing = evidence.clone();
    missing.pairs.remove(&pair(State(1), State(2)));
    let (_, bad) = path(&mut arena, (source, target), missing, proofs);
    assert_eq!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::Session(SessionError::MissingPair(pair(
            State(1),
            State(2)
        ))))
    );
    let (_, bad) = path(&mut arena, (source, target), Evidence::default(), proofs);
    assert_eq!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::Session(SessionError::MissingPair(pair(
            State(1),
            State(0)
        ))))
    );
    let mut administrative = evidence.clone();
    administrative.pairs.insert(pair(State(0), State(0)));
    let (_, bad) = path(&mut arena, (source, target), administrative, proofs);
    assert_eq!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::Session(SessionError::AdministrativePair(
            pair(State(0), State(0))
        )))
    );
    let wrong = code(
        &mut arena,
        vec![
            Node::Mu(State(1)),
            Node::Receive(PayloadSlot(0), State(2)),
            Node::Var(State(0)),
        ],
        payload,
    );
    let (_, bad) = path(&mut arena, (wrong, target), evidence, proofs);
    assert_eq!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::Session(SessionError::WrongAction(pair(
            State(1),
            State(0)
        ))))
    );

    let select = |names: &[&str]| {
        Node::Select(
            names
                .iter()
                .enumerate()
                .map(|(index, name)| (Label((*name).into()), State(index.saturating_add(1))))
                .collect(),
        )
    };
    let narrow = code(&mut arena, vec![select(&["old"]), Node::End], payload);
    let wide = code(
        &mut arena,
        vec![select(&["old", "pause"]), Node::End, Node::End],
        payload,
    );
    let evidence = Evidence {
        pairs: [pair(State(0), State(0)), pair(State(1), State(1))].into(),
        payloads: Vec::new(),
    };
    let (_, bad) = path(&mut arena, (narrow, wide), evidence.clone(), proofs);
    assert_eq!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::Session(SessionError::WrongLabels(pair(
            State(0),
            State(0)
        ))))
    );
    let mut flows = Flows::new();
    let flow = flows
        .push(Flow::Session {
            source: narrow,
            target: wide,
            evidence: Arc::new(evidence.clone()),
            payload_paths: proofs,
        })
        .expect("raw flow");
    form_certificate(
        &mut arena,
        &flows,
        Certificate::Flow(flow),
        Family::Flow,
        ReplayBudget::DEFAULT,
    )
    .expect("one-way width");
    assert!(matches!(
        form_certificate(
            &mut arena,
            &flows,
            Certificate::Flow(flow),
            Family::Path,
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::FamilyMismatch {
            expected: Family::Path,
            actual: Family::Flow
        })
    ));
    assert!(matches!(
        form_certificate(
            &mut arena,
            &flows,
            Certificate::Path(value),
            Family::Flow,
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path
        })
    ));
    let backward = flows
        .push(Flow::Session {
            source: wide,
            target: narrow,
            evidence: Arc::new(evidence),
            payload_paths: proofs,
        })
        .expect("raw reverse request");
    assert!(matches!(
        form_certificate(
            &mut arena,
            &flows,
            Certificate::Flow(backward),
            Family::Flow,
            ReplayBudget::DEFAULT
        ),
        Err(FlowError::Session(SessionError::WrongLabels(StatePair {
            source: State(0),
            target: State(0)
        })))
    ));

    // Different payload codes require an actual native equivalence, not a tag.
    let unit_ty = arena.value_type_unit();
    let pair_ty = arena.value_type_product(unit_ty, unit_ty);
    let source = code(
        &mut arena,
        vec![Node::Send(PayloadSlot(0), State(1)), Node::End],
        unit_ty,
    );
    let target = code(
        &mut arena,
        vec![Node::Send(PayloadSlot(0), State(1)), Node::End],
        pair_ty,
    );
    let mut evidence = Evidence {
        pairs: [pair(State(0), State(0)), pair(State(1), State(1))].into(),
        payloads: Vec::new(),
    };
    let (_, bad) = path(&mut arena, (source, target), evidence.clone(), proofs);
    assert_eq!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::Session(SessionError::PayloadMismatch(pair(
            State(0),
            State(0)
        ))))
    );
    evidence.payloads.push((PayloadSlot(0), PayloadSlot(0)));
    let one = arena.value_unit();
    let two = arena.value_pair(one, one);
    let forward = arena.computation_return(two);
    let forward = arena.computation_lambda(forward);
    let forward = arena.value_thunk(forward);
    let backward = arena.computation_return(one);
    let backward = arena.computation_lambda(backward);
    let backward = arena.value_thunk(backward);
    let rounds =
        crate::path_universe::tests::evidence(&mut arena, &[one], &[two], forward, backward);
    let one_code = arena.value_quote(unit_ty);
    let two_code = arena.value_quote(pair_ty);
    let payload_ty = arena.value_type_path_universe(one_code, two_code);
    let payload_path = arena.value_path_equiv(payload_ty, forward, backward, rounds);
    let tuple = arena.value_pair(payload_path, proofs);
    let (ty, good) = path(&mut arena, (source, target), evidence.clone(), tuple);
    assert_eq!(check_closed_value(&mut arena, good, ty), Ok(()));
    let false_path = arena.value_path_refl(one_code);
    let false_tuple = arena.value_pair(false_path, proofs);
    let (_, bad) = path(&mut arena, (source, target), evidence, false_tuple);
    assert!(matches!(
        synth_closed_value(&mut arena, bad),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    // Conversion may erase derivation pairs; admission's memo must retain them.
    let mut environment = Environment::new();
    let before = environment.arena().watermark();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let payload = arena.value_type_unit();
    let code = code(arena, vec![Node::End], payload);
    let proofs = arena.value_unit();
    let relation = Evidence {
        pairs: [pair(State(0), State(0))].into(),
        payloads: Vec::new(),
    };
    let (ty, good) = path(arena, (code, code), relation, proofs);
    let (_, bad) = path(arena, (code, code), Evidence::default(), proofs);
    assert_eq!(
        crate::conv::equal_values(arena, good, bad),
        crate::Convertibility::Convertible
    );
    let declared = arena.value_type_product(ty, ty);
    let body = arena.value_pair(good, bad);
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    assert_eq!(
        environment.add_decl(staged),
        Err(KernelError::Session(SessionError::MissingPair(pair(
            State(0),
            State(0)
        ))))
    );
    assert_eq!(environment.arena().watermark(), before);
}

#[test]
fn session_boundaries_name_payload_and_graph_refusals()
{
    let mut arena = TermArena::new();
    let before = arena.watermark();
    let stale = arena.value_type_unit();
    arena.truncate_to(before);
    assert_eq!(
        super::payload_codes(&arena, stale),
        Err(SessionError::Arena)
    );
    let graph = Graph {
        nodes: vec![Node::End],
        root: State(0),
    };
    assert_eq!(
        super::validate_graph(&arena, &graph, stale),
        Err(SessionError::Arena)
    );
    assert_eq!(
        super::view(&arena, stale),
        Err(SessionError::ExpectedSession(stale))
    );
    let unit = arena.value_type_unit();
    assert_eq!(
        super::view(&arena, unit),
        Err(SessionError::ExpectedSession(unit))
    );
    assert_eq!(super::payload_codes(&arena, unit), Ok(Vec::new()));
    let payload = arena.value_type_base(BaseType::String);
    let tail = arena.value_type_product(unit, unit);
    let telescope = arena.value_type_product(payload, tail);
    assert_eq!(
        super::payload_codes(&arena, telescope),
        Ok(vec![payload, unit])
    );
    assert_eq!(
        super::payload_codes(&arena, payload),
        Err(SessionError::PayloadTelescope)
    );
    assert_eq!(
        super::node(&graph, State(1)),
        Err(SessionError::MissingState(State(1)))
    );
    assert_eq!(super::head(&graph, State(0)), Ok(State(0)));
    assert_eq!(
        super::head(&graph, State(1)),
        Err(SessionError::MissingState(State(1)))
    );

    // A variable in the sibling branch cannot name the other branch's binder.
    let escaped = Graph {
        root: State(0),
        nodes: vec![
            Node::Select([(Label("a".into()), State(1)), (Label("b".into()), State(4))].into()),
            Node::Mu(State(2)),
            Node::Send(PayloadSlot(0), State(3)),
            Node::Var(State(1)),
            Node::Var(State(1)),
        ],
    };
    assert_eq!(
        super::validate_graph(&arena, &escaped, telescope),
        Err(SessionError::UnboundVariable(State(4)))
    );

    let quoted = code(
        &mut arena,
        vec![Node::Send(PayloadSlot(0), State(1)), Node::End],
        unit,
    );
    synth_closed_value(&mut arena, quoted).expect("formed endpoint");
    let gandr_kernel_term::Value::Quote(ty) = *arena.value(quoted).expect("quote")
    else {
        panic!("quote")
    };
    let pairs = [pair(State(0), State(0)), pair(State(1), State(1))];
    let mut evidence = Evidence {
        pairs: pairs.into(),
        payloads: vec![(PayloadSlot(0), PayloadSlot(0))],
    };
    let expected = super::obligations(&mut arena, ty, ty, &evidence, super::Relation::Bisimulation)
        .expect("payload path obligation");
    let payload_code = arena.value_quote(unit);
    let path_ty = arena.value_type_path_universe(payload_code, payload_code);
    let wanted = arena.value_type_product(path_ty, unit);
    assert_eq!(
        crate::convertible_value_types(&arena, expected, wanted),
        crate::Convertibility::Convertible
    );
    evidence.payloads.push((PayloadSlot(0), PayloadSlot(0)));
    assert_eq!(
        super::obligations(&mut arena, ty, ty, &evidence, super::Relation::Bisimulation),
        Err(SessionError::DuplicatePayloadPath(
            PayloadSlot(0),
            PayloadSlot(0)
        ))
    );
    for slots in [
        (PayloadSlot(1), PayloadSlot(0)),
        (PayloadSlot(0), PayloadSlot(1)),
    ] {
        evidence.payloads = vec![slots];
        assert_eq!(
            super::obligations(&mut arena, ty, ty, &evidence, super::Relation::Bisimulation),
            Err(SessionError::MissingPayload(PayloadSlot(1)))
        );
    }
    evidence.payloads.clear();
    evidence.pairs.insert(pair(State(2), State(1)));
    assert_eq!(
        super::obligations(&mut arena, ty, ty, &evidence, super::Relation::Bisimulation),
        Err(SessionError::MissingState(State(2)))
    );
    assert_eq!(
        super::obligations(
            &mut arena,
            unit,
            ty,
            &evidence,
            super::Relation::Bisimulation
        ),
        Err(SessionError::ExpectedSession(unit))
    );

    let administrative = Graph {
        root: State(0),
        nodes: vec![Node::Mu(State(1)), Node::Var(State(0))],
    };
    assert_eq!(
        super::head(&administrative, State(0)),
        Err(SessionError::NonContractive(State(1)))
    );
}

#[test]
fn session_choice_relations_exhaust_two_label_widths()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    for kind in [super::Choice::Select, super::Choice::Offer] {
        for source_mask in 0_u8 .. 4 {
            for target_mask in 0_u8 .. 4 {
                let graph = |mask| {
                    let mut nodes = vec![Node::End];
                    let mut labels = alloc::collections::BTreeMap::new();
                    for (label, bit) in [("a", 1), ("b", 2)] {
                        if mask & bit != 0 {
                            labels.insert(Label(label.into()), State(nodes.len()));
                            nodes.push(Node::End);
                        }
                    }
                    nodes[0] = match kind {
                        | super::Choice::Select => Node::Select(labels),
                        | super::Choice::Offer => Node::Offer(labels),
                    };
                    Graph {
                        root: State(0),
                        nodes,
                    }
                };
                let left = Arc::new(graph(source_mask));
                let right = Arc::new(graph(target_mask));
                let mut evidence = Evidence {
                    pairs: [pair(State(0), State(0))].into(),
                    payloads: Vec::new(),
                };
                for a in 1 .. left.nodes.len() {
                    for b in 1 .. right.nodes.len() {
                        evidence.pairs.insert(pair(State(a), State(b)));
                    }
                }
                let source = arena.value_type_session(left, unit);
                let target = arena.value_type_session(right, unit);
                for ty in [source, target] {
                    let quoted = arena.value_quote(ty);
                    synth_closed_value(&mut arena, quoted).expect("closed choice code");
                }
                for relation in [super::Relation::Bisimulation, super::Relation::Simulation] {
                    let admitted = match relation {
                        | super::Relation::Bisimulation => source_mask == target_mask,
                        | super::Relation::Simulation => match kind {
                            | super::Choice::Select => source_mask & target_mask == source_mask,
                            | super::Choice::Offer => source_mask & target_mask == target_mask,
                        },
                    };
                    match super::obligations(&mut arena, source, target, &evidence, relation) {
                        | Ok(expected) => {
                            assert!(admitted, "invalid label inclusion admitted");
                            assert_eq!(
                                arena.value_type(expected),
                                Some(&gandr_kernel_term::ValueType::Unit)
                            );
                        },
                        | Err(error) => {
                            assert!(!admitted, "valid label inclusion refused");
                            assert_eq!(error, SessionError::WrongLabels(pair(State(0), State(0))));
                        },
                    }
                }
            }
        }
    }
}
