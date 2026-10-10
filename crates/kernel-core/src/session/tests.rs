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
