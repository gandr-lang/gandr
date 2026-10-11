//! Independent CBPV engine evidence for the directed witnesses.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ResharingMemo;
use gandr_core_nbe::TraceNode;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;

use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::ReplayNode;

/// The direct children of a fixture term, in constructor order.
///
/// # Specification
/// - requires: the node is a fixture term in the CBPV fragment.
/// - ensures: every child is returned without reduction.
/// - provides: the untrusted producer's iterative syntax walk.
/// - panics: on unsupported formers or unresolved fixture roots.
///
/// # Adequacy
/// - hypothesis: L3 — the engine retains pair order and negation branch
///   distinctions.
/// - witness: `flow_universe::tests::one_way_classes_preserve_leaves`
#[spec(ensures: |ret| ret.len() == match node { AnyNode::Value(id) => match arena.value(id) { Some(&Value::PathEquiv { .. }) => 3, Some(&Value::Pair(..) | &Value::StaticApplication(..) | &Value::PathProduct(..)) => 2, Some(&Value::Injection(..) | &Value::Lift { .. } | &Value::Thunk(_) | &Value::Quote(_) | &Value::QuoteComputation(_) | &Value::PathRefl(_)) => 1, _ => 0 }, AnyNode::Computation(id) => match arena.computation(id) { Some(&Computation::Case { .. }) => 3, Some(&Computation::Application(..) | &Computation::Bind(..) | &Computation::Transport(..)) => 2, Some(_) => 1, None => 0 }, _ => 0 })]
fn children(
    arena: &TermArena,
    node: AnyNode,
) -> Vec<AnyNode>
{
    match node {
        | AnyNode::Value(id) => match arena.value(id).expect("value resolves") {
            | &Value::Pair(a, b) => vec![AnyNode::Value(a), AnyNode::Value(b)],
            | &Value::Injection(_, value) => vec![AnyNode::Value(value)],
            | &Value::Thunk(body) => vec![AnyNode::Computation(body)],
            | &Value::Unit | &Value::Variable(_) | &Value::Literal(_) => Vec::new(),
            | _ => panic!("unsupported fixture value"),
        },
        | AnyNode::Computation(id) => match *arena.computation(id).expect("computation resolves") {
            | Computation::Lambda(body) => vec![AnyNode::Computation(body)],
            | Computation::Application(head, value) => {
                vec![AnyNode::Computation(head), AnyNode::Value(value)]
            },
            | Computation::Return(value) | Computation::Force(value) => vec![AnyNode::Value(value)],
            | Computation::Bind(a, b) => vec![AnyNode::Computation(a), AnyNode::Computation(b)],
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => vec![
                AnyNode::Value(scrutinee),
                AnyNode::Computation(on_left),
                AnyNode::Computation(on_right),
            ],
            | Computation::Absurd(_)
            | Computation::Transport(..)
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..) => {
                panic!("native elimination is outside the forward-translator fixture")
            },
        },
        | AnyNode::ValueType(_) | AnyNode::CompType(_) => panic!("no fixture type node"),
    }
}

/// Translate the fixture graph into the engine's separate syntax without
/// reducing it.
///
/// # Specification
/// - requires: the two computations use only fixture-supported CBPV formers.
/// - ensures: graph structure and binder indices are preserved in a fresh
///   arena.
/// - provides: an iterative translation, independent of kernel reduction.
/// - panics: on unsupported fixture formers or unresolved fixture roots.
///
/// # Adequacy
/// - hypothesis: L3 — translated computations distinguish swapped Bool outputs.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(ensures: |ret| ret.0.computation(ret.1).is_some() && ret.0.computation(ret.2).is_some() && (left != right || ret.1 == ret.2))]
fn translate(
    arena: &TermArena,
    left: ComputationId,
    right: ComputationId,
) -> (
    CoreArena,
    gandr_core_term::ComputationId,
    gandr_core_term::ComputationId,
)
{
    let mut core = CoreArena::new();
    let mut values = BTreeMap::new();
    let mut computations = BTreeMap::new();
    let mut pending = vec![
        (AnyNode::Computation(right), false),
        (AnyNode::Computation(left), false),
    ];
    while let Some((node, expanded)) = pending.pop() {
        if !expanded {
            pending.push((node, true));
            for child in children(arena, node).into_iter().rev() {
                pending.push((child, false));
            }
            continue;
        }
        match node {
            | AnyNode::Value(id) => {
                let value = match arena.value(id).expect("value resolves") {
                    | &Value::Unit => core.value_unit(),
                    | &Value::Variable(index) => core.value_variable(Zone::Intuitionistic, index),
                    | &Value::Pair(first, second) => {
                        core.value_pair(values[&first], values[&second])
                    },
                    | &Value::Injection(side, value) => core.value_injection(side, values[&value]),
                    | &Value::Thunk(body) => core.value_thunk(computations[&body]),
                    | &Value::Literal(ref value) => core.value_literal(value.clone()),
                    | _ => panic!("unsupported fixture value"),
                };
                values.insert(id, value);
            },
            | AnyNode::Computation(id) => {
                let computation = match *arena.computation(id).expect("computation resolves") {
                    | Computation::Return(value) => core.computation_return(values[&value]),
                    | Computation::Force(value) => core.computation_force(values[&value]),
                    | Computation::Lambda(body) => core.computation_lambda(computations[&body]),
                    | Computation::Application(head, value) => {
                        core.computation_application(computations[&head], values[&value])
                    },
                    | Computation::Bind(first, second) => {
                        core.computation_bind(computations[&first], computations[&second])
                    },
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => core.computation_case(
                        values[&scrutinee],
                        computations[&on_left],
                        computations[&on_right],
                    ),
                    | Computation::Absurd(_)
                    | Computation::Transport(..)
                    | Computation::DataCase { .. }
                    | Computation::RecordProjection(..) => {
                        panic!("native elimination is outside the forward-translator fixture")
                    },
                };
                computations.insert(id, computation);
            },
            | AnyNode::ValueType(_) | AnyNode::CompType(_) => {
                panic!("no type nodes in fixture computations")
            },
        }
    }
    (core, computations[&left], computations[&right])
}

/// Erase arena-local hints, preserving every decision and premise position.
///
/// # Specification
/// trivial.
pub(super) fn portable<Node>(decision: ConversionDecision<Node>) -> ConversionDecision<()>
where
    Node: Copy,
{
    match decision {
        | ConversionDecision::ReduceLeft { .. } => ConversionDecision::ReduceLeft { redex: () },
        | ConversionDecision::ReduceRight { .. } => ConversionDecision::ReduceRight { redex: () },
        | ConversionDecision::ConstShortcut { .. } => {
            ConversionDecision::ConstShortcut { constant: () }
        },
        | ConversionDecision::Unfold { .. } => ConversionDecision::Unfold { constant: () },
        | ConversionDecision::Postpone { .. } => ConversionDecision::Postpone { constant: () },
        | ConversionDecision::Freeze { side, .. } => {
            ConversionDecision::Freeze { constant: (), side }
        },
        | ConversionDecision::EtaExpand { side, .. } => {
            ConversionDecision::EtaExpand { variable: (), side }
        },
        | ConversionDecision::Force { .. } => ConversionDecision::Force { thunk: () },
        | ConversionDecision::ComparedShared { .. } => ConversionDecision::ComparedShared {
            left: (),
            right: (),
        },
        | ConversionDecision::Decompose => ConversionDecision::Decompose,
        | ConversionDecision::NegativeSubgoal { position } => {
            ConversionDecision::NegativeSubgoal { position }
        },
    }
}

/// Run the untrusted engine and retain its complete decision sequence.
///
/// # Specification
/// - requires: the sides are closed computations in the fixture fragment.
/// - ensures: verdict and trace come from `core-nbe::decide`, not kernel
///   replay; all arena-local trace anchors are erased.
/// - provides: independent computation of each claim.
/// - panics: on fixture translation or an operational engine failure.
///
/// # Adequacy
/// - hypothesis: L3 — independent positive and negative traces replay to their
///   verdicts.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[spec(ensures: |ret| ret.1.0.iter().all(|step| match *step {
    ConversionDecision::ReduceLeft { redex } | ConversionDecision::ReduceRight { redex } => redex == ReplayNode::Other,
    ConversionDecision::ConstShortcut { constant } | ConversionDecision::Unfold { constant } | ConversionDecision::Postpone { constant } | ConversionDecision::Freeze { constant, .. } => constant == ReplayNode::Other,
    ConversionDecision::EtaExpand { variable, .. } => variable == ReplayNode::Other,
    ConversionDecision::Force { thunk } => thunk == ReplayNode::Other,
    ConversionDecision::ComparedShared { left, right } => left == ReplayNode::Other && right == ReplayNode::Other,
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } => true,
}))]
pub(super) fn engine(
    arena: &TermArena,
    left: ComputationId,
    right: ComputationId,
) -> (EngineClaim, Dialogue)
{
    let (core, left, right) = translate(arena, left, right);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let left = gandr_core_nbe::eval_computation(
        &core,
        &mut domain,
        definitions,
        Fuel::from(4096_u32),
        left,
    )
    .expect("left evaluation");
    let right = gandr_core_nbe::eval_computation(
        &core,
        &mut domain,
        definitions,
        Fuel::from(4096_u32),
        right,
    )
    .expect("right evaluation");
    let mut log = TraceLog::new();
    let report = gandr_core_nbe::decide::<_, ResharingMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::computations(left, right),
        &mut log,
    )
    .expect("engine verdict");
    let claim = match report.verdict() {
        | MachineVerdict::Convertible => EngineClaim::Convertible,
        | MachineVerdict::NotConvertible => EngineClaim::NotConvertible,
        | MachineVerdict::Declined(_) => EngineClaim::Declined,
    };
    (
        claim,
        Dialogue(log.decisions().copied().map(decision).collect()),
    )
}

/// Forget engine-local node identities, preserving all decision structure.
///
/// # Specification
/// trivial.
fn decision(step: ConversionDecision<TraceNode>) -> ConversionDecision<ReplayNode>
{
    match step {
        | ConversionDecision::ComparedShared { .. } => ConversionDecision::ComparedShared {
            left: ReplayNode::Other,
            right: ReplayNode::Other,
        },
        | ConversionDecision::Force { .. } => ConversionDecision::Force {
            thunk: ReplayNode::Other,
        },
        | ConversionDecision::EtaExpand { side, .. } => ConversionDecision::EtaExpand {
            side,
            variable: ReplayNode::Other,
        },
        | ConversionDecision::NegativeSubgoal { position } => {
            ConversionDecision::NegativeSubgoal { position }
        },
        | ConversionDecision::Decompose => ConversionDecision::Decompose,
        | ConversionDecision::ReduceLeft { .. } => ConversionDecision::ReduceLeft {
            redex: ReplayNode::Other,
        },
        | ConversionDecision::ReduceRight { .. } => ConversionDecision::ReduceRight {
            redex: ReplayNode::Other,
        },
        | ConversionDecision::ConstShortcut { .. }
        | ConversionDecision::Unfold { .. }
        | ConversionDecision::Postpone { .. }
        | ConversionDecision::Freeze { .. } => panic!("closed fixture contains no constants"),
    }
}
