//! Native universe paths admitted as declarations, with independent `NbE`
//! evidence.

#[path = "../higher_field/certificate_tests.rs"]
mod higher_field_tests;

#[path = "../identity_recursion/recursive/transport_tests.rs"]
mod recursive_transport_tests;

#[path = "../identity_recursion/universe_tests.rs"]
mod universe_fold_tests;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
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
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::PathEvidence;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Dialogue;
use super::Direction;
use super::PathError;
use super::PatternPosition;
use super::Reduction;
use super::Transport;
use super::beta;
use super::replay_transport;
use crate::env::CheckedId;
use crate::env::Environment;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

/// The producer's structural edges, with no call to a kernel reducer.
///
/// # Specification
/// - requires: the root belongs to the supported native-path fixture fragment.
/// - ensures: every direct structural child is retained, in constructor order.
/// - provides: edges for a non-reducing translation into the separate engine.
/// - fails: never.
/// - panics: on an unreadable or unsupported fixture former.
///
/// # Adequacy
/// - hypothesis: L3 — asymmetric product paths retain both component roles.
/// - witness: `path_universe::tests::it_computes_through_a_former`
#[spec(ensures: |ret| ret.len() == match node {
        AnyNode::Value(id) => arena.value(id).map_or(0, |matched_native_node| match *matched_native_node {
Value::Constructor {ref fields,..} => fields.len().saturating_add(1),
Value::Record(ref fields) => fields.len(),
Value::PathEquiv { .. } => 3,
Value::Pair(..) | Value::StaticApplication(..) | Value::PathProduct(..) => 2,
Value::Injection(..) | Value::Lift { .. } | Value::Thunk(_) | Value::Quote(_) | Value::QuoteComputation(_) | Value::PathRefl(_) => 1,
_ => 0,
}),
        AnyNode::Computation(id) => arena.computation(id).map_or(0, |matched_native_node| match *matched_native_node {
Computation::DataCase {ref branches,..} => branches.len().saturating_add(2),
Computation::Case { .. } => 3,
Computation::Application(..) | Computation::Bind(..) | Computation::Transport(..) => 2,
_ => 1,
}),
        AnyNode::ValueType(id) => arena.value_type(id).map_or(0, |matched_native_node| match *matched_native_node {
ValueType::Data {ref arguments,..} => arguments.len(),
ValueType::Record(ref fields) => fields.len(),
ValueType::Product(..) | ValueType::Sum(..) | ValueType::StaticPi { .. } | ValueType::PathUniverse(..) => 2,
ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::List(_) => 1,
_ => 0,
}),
        AnyNode::CompType(id) => match arena.comp_type(id) {
            Some(&CompType::Arrow { .. } | &CompType::Pi { .. }) => 2,
            Some(_) => 1, None => 0,
        },
    })]
fn children(
    arena: &TermArena,
    node: AnyNode,
) -> Vec<AnyNode>
{
    use AnyNode::CompType as C;
    use AnyNode::Computation as M;
    use AnyNode::Value as V;
    use AnyNode::ValueType as A;
    match node {
        | V(id) => match *(arena.value(id).expect("fixture value")) {
            | Value::Constructor {
                ref datatype,
                ref fields,
                ..
            } => core::iter::once(A(*datatype))
                .chain(fields.iter().copied().map(V))
                .collect(),
            | Value::Record(ref fields) => fields.values().copied().map(V).collect(),
            | Value::SessionPath { .. } => {
                panic!("session evidence has a separate finite producer")
            },
            | Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => vec![A(path_type), V(forward), V(backward)],
            | Value::PathProduct(a, b) | Value::Pair(a, b) | Value::StaticApplication(a, b) => {
                vec![V(a), V(b)]
            },
            | Value::PathRefl(a) | Value::Injection(_, a) | Value::Lift { body: a, .. } => {
                vec![V(a)]
            },
            | Value::Thunk(a) => vec![M(a)],
            | Value::Quote(a) => vec![A(a)],
            | Value::QuoteComputation(a) => vec![C(a)],
            | Value::Variable(_) | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
                Vec::new()
            },
        },
        | M(id) => match *arena.computation(id).expect("fixture computation") {
            | Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            } => [V(scrutinee), C(motive)]
                .into_iter()
                .chain(branches.iter().copied().map(M))
                .collect(),
            | Computation::RecordProjection(record, _) => vec![V(record)],
            | Computation::Absurd(_) => {
                panic!("empty elimination is outside the path fixture fragment")
            },
            | Computation::Transport(a, b) => vec![V(a), V(b)],
            | Computation::Lambda(a) => vec![M(a)],
            | Computation::Application(a, b) => vec![M(a), V(b)],
            | Computation::Return(a) | Computation::Force(a) => vec![V(a)],
            | Computation::Bind(a, b) => vec![M(a), M(b)],
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => vec![V(scrutinee), M(on_left), M(on_right)],
        },
        | A(id) => match *(arena.value_type(id).expect("fixture value type")) {
            | ValueType::Data { ref arguments, .. } => arguments.iter().copied().map(V).collect(),
            | ValueType::Record(ref fields) => fields.values().copied().map(A).collect(),
            | ValueType::List(_) | ValueType::Session { .. } => {
                panic!("recursive inhabitants stay outside the first-order path producer")
            },
            | ValueType::PathUniverse(a, b) => vec![V(a), V(b)],
            | ValueType::Product(a, b)
            | ValueType::Sum(a, b)
            | ValueType::StaticPi {
                domain: a,
                codomain: b,
            } => vec![A(a), A(b)],
            | ValueType::Thunk(a) => vec![C(a)],
            | ValueType::Lift { inner: a, .. } => vec![A(a)],
            | ValueType::Element { code: a, .. } => vec![V(a)],
            | ValueType::Base(_)
            | ValueType::Unit
            | ValueType::Empty
            | ValueType::Universe { .. }
            | ValueType::Abstract(_) => Vec::new(),
        },
        | C(id) => match arena.comp_type(id).expect("fixture computation type") {
            | &CompType::Returner(a) => vec![A(a)],
            | &CompType::Arrow {
                domain: a,
                codomain: b,
            }
            | &CompType::Pi {
                domain: a,
                codomain: b,
            } => vec![A(a), C(b)],
            | &CompType::Element { code: a, .. } => vec![V(a)],
        },
    }
}

/// Bool's code, constructors and closed negation map.
#[derive(Clone, Copy)]
struct Boolean
{
    /// The sum of units.
    ty: ValueTypeId,
    /// Its quote.
    code: ValueId,
    /// The left constructor.
    truth: ValueId,
    /// The right constructor.
    falsity: ValueId,
    /// The negation thunk.
    not: ValueId,
}

/// Construct Bool and negation as ordinary kernel syntax.
///
/// # Specification
/// trivial.
fn boolean(arena: &mut TermArena) -> Boolean
{
    let unit_type = arena.value_type_unit();
    let ty = arena.value_type_sum(unit_type, unit_type);
    let code = arena.value_quote(ty);
    let unit = arena.value_unit();
    let truth = arena.value_injection(Side::Left, unit);
    let falsity = arena.value_injection(Side::Right, unit);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let left = arena.value_injection(Side::Right, variable);
    let right = arena.value_injection(Side::Left, variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let body = arena.computation_case(variable, left, right);
    let body = arena.computation_lambda(body);
    Boolean {
        ty,
        code,
        truth,
        falsity,
        not: arena.value_thunk(body),
    }
}

/// Form a forced application without reducing it.
///
/// # Specification
/// trivial.
fn apply(
    arena: &mut TermArena,
    function: ValueId,
    value: ValueId,
) -> ComputationId
{
    let force = arena.computation_force(function);
    arena.computation_application(force, value)
}

/// Compose two closed translator thunks.
///
/// # Specification
/// trivial.
fn compose(
    arena: &mut TermArena,
    first: ValueId,
    second: ValueId,
) -> ValueId
{
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let first = apply(arena, first, variable);
    let second = apply(arena, second, variable);
    let body = arena.computation_bind(first, second);
    let body = arena.computation_lambda(body);
    arena.value_thunk(body)
}

/// Inline triple negation while retaining its administrative bind seams.
///
/// # Specification
/// - ensures: both Bool constructors are negated, with distinct map syntax.
/// - panics: none.
/// - provides: a fixed syntax observer for the two administrative bind seams;
///   normalization of both applications remains an independent witness.
///
/// # Adequacy
/// - hypothesis: L3 — extensional agreement does not identify certificates; the
///   local predicate retains opposite branches and both bind seams.
/// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
#[spec(ensures: |ret| {
    let Some(&Value::Thunk(lambda)) = arena.value(ret) else { return false; };
    let Some(&Computation::Lambda(case)) = arena.computation(lambda) else { return false; };
    let Some(&Computation::Case { scrutinee, on_left, on_right }) = arena.computation(case) else { return false; };
    matches!(arena.value(scrutinee), Some(&Value::Variable(index)) if u32::from(index) == 0)
        && [(on_left, Side::Right), (on_right, Side::Left)].into_iter().all(|(branch, side)| {
            let Some(&Computation::Bind(payload, inner)) = arena.computation(branch) else { return false; };
            let Some(&Computation::Bind(again, returned)) = arena.computation(inner) else { return false; };
            let Some(&Computation::Return(injection)) = arena.computation(returned) else { return false; };
            payload == again && arena.computation(payload) == Some(&Computation::Return(scrutinee))
                && arena.value(injection) == Some(&Value::Injection(side, scrutinee))
        })
})]
fn inlined_triple_negation(arena: &mut TermArena) -> ValueId
{
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let payload = arena.computation_return(variable);
    let mut branch = |side| {
        let value = arena.value_injection(side, variable);
        let result = arena.computation_return(value);
        let result = arena.computation_bind(payload, result);
        arena.computation_bind(payload, result)
    };
    let left = branch(Side::Right);
    let right = branch(Side::Left);
    let body = arena.computation_case(variable, left, right);
    let body = arena.computation_lambda(body);
    arena.value_thunk(body)
}

/// Erase arena-local hints, preserving every decision and premise position.
///
/// # Specification
/// trivial.
fn portable<Node>(decision: ConversionDecision<Node>) -> ConversionDecision<()>
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

/// Translate the reachable native graph without running a kernel reduction.
///
/// # Specification
/// - ensures: every former, binder and translator body is preserved.
/// - panics: on a dangling fixture node.
///
/// # Termination
/// - reason: a visited-node postorder worklist over the finite arena.
/// - measure: unvisited reachable nodes.
///
/// # Adequacy
/// - hypothesis: L3 — independently evaluated native computations distinguish
///   Bool outputs, product order and intensional path identity.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
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
    let mut types = BTreeMap::new();
    let mut comp_types = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut pending = vec![
        (AnyNode::Computation(right), false),
        (AnyNode::Computation(left), false),
    ];
    while let Some((node, expanded)) = pending.pop() {
        if !expanded {
            if !seen.insert(node) {
                continue;
            }
            pending.push((node, true));
            pending.extend(
                children(arena, node)
                    .into_iter()
                    .rev()
                    .map(|child| (child, false)),
            );
            continue;
        }
        match node {
            | AnyNode::Value(id) => {
                let value = match *(arena.value(id).expect("fixture value")) {
                    | Value::Constructor {
                        ref datatype,
                        ref tag,
                        ref fields,
                    } => core.value_constructor(
                        types[datatype],
                        *tag,
                        fields.iter().map(|field| values[field]).collect(),
                    ),
                    | Value::Record(ref fields) => core.value_record(
                        fields
                            .iter()
                            .map(|(label, field)| (label.clone(), values[field]))
                            .collect(),
                    ),
                    | Value::SessionPath { .. } => {
                        panic!("session evidence has a separate finite producer")
                    },
                    | Value::PathRefl(code) => core.value_path_refl(values[&code]),
                    | Value::PathProduct(first, second) => {
                        core.value_path_product(values[&first], values[&second])
                    },
                    | Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ref evidence,
                    } => core.value_path_equiv(
                        types[&path_type],
                        values[&forward],
                        values[&backward],
                        Arc::clone(evidence),
                    ),
                    | Value::Variable(index) => core.value_variable(Zone::Intuitionistic, index),
                    | Value::Constant(index) => core.value_constant(index),
                    | Value::Unit => core.value_unit(),
                    | Value::Literal(ref literal) => core.value_literal(literal.clone()),
                    | Value::Pair(first, second) => {
                        core.value_pair(values[&first], values[&second])
                    },
                    | Value::Injection(side, body) => core.value_injection(side, values[&body]),
                    | Value::Thunk(body) => core.value_thunk(computations[&body]),
                    | Value::Lift { ref target, body } => {
                        core.value_lift(target.clone(), values[&body])
                    },
                    | Value::Quote(quoted) => core.value_quote(types[&quoted]),
                    | Value::QuoteComputation(quoted) => {
                        core.value_quote_computation(comp_types[&quoted])
                    },
                    | Value::StaticApplication(head, argument) => {
                        core.value_static_application(values[&head], values[&argument])
                    },
                };
                values.insert(id, value);
            },
            | AnyNode::Computation(id) => {
                let computation = match *arena.computation(id).expect("fixture computation") {
                    | Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                    } => core.computation_data_case(
                        values[&scrutinee],
                        comp_types[&motive],
                        branches.iter().map(|branch| computations[branch]).collect(),
                    ),
                    | Computation::RecordProjection(record, ref label) => {
                        core.computation_record_projection(values[&record], label.clone())
                    },
                    | Computation::Absurd(_) => {
                        panic!("empty elimination is outside the path fixture fragment")
                    },
                    | Computation::Transport(path, value) => {
                        core.computation_transport(values[&path], values[&value])
                    },
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
                };
                computations.insert(id, computation);
            },
            | AnyNode::ValueType(id) => {
                let ty = match *(arena.value_type(id).expect("fixture value type")) {
                    | ValueType::Data {
                        ref declaration,
                        ref arguments,
                    } => core.value_type_data(
                        *declaration,
                        arguments.iter().map(|argument| values[argument]).collect(),
                    ),
                    | ValueType::Record(ref fields) => core.value_type_record(
                        fields
                            .iter()
                            .map(|(label, field)| (label.clone(), types[field]))
                            .collect(),
                    ),
                    | ValueType::List(_) | ValueType::Session { .. } => {
                        panic!("recursive inhabitants stay outside the first-order path producer")
                    },
                    | ValueType::PathUniverse(source, target) => {
                        core.value_type_path_universe(values[&source], values[&target])
                    },
                    | ValueType::Empty => {
                        panic!("empty types are outside the path fixture fragment")
                    },
                    | ValueType::Base(base) => core.value_type_base(base),
                    | ValueType::Unit => core.value_type_unit(),
                    | ValueType::Product(first, second) => {
                        core.value_type_product(types[&first], types[&second])
                    },
                    | ValueType::Sum(first, second) => {
                        core.value_type_sum(types[&first], types[&second])
                    },
                    | ValueType::Thunk(body) => core.value_type_thunk(comp_types[&body]),
                    | ValueType::Universe { sort, ref level } => {
                        core.value_type_universe(gandr_core_term::Sort::Ground(sort), level.clone())
                    },
                    | ValueType::Lift { inner, ref target } => {
                        core.value_type_lift(types[&inner], target.clone())
                    },
                    | ValueType::Element { code, ref target } => {
                        core.value_type_element(values[&code], target.clone())
                    },
                    | ValueType::Abstract(index) => core.value_type_abstract(index),
                    | ValueType::StaticPi { domain, codomain } => {
                        core.value_type_static_pi(types[&domain], types[&codomain])
                    },
                };
                types.insert(id, ty);
            },
            | AnyNode::CompType(id) => {
                let ty = match arena.comp_type(id).expect("fixture computation type") {
                    | &CompType::Returner(result) => core.comp_type_returner(types[&result]),
                    | &CompType::Arrow { domain, codomain } => {
                        core.comp_type_arrow(types[&domain], comp_types[&codomain])
                    },
                    | &CompType::Pi { domain, codomain } => {
                        core.comp_type_pi(types[&domain], comp_types[&codomain])
                    },
                    | &CompType::Element { code, ref target } => {
                        core.comp_type_element(values[&code], target.clone())
                    },
                };
                comp_types.insert(id, ty);
            },
        }
    }
    (core, computations[&left], computations[&right])
}

/// Run `NbE` and retain its untrusted verdict and complete trace.
///
/// # Specification
/// - requires: closed computations in the supported fixture fragment.
/// - ensures: no kernel reducer or verdict produces the claim; all returned
///   decision anchors are independent of either syntax arena.
/// - provides: the separate engine's verdict and its complete portable
///   dialogue.
/// - panics: on an operational fixture failure.
///
/// # Adequacy
/// - hypothesis: L3 — both positive and negative claims are replayed.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
#[spec(ensures: |ret| ret.1.0.iter().all(|step| match *step {
    ConversionDecision::ReduceLeft { redex } | ConversionDecision::ReduceRight { redex } => redex == ReplayNode::Other,
    ConversionDecision::ConstShortcut { constant } | ConversionDecision::Unfold { constant } | ConversionDecision::Postpone { constant } | ConversionDecision::Freeze { constant, .. } => constant == ReplayNode::Other,
    ConversionDecision::EtaExpand { variable, .. } => variable == ReplayNode::Other,
    ConversionDecision::Force { thunk } => thunk == ReplayNode::Other,
    ConversionDecision::ComparedShared { left, right } => left == ReplayNode::Other && right == ReplayNode::Other,
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } => true,
}))]
fn engine(
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
        Dialogue(
            log.decisions()
                .copied()
                .map(portable)
                .map(super::anchor)
                .collect(),
        ),
    )
}

/// Produce round trips on the constructor samples; admission independently
/// derives the symbolic obligations and checks the coverage.
///
/// # Specification
/// - requires: the samples and maps belong to the supported fixture fragment.
/// - ensures: one dialogue per source and target sample, recording the engine's
///   actual traces, including failures.
/// - provides: untrusted evidence for independent symbolic admission.
/// - panics: on an operational fixture failure.
///
/// # Adequacy
/// - hypothesis: L3 — finite sampling cannot certify a constant Base map.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[spec(ensures: |ret| ret.source.len() == source.len() && ret.target.len() == target.len())]
pub fn evidence(
    arena: &mut TermArena,
    source: &[ValueId],
    target: &[ValueId],
    forward: ValueId,
    backward: ValueId,
) -> Arc<PathEvidence>
{
    let mut evidence = PathEvidence::default();
    for (first, second, patterns, dialogues) in [
        (forward, backward, source, &mut evidence.source),
        (backward, forward, target, &mut evidence.target),
    ] {
        for &value in patterns {
            let first = apply(arena, first, value);
            let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
            let second = apply(arena, second, variable);
            let composite = arena.computation_bind(first, second);
            let identity = arena.computation_return(value);
            let (_, dialogue) = engine(arena, composite, identity);
            dialogues.push(dialogue.0.into_iter().map(portable).collect());
        }
    }
    Arc::new(evidence)
}

/// Construct a raw Bool equivalence with engine-produced evidence.
///
/// # Specification
/// - requires: the maps and Boolean fixture belong to the supported fragment.
/// - ensures: preserves the classifier and both directed map identities.
/// - provides: raw native syntax carrying independent producer evidence.
/// - fails: never.
/// - panics: on an operational producer failure.
///
/// # Adequacy
/// - hypothesis: L3 — false inverse claims reach and fail symbolic admission.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[spec(ensures: |ret| matches!(arena.value(ret), Some(&Value::PathEquiv { path_type, forward: first, backward: second, .. }) if first == forward && second == backward && matches!(arena.value_type(path_type), Some(&ValueType::PathUniverse(source, target)) if source == boolean.code && target == boolean.code)))]
fn equivalence(
    arena: &mut TermArena,
    boolean: Boolean,
    forward: ValueId,
    backward: ValueId,
) -> ValueId
{
    let samples = [boolean.truth, boolean.falsity];
    let evidence = evidence(arena, &samples, &samples, forward, backward);
    let classifier = arena.value_type_path_universe(boolean.code, boolean.code);
    arena.value_path_equiv(classifier, forward, backward, evidence)
}

/// Stage and offer a definition through the ordinary admission choke point.
///
/// # Specification
/// - requires: the builder returns roots in its supplied arena.
/// - ensures: success adds exactly one checked declaration at the old boundary;
///   refusal adds none.
/// - provides: the ordinary admission result, with no unchecked bypass.
/// - fails: the kernel's formation, typing or replay refusal.
/// - panics: only as the caller's builder does.
///
/// # Adequacy
/// - hypothesis: L3 — a forged equivalence cannot acquire an admission receipt.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[spec(captures: before = environment.entries().len(), ensures: |ret| ret.as_ref().map_or_else(|_| environment.entries().len() == before, |id| environment.entries().len() == before.saturating_add(1) && usize::from(id.position()) == before))]
fn offer<Build>(
    environment: &mut Environment,
    build: Build,
) -> Result<CheckedId, KernelError>
where
    Build: FnOnce(&mut TermArena) -> (ValueTypeId, ValueId),
{
    let mut staging = environment.stage();
    let (declared, body) = build(staging.arena());
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    environment.add_decl(staged)
}

/// Admit the native Bool negation path, retaining its arena roots.
///
/// # Specification
/// - requires: no unresolved staging lies above the new fixture.
/// - ensures: admits one native path whose two maps are Boolean negation.
/// - provides: the fixture roots retained by that admission.
/// - fails: never.
/// - panics: on a producer or kernel disagreement.
///
/// # Adequacy
/// - hypothesis: L3 — both Boolean inputs compute through the admitted path.
/// - witness: `path_universe::tests::transport_computes`
#[spec(captures: before = environment.entries().len(), ensures: |ret| environment.entries().len() == before.saturating_add(1) && matches!(environment.arena().value(ret.1), Some(&Value::PathEquiv { forward, backward, .. }) if forward == ret.0.not && backward == ret.0.not))]
fn admit_negation(environment: &mut Environment) -> (Boolean, ValueId)
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let boolean = boolean(arena);
    let path = equivalence(arena, boolean, boolean.not, boolean.not);
    let declared = arena.value_type_path_universe(boolean.code, boolean.code);
    let staged = staging.def(LevelSignature::monomorphic(), declared, path);
    let _checked = environment.add_decl(staged).expect("native path admission");
    (boolean, path)
}

/// Admit a declaration whose suspended body is native transport, and return
/// the computation and its independently chosen expected returner.
///
/// # Specification
/// - requires: the native transport checks at the supplied target type.
/// - ensures: admits one suspended transport and retains the independent
///   expected returner without replacing either operand.
/// - provides: the two computations offered to the independent producer.
/// - fails: never.
/// - panics: if native transport admission refuses.
///
/// # Adequacy
/// - hypothesis: L3 — a wrong target value remains distinguishable by replay.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
#[spec(captures: [before = environment.entries().len(), expected_input = expected], ensures: |ret| environment.entries().len() == before.saturating_add(1) && matches!(environment.arena().computation(ret.0), Some(&Computation::Transport(path, value)) if path == term.path && value == term.value) && matches!(environment.arena().computation(ret.1), Some(&Computation::Return(value)) if value == expected_input))]
fn admit_transport(
    environment: &mut Environment,
    term: Transport,
    target: ValueTypeId,
    expected: ValueId,
) -> (ComputationId, ComputationId)
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let result = arena.comp_type_returner(target);
    let declared = arena.value_type_thunk(result);
    let computation = arena.computation_transport(term.path, term.value);
    let body = arena.value_thunk(computation);
    let expected = arena.computation_return(expected);
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    let _checked = environment
        .add_decl(staged)
        .expect("native transport admission");
    (computation, expected)
}

/// Replay through the public consumer boundary and require arena restoration.
///
/// # Specification
/// - requires: `term` and `expected` are well-typed admitted transport sides.
/// - ensures: replays the supplied claim without retaining temporary syntax.
/// - provides: the kernel verdict, not the engine claim.
/// - fails: never.
/// - panics: if the native transport is ill-typed or staging leaks.
///
/// # Adequacy
/// - hypothesis: L3 — forged evidence refuses while a real reduction succeeds.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
#[spec(captures: [before = environment.arena().watermark()], ensures: environment.arena().watermark() == before)]
fn replay(
    environment: &mut Environment,
    term: Transport,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
) -> KernelVerdict
{
    let mut staging = environment.stage();
    let mark = staging.arena().watermark();
    let verdict = replay_transport(
        staging.arena(),
        term,
        expected,
        claim,
        dialogue,
        ReplayBudget::DEFAULT,
    )
    .expect("native transport typing");
    assert_eq!(staging.arena().watermark(), mark);
    staging.discard();
    verdict
}

/// Compare already admitted native certificate values by the ordinary engine
/// and kernel replay machines.
///
/// # Specification
/// - requires: both values are already admitted native certificates.
/// - ensures: independently produces and replays a conversion claim, retaining
///   neither temporary return wrappers nor reduction syntax.
/// - provides: the ordinary kernel conversion verdict.
/// - fails: never.
/// - panics: on an operational producer failure.
///
/// # Adequacy
/// - hypothesis: L3 — evidence bytes do not collapse distinct certificate maps.
/// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
#[spec(captures: [before = environment.arena().watermark()], ensures: environment.arena().watermark() == before)]
fn compare_paths(
    environment: &mut Environment,
    left: ValueId,
    right: ValueId,
) -> KernelVerdict
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let left_return = arena.computation_return(left);
    let right_return = arena.computation_return(right);
    let (claim, dialogue) = engine(arena, left_return, right_return);
    let verdict = crate::replay::replay(
        arena,
        &Unfoldings::default(),
        ReplaySides::Computations(left_return, right_return),
        claim,
        dialogue.0,
        ReplayBudget::DEFAULT,
    );
    staging.discard();
    verdict
}

#[test]
fn transport_computes()
{
    let mut environment = Environment::new();
    let (boolean, path) = admit_negation(&mut environment);
    let term = Transport {
        path,
        value: boolean.falsity,
    };
    let (computation, expected) =
        admit_transport(&mut environment, term, boolean.ty, boolean.truth);
    let (claim, dialogue) = engine(environment.arena(), computation, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    assert_eq!(
        replay(&mut environment, term, expected, claim, &dialogue),
        KernelVerdict::Convertible
    );
    let mut staging = environment.stage();
    let mark = staging.arena().watermark();
    assert_eq!(
        replay_transport(
            staging.arena(),
            term,
            expected,
            claim,
            &dialogue,
            ReplayBudget::from(0_u64)
        ),
        Err(KernelError::Path(PathError::Budget))
    );
    assert_eq!(staging.arena().watermark(), mark);
    staging.discard();
}

#[test]
fn it_computes_through_a_former()
{
    let mut environment = Environment::new();
    let (boolean, negation) = admit_negation(&mut environment);
    let mut staging = environment.stage();
    let arena = staging.arena();
    let product = arena.value_type_product(boolean.ty, boolean.ty);
    let code = arena.value_quote(product);
    let declared = arena.value_type_path_universe(code, code);
    let path = arena.value_path_product(negation, negation);
    let value = arena.value_pair(boolean.truth, boolean.falsity);
    let expected_pair = arena.value_pair(boolean.falsity, boolean.truth);
    let first = arena.computation_transport(negation, boolean.truth);
    let second = arena.computation_transport(negation, boolean.falsity);
    let first_expected = arena.computation_return(boolean.falsity);
    let second_expected = arena.computation_return(boolean.truth);
    let staged = staging.def(LevelSignature::monomorphic(), declared, path);
    let _checked = environment.add_decl(staged).expect("native product path");
    let term = Transport { path, value };
    let (computation, expected) = admit_transport(&mut environment, term, product, expected_pair);
    let (claim, dialogue) = engine(environment.arena(), computation, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    assert_eq!(
        replay(&mut environment, term, expected, claim, &dialogue),
        KernelVerdict::Convertible
    );
    let (_, first) = engine(environment.arena(), first, first_expected);
    let (_, second) = engine(environment.arena(), second, second_expected);
    let mut paired = Dialogue::pair(first, second);
    assert_eq!(
        replay(&mut environment, term, expected, claim, &paired),
        KernelVerdict::Convertible
    );
    paired.0.push(ConversionDecision::Decompose);
    assert!(matches!(
        replay(&mut environment, term, expected, claim, &paired),
        KernelVerdict::Declined(_)
    ));
}

#[test]
fn refl_collapses()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let boolean = boolean(staging.arena());
    let path = staging.arena().value_path_refl(boolean.code);
    let declared = staging
        .arena()
        .value_type_path_universe(boolean.code, boolean.code);
    let staged = staging.def(LevelSignature::monomorphic(), declared, path);
    let _checked = environment.add_decl(staged).expect("native reflexivity");
    for value in [boolean.truth, boolean.falsity] {
        let term = Transport { path, value };
        let (computation, expected) = admit_transport(&mut environment, term, boolean.ty, value);
        let (claim, dialogue) = engine(environment.arena(), computation, expected);
        assert_eq!(
            replay(&mut environment, term, expected, claim, &dialogue),
            KernelVerdict::Convertible
        );
        let mut staging = environment.stage();
        let Reduction::Reduced(reduct) = beta(staging.arena(), term).expect("native beta")
        else {
            panic!("reflexivity is not neutral")
        };
        assert_eq!(
            staging.arena().computation(reduct),
            Some(&Computation::Return(value))
        );
        staging.discard();
    }
}

#[test]
fn a_wrong_answer_is_caught()
{
    let mut environment = Environment::new();
    let (boolean, path) = admit_negation(&mut environment);
    let term = Transport {
        path,
        value: boolean.falsity,
    };
    let (computation, wrong) = admit_transport(&mut environment, term, boolean.ty, boolean.falsity);
    let (claim, dialogue) = engine(environment.arena(), computation, wrong);
    assert_eq!(claim, EngineClaim::NotConvertible);
    assert_eq!(
        replay(&mut environment, term, wrong, claim, &dialogue),
        KernelVerdict::NotConvertible
    );
    assert!(matches!(
        replay(
            &mut environment,
            term,
            wrong,
            EngineClaim::Convertible,
            &dialogue
        ),
        KernelVerdict::Declined(_)
    ));
}

#[test]
fn a_non_equivalence_is_refused()
{
    let mut environment = Environment::new();
    let before = environment.arena().watermark();
    let bad = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let returned = arena.computation_return(boolean.truth);
        let lambda = arena.computation_lambda(returned);
        let constant = arena.value_thunk(lambda);
        let path = equivalence(arena, boolean, constant, constant);
        (
            arena.value_type_path_universe(boolean.code, boolean.code),
            path,
        )
    });
    assert!(matches!(
        bad,
        Err(KernelError::Path(PathError::RoundTrip {
            direction: Direction::Source,
            pattern: PatternPosition(1),
            verdict: KernelVerdict::Declined(_)
        }))
    ));
    assert_eq!(environment.arena().watermark(), before);
    // A good first certificate must not cache admission of the same maps
    // carrying missing evidence later in this very declaration.
    let missing = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let good = equivalence(arena, boolean, boolean.not, boolean.not);
        let ty = arena.value_type_path_universe(boolean.code, boolean.code);
        let bad = arena.value_path_equiv(
            ty,
            boolean.not,
            boolean.not,
            Arc::new(PathEvidence::default()),
        );
        let declared = arena.value_type_product(ty, ty);
        (declared, arena.value_pair(good, bad))
    });
    assert!(matches!(
        missing,
        Err(KernelError::Path(PathError::Coverage(Direction::Source)))
    ));
    let mistyped = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let ty = arena.value_type_path_universe(boolean.code, boolean.code);
        let unit = arena.value_unit();
        (
            ty,
            arena.value_path_equiv(ty, unit, boolean.not, Arc::new(PathEvidence::default())),
        )
    });
    assert!(matches!(mistyped, Err(KernelError::ValueTypeMismatch(_))));
    let unsupported = offer(&mut environment, |arena| {
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let thunk = arena.value_type_thunk(returner);
        let code = arena.value_quote(thunk);
        (
            arena.value_type_path_universe(code, code),
            arena.value_path_refl(code),
        )
    });
    assert!(matches!(
        unsupported,
        Err(KernelError::Path(PathError::UnsupportedType(_)))
    ));
    let open = offer(&mut environment, |arena| {
        let code = arena.value_variable(DeBruijnIndex::from(0_u32));
        (
            arena.value_type_path_universe(code, code),
            arena.value_path_refl(code),
        )
    });
    assert!(matches!(
        open,
        Err(KernelError::Path(PathError::UnsupportedCode(_)))
    ));
    // A one-sided inverse passes its Unit source but fails the Bool target.
    let one_sided = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let unit_type = arena.value_type_unit();
        let code = arena.value_quote(unit_type);
        let unit = arena.value_unit();
        let forward = arena.computation_return(boolean.falsity);
        let forward = arena.computation_lambda(forward);
        let forward = arena.value_thunk(forward);
        let backward = arena.computation_return(unit);
        let backward = arena.computation_lambda(backward);
        let backward = arena.value_thunk(backward);
        let evidence = evidence(
            arena,
            &[unit],
            &[boolean.truth, boolean.falsity],
            forward,
            backward,
        );
        let ty = arena.value_type_path_universe(code, boolean.code);
        (ty, arena.value_path_equiv(ty, forward, backward, evidence))
    });
    assert!(matches!(
        one_sided,
        Err(KernelError::Path(PathError::RoundTrip {
            direction: Direction::Target,
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_)
        }))
    ));
    let sampled = offer(&mut environment, |arena| {
        let string = arena.value_type_base(BaseType::String);
        let code = arena.value_quote(string);
        let sample = arena.value_literal(gandr_kernel_term::Literal::Text(
            gandr_kernel_term::StringLiteral::new("sample".into()),
        ));
        let returned = arena.computation_return(sample);
        let lambda = arena.computation_lambda(returned);
        let constant = arena.value_thunk(lambda);
        let evidence = evidence(arena, &[sample], &[sample], constant, constant);
        let ty = arena.value_type_path_universe(code, code);
        (ty, arena.value_path_equiv(ty, constant, constant, evidence))
    });
    assert!(matches!(
        sampled,
        Err(KernelError::Path(PathError::RoundTrip {
            direction: Direction::Source,
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_)
        }))
    ));
    let valid = offer(&mut environment, |arena| {
        let string = arena.value_type_base(BaseType::String);
        let product = arena.value_type_product(string, string);
        let code = arena.value_quote(product);
        let sample = arena.value_literal(gandr_kernel_term::Literal::Text(
            gandr_kernel_term::StringLiteral::new("sample".into()),
        ));
        let pair = arena.value_pair(sample, sample);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let identity = arena.computation_return(variable);
        let identity = arena.computation_lambda(identity);
        let identity = arena.value_thunk(identity);
        let evidence = evidence(arena, &[pair], &[pair], identity, identity);
        let ty = arena.value_type_path_universe(code, code);
        (ty, arena.value_path_equiv(ty, identity, identity, evidence))
    })
    .expect("symbolic identity on two independent Base leaves");
    assert_eq!(usize::from(valid.position()), 0);
}

#[test]
fn certificate_identity_stays_out_of_conversion()
{
    let mut environment = Environment::new();
    let (boolean, first) = admit_negation(&mut environment);
    let mut staging = environment.stage();
    let arena = staging.arena();
    let twice = compose(arena, boolean.not, boolean.not);
    let original = compose(arena, twice, boolean.not);
    let thrice = inlined_triple_negation(arena);
    for value in [boolean.truth, boolean.falsity] {
        let original = apply(arena, original, value);
        let inlined = apply(arena, thrice, value);
        assert_eq!(engine(arena, original, inlined).0, EngineClaim::Convertible);
    }
    let second = equivalence(arena, boolean, boolean.not, thrice);
    let ty = arena.value_type_path_universe(boolean.code, boolean.code);
    let staged = staging.def(LevelSignature::monomorphic(), ty, second);
    let _checked = environment
        .add_decl(staged)
        .expect("native not/triple-not equivalence");
    assert_eq!(
        compare_paths(&mut environment, first, second),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        compare_paths(&mut environment, first, first),
        KernelVerdict::Convertible
    );
    // Equality erases only evidence, whereas the admission key above binds it.
    let mut staging = environment.stage();
    let different_evidence = staging.arena().value_path_equiv(
        ty,
        boolean.not,
        boolean.not,
        Arc::new(PathEvidence::default()),
    );
    assert_eq!(
        crate::conv::equal_values(staging.arena(), first, different_evidence),
        crate::conv::Convertibility::Convertible
    );
    let mut table = crate::encoding::ContentTable::new();
    assert_ne!(
        crate::encoding::encode_support(
            &mut table,
            staging.arena(),
            crate::encoding::SupportGoal::SynthValue(first),
            &[]
        ),
        crate::encoding::encode_support(
            &mut table,
            staging.arena(),
            crate::encoding::SupportGoal::SynthValue(different_evidence),
            &[]
        ),
        "erased conversion evidence still changes admission content"
    );
    staging.discard();
}

#[test]
fn no_k()
{
    let mut environment = Environment::new();
    let (boolean, path) = admit_negation(&mut environment);
    let mut staging = environment.stage();
    let refl = staging.arena().value_path_refl(boolean.code);
    let ty = staging
        .arena()
        .value_type_path_universe(boolean.code, boolean.code);
    let staged = staging.def(LevelSignature::monomorphic(), ty, refl);
    let _checked = environment.add_decl(staged).expect("native reflexivity");
    assert_eq!(
        compare_paths(&mut environment, path, refl),
        KernelVerdict::NotConvertible
    );
    // The native destructor table permits neither forcing nor matching a
    // path variable. No string dispatcher stands between these terms and the
    // ordinary checker, and a nontrivial self-path has not collapsed to refl.
    let forced = offer(&mut environment, |arena| {
        let path_type = arena.value_type_path_universe(boolean.code, boolean.code);
        let result = arena.comp_type_returner(boolean.ty);
        let arrow = arena.comp_type_arrow(path_type, result);
        let declared = arena.value_type_thunk(arrow);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_force(variable);
        let body = arena.computation_lambda(body);
        (declared, arena.value_thunk(body))
    });
    assert!(matches!(
        forced,
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Thunk,
            ..
        })
    ));
    let matched = offer(&mut environment, |arena| {
        let path_type = arena.value_type_path_universe(boolean.code, boolean.code);
        let result = arena.comp_type_returner(boolean.ty);
        let arrow = arena.comp_type_arrow(path_type, result);
        let declared = arena.value_type_thunk(arrow);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let branch = arena.computation_return(boolean.truth);
        let body = arena.computation_case(variable, branch, branch);
        let body = arena.computation_lambda(body);
        (declared, arena.value_thunk(body))
    });
    assert!(matches!(
        matched,
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Sum,
            ..
        })
    ));
}
