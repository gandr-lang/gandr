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
use gandr_core_nbe::BinderLevel;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::MachineSettings;
use gandr_core_nbe::MachineVerdict;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::Problem;
use gandr_core_nbe::ResharingMemo;
use gandr_core_nbe::TermFace;
use gandr_core_nbe::Unfolding;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::PathEvidence;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;
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
Value::Tuple(ref components) => components.len(),
Value::StaticApplication(..) | Value::PathProduct(..) | Value::ListCons(..) => 2,
Value::Injection(..) | Value::Lift { .. } | Value::Thunk(_) | Value::Quote(_) | Value::QuoteComputation(_) | Value::PathRefl(_) | Value::Univalence(_) => 1,
Value::SessionPath { .. } | Value::SessionFlow { .. } | Value::Stay { .. } | Value::ForwardFlow { .. } | Value::FunctionFlow { .. } | Value::Then { .. } | Value::FlowProduct(..) | Value::Here { .. } | Value::Returned(_) | Value::Higher { .. } | Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. } | Value::Variable(_) | Value::Constant(_) | Value::Literal(_) | Value::ListNil => 0,
}),
        AnyNode::Computation(id) => arena.computation(id).map_or(0, |matched_native_node| match *matched_native_node {
Computation::DataCase {ref branches,..} => branches.len().saturating_add(2),
Computation::Case { ref branches, .. } => branches.len().saturating_add(1),
Computation::Application(..) | Computation::Bind(..) | Computation::Transport(..) | Computation::With(..) => 2,
Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Return(_) | Computation::Force(_) | Computation::SigmaSplit { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::PathTransport { .. } | Computation::TelescopeTransport { .. } | Computation::Ride { .. } | Computation::TelescopeRide { .. } | Computation::RelatedApplication { .. } | Computation::Project(..) | Computation::Fixpoint { .. } => 1,
}),
        AnyNode::ValueType(id) => arena.value_type(id).map_or(0, |matched_native_node| match *matched_native_node {
ValueType::Data {ref arguments,..} => arguments.len(),
ValueType::Record(ref fields) => fields.len(),
ValueType::Product(ref parts) | ValueType::Sum(ref parts) => parts.len(),
ValueType::StaticPi { .. } | ValueType::PathUniverse(..) => 2,
ValueType::Thunk(_) | ValueType::Lift { .. } | ValueType::Element { .. } | ValueType::List(_) | ValueType::Staged { .. } => 1,
ValueType::Session { .. } | ValueType::FlowUniverse(..) | ValueType::Path { .. } | ValueType::Flow { .. } | ValueType::Bridge { .. } | ValueType::Base(_) | ValueType::Sigma { .. } | ValueType::Universe { .. } | ValueType::Abstract(_) => 0,
}),
        AnyNode::CompType(id) => match arena.comp_type(id) {
            Some(&CompType::Arrow { .. } | &CompType::Pi { .. } | &CompType::With(..)) => 2,
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
        V(id) => match *(arena.value(id).expect("fixture value")) {
            Value::Constructor {
                ref datatype,
                ref fields,
                ..
            } => core::iter::once(A(*datatype))
                .chain(fields.iter().copied().map(V))
                .collect(),
            Value::Record(ref fields) => fields.values().copied().map(V).collect(),
            Value::SessionPath { .. } | Value::SessionFlow { .. } => {
                panic!("session evidence has a separate finite producer")
            },
            Value::Here { .. }
            | Value::Stay { .. }
            | Value::ForwardFlow { .. }
            | Value::FunctionFlow { .. }
            | Value::Then { .. }
            | Value::FlowProduct(..)
            | Value::Returned(_)
            | Value::Higher { .. }
            | Value::HigherEvaluation { .. }
            | Value::QuantifiedEvaluation { .. } => {
                panic!("element identity is outside the universe-path fixture fragment")
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => vec![A(path_type), V(forward), V(backward)],
            Value::PathProduct(a, b) | Value::StaticApplication(a, b) | Value::ListCons(a, b) => {
                vec![V(a), V(b)]
            },
            Value::Tuple(ref components) => components.iter().copied().map(V).collect(),
            Value::PathRefl(a)
            | Value::Univalence(a)
            | Value::Injection(_, a)
            | Value::Lift { body: a, .. } => {
                vec![V(a)]
            },
            Value::Thunk(a) => vec![M(a)],
            Value::Quote(a) => vec![A(a)],
            Value::QuoteComputation(a) => vec![C(a)],
            Value::Variable(_) | Value::Constant(_) | Value::Literal(_) | Value::ListNil => {
                Vec::new()
            },
        },
        M(id) => match *arena.computation(id).expect("fixture computation") {
            Computation::DataCase {
                scrutinee,
                motive,
                ref branches,
            } => [V(scrutinee), C(motive)]
                .into_iter()
                .chain(branches.iter().copied().map(M))
                .collect(),
            Computation::SigmaSplit {
                scrutinee,
                motive,
                body,
            } => vec![V(scrutinee), C(motive), M(body)],
            Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => {
                vec![V(record)]
            },
            Computation::ListFold { .. } | Computation::ListCase { .. } => {
                panic!("list elimination is outside the path fixture fragment")
            },
            Computation::PathTransport { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeRide { .. }
            | Computation::RelatedApplication { .. } => {
                panic!("element identity is outside the universe-path fixture fragment")
            },
            Computation::Fixpoint { .. } => {
                panic!("recursion is outside the path fixture fragment")
            },
            Computation::Transport(a, b) => vec![V(a), V(b)],
            Computation::Lambda(a) | Computation::Project(_, a) => vec![M(a)],
            Computation::Application(a, b) => vec![M(a), V(b)],
            Computation::Return(a) | Computation::Force(a) => vec![V(a)],
            Computation::Bind(a, b) | Computation::With(a, b) => vec![M(a), M(b)],
            Computation::Case {
                scrutinee,
                ref branches,
            } => core::iter::once(V(scrutinee))
                .chain(branches.iter().copied().map(M))
                .collect(),
        },
        A(id) => match *(arena.value_type(id).expect("fixture value type")) {
            ValueType::Data { ref arguments, .. } => arguments.iter().copied().map(V).collect(),
            ValueType::Record(ref fields) => fields.values().copied().map(A).collect(),
            ValueType::List(_)
            | ValueType::Session { .. }
            | ValueType::Path { .. }
            | ValueType::Flow { .. }
            | ValueType::Bridge { .. }
            | ValueType::FlowUniverse(..) => {
                panic!("recursive inhabitants stay outside the first-order path producer")
            },
            ValueType::PathUniverse(a, b) => vec![V(a), V(b)],
            ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                parts.iter().copied().map(A).collect()
            },
            ValueType::StaticPi {
                domain: a,
                codomain: b,
            }
            | ValueType::Sigma {
                first: a,
                second: b,
            } => vec![A(a), A(b)],
            ValueType::Thunk(a) => vec![C(a)],
            ValueType::Lift { inner: a, .. } | ValueType::Staged { base: a, .. } => vec![A(a)],
            ValueType::Element { code: a, .. } => vec![V(a)],
            ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_) => Vec::new(),
        },
        C(id) => match arena.comp_type(id).expect("fixture computation type") {
            &CompType::Returner(a) => vec![A(a)],
            &CompType::Arrow {
                domain: a,
                codomain: b,
            }
            | &CompType::Pi {
                domain: a,
                codomain: b,
            } => vec![A(a), C(b)],
            &CompType::Element { code: a, .. } => vec![V(a)],
            &CompType::With(a, b) => vec![C(a), C(b)],
            &CompType::Codata { ref arguments, .. } => arguments.iter().copied().map(V).collect(),
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
    let ty = arena.value_type_sum(&[unit_type, unit_type]);
    let code = arena.value_quote(ty);
    let unit = arena.value_unit();
    let truth = arena.value_injection(Side::Left.into(), unit);
    let falsity = arena.value_injection(Side::Right.into(), unit);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let left = arena.value_injection(Side::Right.into(), variable);
    let right = arena.value_injection(Side::Left.into(), variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let body = arena.computation_case(variable, &[left, right]);
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
    let Some(&Computation::Case { scrutinee, ref branches }) = arena.computation(case) else { return false; };
    let &[on_left, on_right] = &**branches else { return false; };
    matches!(arena.value(scrutinee), Some(&Value::Variable(index)) if u32::from(index) == 0)
        && [(on_left, Side::Right), (on_right, Side::Left)].into_iter().all(|(branch, side)| {
            let Some(&Computation::Bind(payload, inner)) = arena.computation(branch) else { return false; };
            let Some(&Computation::Bind(again, returned)) = arena.computation(inner) else { return false; };
            let Some(&Computation::Return(injection)) = arena.computation(returned) else { return false; };
            payload == again && arena.computation(payload) == Some(&Computation::Return(scrutinee))
                && arena.value(injection) == Some(&Value::Injection(side.into(), scrutinee))
        })
})]
fn inlined_triple_negation(arena: &mut TermArena) -> ValueId
{
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let payload = arena.computation_return(variable);
    let mut branch = |side| {
        let value = arena.value_injection(Summand::from(side), variable);
        let result = arena.computation_return(value);
        let result = arena.computation_bind(payload, result);
        arena.computation_bind(payload, result)
    };
    let left = branch(Side::Right);
    let right = branch(Side::Left);
    let body = arena.computation_case(variable, &[left, right]);
    let body = arena.computation_lambda(body);
    arena.value_thunk(body)
}

/// Erase arena-local hints, preserving every decision and premise position.
///
/// # Specification
/// trivial.
fn portable<Node>(decision: ConversionDecision<Node>) -> ConversionDecision<()>
{
    decision.map(|_| ())
}

/// Translate the reachable native graph without running a kernel reduction,
/// with each of `bodies` beside the two computations.
///
/// # Specification
/// - ensures: every former, binder and translator body is preserved; the
///   translated bodies follow in the order given.
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
/// - witness: `path_universe::tests::a_translator_may_name_an_admitted_definition`
#[spec(ensures: |ret| ret.0.computation(ret.1).is_some() && ret.0.computation(ret.2).is_some() && (left != right || ret.1 == ret.2) && ret.3.len() == bodies.len())]
fn translate(
    arena: &TermArena,
    (left, right): (ComputationId, ComputationId),
    bodies: &[ValueId],
) -> (
    CoreArena,
    gandr_core_term::ComputationId,
    gandr_core_term::ComputationId,
    Vec<gandr_core_term::ValueId>,
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
    pending.extend(bodies.iter().map(|&body| (AnyNode::Value(body), false)));
    // One buffer per operand kind, refilled for each tuple, case and product.
    let (mut operands, mut branch_ids, mut part_ids) = (Vec::new(), Vec::new(), Vec::new());
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
            AnyNode::Value(id) => {
                let value = match *(arena.value(id).expect("fixture value")) {
                    Value::Constructor {
                        ref datatype,
                        ref tag,
                        ref fields,
                    } => core.value_constructor(
                        types[datatype],
                        *tag,
                        fields.iter().map(|field| values[field]).collect(),
                    ),
                    Value::Record(ref fields) => core.value_record(
                        fields
                            .iter()
                            .map(|(label, field)| (label.clone(), values[field]))
                            .collect(),
                    ),
                    Value::ListNil => core.value_list_nil(),
                    Value::ListCons(head, tail) => {
                        core.value_list_cons(values[&head], values[&tail])
                    },
                    Value::SessionPath { .. } | Value::SessionFlow { .. } => {
                        panic!("session evidence has a separate finite producer")
                    },
                    Value::Here { .. }
                    | Value::Univalence { .. }
                    | Value::Stay { .. }
                    | Value::ForwardFlow { .. }
                    | Value::FunctionFlow { .. }
                    | Value::Then { .. }
                    | Value::FlowProduct(..)
                    | Value::Returned(_)
                    | Value::Higher { .. }
                    | Value::HigherEvaluation { .. }
                    | Value::QuantifiedEvaluation { .. } => {
                        panic!("element identity is outside the universe-path fixture fragment")
                    },
                    Value::PathRefl(code) => core.value_path_refl(values[&code]),
                    Value::PathProduct(first, second) => {
                        core.value_path_product(values[&first], values[&second])
                    },
                    Value::PathEquiv {
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
                    Value::Variable(index) => core.value_variable(Zone::Intuitionistic, index),
                    Value::Constant(index) => core.value_constant(index),
                    Value::Literal(ref literal) => core.value_literal(literal.clone()),
                    Value::Tuple(ref components) => {
                        operands.clear();
                        operands.extend(components.iter().map(|component| values[component]));
                        core.value_tuple(&operands)
                    },
                    Value::Injection(summand, body) => core.value_injection(summand, values[&body]),
                    Value::Thunk(body) => core.value_thunk(computations[&body]),
                    Value::Lift { ref target, body } => {
                        core.value_lift(target.clone(), values[&body])
                    },
                    Value::Quote(quoted) => core.value_quote(types[&quoted]),
                    Value::QuoteComputation(quoted) => {
                        core.value_quote_computation(comp_types[&quoted])
                    },
                    Value::StaticApplication(head, argument) => {
                        core.value_static_application(values[&head], values[&argument])
                    },
                };
                values.insert(id, value);
            },
            AnyNode::Computation(id) => {
                let computation = match *arena.computation(id).expect("fixture computation") {
                    Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                    } => core.computation_data_case(
                        values[&scrutinee],
                        comp_types[&motive],
                        branches.iter().map(|branch| computations[branch]).collect(),
                    ),
                    Computation::SigmaSplit {
                        scrutinee,
                        motive,
                        body,
                    } => core.computation_dependent_split(
                        values[&scrutinee],
                        gandr_core_term::ComponentCount::from(2_usize),
                        comp_types[&motive],
                        computations[&body],
                    ),
                    Computation::RecordProjection(record, ref label) => {
                        core.computation_record_projection(values[&record], label.clone())
                    },
                    Computation::TupleProjection(tuple, component) => {
                        core.computation_tuple_projection(values[&tuple], component)
                    },
                    Computation::ListFold { .. } | Computation::ListCase { .. } => {
                        panic!("list elimination is outside the path fixture fragment")
                    },
                    Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Ride { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. } => {
                        panic!("element identity is outside the universe-path fixture fragment")
                    },
                    Computation::Fixpoint { .. } => {
                        panic!("recursion is outside the path fixture fragment")
                    },
                    Computation::Transport(path, value) => {
                        core.computation_transport(values[&path], values[&value])
                    },
                    Computation::Return(value) => core.computation_return(values[&value]),
                    Computation::Force(value) => core.computation_force(values[&value]),
                    Computation::Lambda(body) => core.computation_lambda(computations[&body]),
                    Computation::Application(head, value) => {
                        core.computation_application(computations[&head], values[&value])
                    },
                    Computation::Bind(first, second) => {
                        core.computation_bind(computations[&first], computations[&second])
                    },
                    Computation::With(first, second) => {
                        core.computation_with(computations[&first], computations[&second])
                    },
                    Computation::Project(side, pair) => {
                        core.computation_project(side, computations[&pair])
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        branch_ids.clear();
                        branch_ids.extend(branches.iter().map(|branch| computations[branch]));
                        core.computation_case(values[&scrutinee], &branch_ids)
                    },
                };
                computations.insert(id, computation);
            },
            AnyNode::ValueType(id) => {
                let ty = match *(arena.value_type(id).expect("fixture value type")) {
                    ValueType::Data {
                        ref declaration,
                        ref arguments,
                    } => core.value_type_data(
                        *declaration,
                        arguments.iter().map(|argument| values[argument]).collect(),
                    ),
                    ValueType::Record(ref fields) => core.value_type_record(
                        fields
                            .iter()
                            .map(|(label, field)| (label.clone(), types[field]))
                            .collect(),
                    ),
                    ValueType::List(_)
                    | ValueType::Session { .. }
                    | ValueType::Path { .. }
                    | ValueType::Flow { .. }
                    | ValueType::Bridge { .. }
                    | ValueType::FlowUniverse(..) => {
                        panic!("recursive inhabitants stay outside the first-order path producer")
                    },
                    ValueType::PathUniverse(source, target) => {
                        core.value_type_path_universe(values[&source], values[&target])
                    },
                    ValueType::Base(base) => core.value_type_base(base),
                    ValueType::Staged { base, stage } => {
                        core.value_type_staged(types[&base], stage)
                    },
                    ValueType::Product(ref parts) => {
                        part_ids.clear();
                        part_ids.extend(parts.iter().map(|part| types[part]));
                        core.value_type_product(&part_ids)
                    },
                    ValueType::Sum(ref parts) => {
                        part_ids.clear();
                        part_ids.extend(parts.iter().map(|part| types[part]));
                        core.value_type_sum(&part_ids)
                    },
                    ValueType::Thunk(body) => core.value_type_thunk(comp_types[&body]),
                    ValueType::Universe { sort, ref level } => {
                        core.value_type_universe(gandr_core_term::Sort::Ground(sort), level.clone())
                    },
                    ValueType::Lift { inner, ref target } => {
                        core.value_type_lift(types[&inner], target.clone())
                    },
                    ValueType::Element { code, ref target } => {
                        core.value_type_element(values[&code], target.clone())
                    },
                    ValueType::Abstract(index) => core.value_type_abstract(index),
                    ValueType::StaticPi { domain, codomain } => {
                        core.value_type_static_pi(types[&domain], types[&codomain])
                    },
                    ValueType::Sigma { first, second } => {
                        core.value_type_sigma(types[&first], types[&second])
                    },
                };
                types.insert(id, ty);
            },
            AnyNode::CompType(id) => {
                let ty = match *arena.comp_type(id).expect("fixture computation type") {
                    CompType::Returner(result) => core.comp_type_returner(types[&result]),
                    CompType::Arrow { domain, codomain } => {
                        core.comp_type_arrow(types[&domain], comp_types[&codomain])
                    },
                    CompType::Pi { domain, codomain } => {
                        core.comp_type_pi(types[&domain], comp_types[&codomain])
                    },
                    CompType::Element { code, ref target } => {
                        core.comp_type_element(values[&code], target.clone())
                    },
                    CompType::With(first, second) => {
                        core.comp_type_with(comp_types[&first], comp_types[&second])
                    },
                    CompType::Codata { .. } => panic!("the fixtures name no codata type"),
                };
                comp_types.insert(id, ty);
            },
        }
    }
    let bodies = bodies.iter().map(|body| values[body]).collect();
    (core, computations[&left], computations[&right], bodies)
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
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } | ConversionDecision::ReturnEta { .. } | ConversionDecision::Reassociate { .. } => true,
}))]
fn engine(
    arena: &TermArena,
    left: ComputationId,
    right: ComputationId,
) -> (EngineClaim, Dialogue)
{
    defining_engine(arena, (left, right), &[], BinderLevel::from(0_u32))
}

/// Run `NbE` as [`engine`] does with each of `definitions` unfolding, in
/// admission order, to its body, and `opened` binders read as rigid variables.
///
/// # Specification
/// - requires: as [`engine`], save that both computations may stand under
///   `opened` binders; every body is closed and in the fixture fragment.
/// - ensures: as [`engine`], the constants unfolding as the machine decides.
/// - provides: the dialogue a translator naming an admitted definition carries.
/// - panics: on an operational fixture failure.
///
/// # Adequacy
/// - hypothesis: L3 — a path naming admitted negation replays only with the
///   unfoldings recorded.
/// - witness: `path_universe::tests::a_translator_may_name_an_admitted_definition`
#[spec(ensures: |ret| ret.1.0.iter().all(|step| match *step {
    ConversionDecision::ReduceLeft { redex } | ConversionDecision::ReduceRight { redex } => redex == ReplayNode::Other,
    ConversionDecision::ConstShortcut { constant } | ConversionDecision::Unfold { constant } | ConversionDecision::Postpone { constant } | ConversionDecision::Freeze { constant, .. } => constant == ReplayNode::Other,
    ConversionDecision::EtaExpand { variable, .. } => variable == ReplayNode::Other,
    ConversionDecision::Force { thunk } => thunk == ReplayNode::Other,
    ConversionDecision::ComparedShared { left, right } => left == ReplayNode::Other && right == ReplayNode::Other,
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } | ConversionDecision::ReturnEta { .. } | ConversionDecision::Reassociate { .. } => true,
}))]
fn defining_engine(
    arena: &TermArena,
    (left, right): (ComputationId, ComputationId),
    definitions: &[(ConstantIndex, ValueId)],
    opened: BinderLevel,
) -> (EngineClaim, Dialogue)
{
    let bodies: Vec<ValueId> = definitions.iter().map(|&(_, body)| body).collect();
    let (core, left, right, lowered) = translate(arena, (left, right), &bodies);
    let mut chain = LoweredChain::new();
    for (entry, (&(constant, _), body)) in definitions.iter().zip(lowered).enumerate() {
        let entry = u32::try_from(entry).expect("a small fixture chain");
        chain
            .define(
                constant,
                GlobalIndex::from(entry),
                Transparency::Manifest,
                &[],
                body,
            )
            .expect("a fixture definition");
    }
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mut bound = gandr_core_nbe::Environment::new();
    for level in 0 .. u32::from(opened) {
        let neutral = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: BinderLevel::from(level),
                },
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a fixture neutral");
        let value = domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a fixture neutral value");
        bound.extend(Zone::Intuitionistic, value);
    }
    let mut evaluate = |term| {
        gandr_core_nbe::eval_comp_within(
            &core,
            &mut domain,
            definitions,
            Fuel::from(4096_u32),
            term,
            bound.clone(),
        )
        .map(|(produced, _remaining)| produced)
    };
    let left = evaluate(left).expect("left evaluation");
    let right = evaluate(right).expect("right evaluation");
    let mut log = TraceLog::new();
    let report = gandr_core_nbe::decide::<_, ResharingMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::computations(left, right).under(opened),
        &mut log,
    )
    .expect("engine verdict");
    let claim = match report.verdict() {
        MachineVerdict::Convertible => EngineClaim::Convertible,
        MachineVerdict::NotConvertible => EngineClaim::NotConvertible,
        MachineVerdict::Declined(_) => EngineClaim::Declined,
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

/// [`evidence`] for patterns that stand under one binder each, a list's tail,
/// both directions over the same `patterns`.
///
/// # Specification
/// - requires: as [`evidence`], each pattern open in at most its innermost
///   variable.
/// - ensures: one dialogue per pattern on each side, the engine's trace with
///   the variable read as rigid.
/// - provides: untrusted evidence for a list code's coverage.
/// - panics: on an operational fixture failure.
///
/// # Adequacy
/// - hypothesis: L3 — the identity's dialogues admit at a rigid tail and the
///   kernel, not the evidence, fixes the cells.
/// - witness: `path_universe::tests::a_list_code_covers_one_cell_over_a_rigid_tail`
#[spec(ensures: |ret| ret.source.len() == patterns.len() && ret.target.len() == patterns.len())]
fn open_evidence(
    arena: &mut TermArena,
    patterns: &[ValueId],
    forward: ValueId,
    backward: ValueId,
) -> Arc<PathEvidence>
{
    let mut evidence = PathEvidence::default();
    for (first, second, dialogues) in [
        (forward, backward, &mut evidence.source),
        (backward, forward, &mut evidence.target),
    ] {
        for &value in patterns {
            let first = apply(arena, first, value);
            let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
            let second = apply(arena, second, variable);
            let composite = arena.computation_bind(first, second);
            let identity = arena.computation_return(value);
            let (_, dialogue) =
                defining_engine(arena, (composite, identity), &[], BinderLevel::from(1_u32));
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
    let product = arena.value_type_product(&[boolean.ty, boolean.ty]);
    let code = arena.value_quote(product);
    let declared = arena.value_type_path_universe(code, code);
    let path = arena.value_path_product(negation, negation);
    let value = arena.value_tuple(&[boolean.truth, boolean.falsity]);
    let expected_pair = arena.value_tuple(&[boolean.falsity, boolean.truth]);
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
        let declared = arena.value_type_product(&[ty, ty]);
        (declared, arena.value_tuple(&[good, bad]))
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
    assert!(matches!(
        mistyped,
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));
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
        let product = arena.value_type_product(&[string, string]);
        let code = arena.value_quote(product);
        let sample = arena.value_literal(gandr_kernel_term::Literal::Text(
            gandr_kernel_term::StringLiteral::new("sample".into()),
        ));
        let pair = arena.value_tuple(&[sample, sample]);
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
        crate::encoding::support_key(
            &mut table,
            staging.arena(),
            crate::encoding::SupportGoal::SynthValue(first),
            crate::encoding::Telescope::Whole(&[])
        ),
        crate::encoding::support_key(
            &mut table,
            staging.arena(),
            crate::encoding::SupportGoal::SynthValue(different_evidence),
            crate::encoding::Telescope::Whole(&[])
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
        let body = arena.computation_case(variable, &[branch, branch]);
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

#[test]
fn a_translator_may_name_an_admitted_definition()
{
    // Negation is admitted as a definition, and the path names it as both
    // translators. Each round trip unfolds it by replay against what the
    // environment admitted; the same path whose dialogues read negation as
    // rigid is refused at its first pattern.
    let mut environment = Environment::new();
    let negation = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let result = arena.comp_type_returner(boolean.ty);
        let arrow = arena.comp_type_arrow(boolean.ty, result);
        (arena.value_type_thunk(arrow), boolean.not)
    })
    .expect("negation")
    .position();
    let named = |environment: &mut Environment, unfolding: bool| {
        offer(environment, |arena| {
            let boolean = boolean(arena);
            let constant = arena.value_constant(negation);
            let definitions = [(negation, boolean.not)];
            let definitions = if unfolding { &definitions[..] } else { &[] };
            let mut evidence = PathEvidence::default();
            for dialogues in [&mut evidence.source, &mut evidence.target] {
                for value in [boolean.truth, boolean.falsity] {
                    let first = apply(arena, constant, value);
                    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
                    let second = apply(arena, constant, variable);
                    let composite = arena.computation_bind(first, second);
                    let identity = arena.computation_return(value);
                    let (_, dialogue) = defining_engine(
                        arena,
                        (composite, identity),
                        definitions,
                        BinderLevel::from(0_u32),
                    );
                    dialogues.push(dialogue.0.into_iter().map(portable).collect());
                }
            }
            let classifier = arena.value_type_path_universe(boolean.code, boolean.code);
            let path = arena.value_path_equiv(classifier, constant, constant, Arc::new(evidence));
            (classifier, path)
        })
    };
    named(&mut environment, true).expect("each round trip unfolds the admitted negation");
    assert!(matches!(
        named(&mut environment, false),
        Err(KernelError::Path(PathError::RoundTrip {
            direction: Direction::Source,
            pattern: PatternPosition(0),
            ..
        }))
    ));
}

#[test]
fn a_list_code_covers_one_cell_over_a_rigid_tail()
{
    // Reflexivity at lists of booleans, and the code inside a product.
    let mut environment = Environment::new();
    let refl = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let list = arena.value_type_list(boolean.ty);
        let code = arena.value_quote(list);
        (
            arena.value_type_path_universe(code, code),
            arena.value_path_refl(code),
        )
    });
    assert!(refl.is_ok(), "{refl:?}");
    let mut arena = TermArena::new();
    let bools = boolean(&mut arena);
    let list = arena.value_type_list(bools.ty);
    let pair = arena.value_type_product(&[bools.ty, list]);
    let code = arena.value_quote(pair);
    assert_eq!(super::code(&arena, code, ReplayBudget::DEFAULT), Ok(pair));

    // The empty list, then one cell per boolean over the same rigid tail: the
    // identity's round trips replay there, so the path admits.
    let lists =
        |environment: &mut Environment, forward: fn(&mut TermArena) -> ValueId, cells: usize| {
            offer(environment, |arena| {
                let boolean = boolean(arena);
                let list = arena.value_type_list(boolean.ty);
                let code = arena.value_quote(list);
                let empty = arena.value_list_nil();
                let tail = arena.value_variable(DeBruijnIndex::from(0_u32));
                let first = arena.value_list_cons(boolean.truth, tail);
                let second = arena.value_list_cons(boolean.falsity, tail);
                let patterns = [empty, first, second];
                let patterns = patterns.get(.. cells).unwrap_or(patterns.as_slice());
                let forward = forward(arena);
                let backward = identity_map(arena);
                let evidence = open_evidence(arena, patterns, forward, backward);
                let classifier = arena.value_type_path_universe(code, code);
                let path = arena.value_path_equiv(classifier, forward, backward, evidence);
                (classifier, path)
            })
        };
    let admitted = lists(&mut environment, identity_map, 3);
    assert!(admitted.is_ok(), "{admitted:?}");
    // Two dialogues for three patterns: the kernel's coverage, not the
    // evidence, chooses the cells.
    assert!(matches!(
        lists(&mut environment, identity_map, 2),
        Err(KernelError::Path(PathError::Coverage(Direction::Source)))
    ));
    // A translator to the empty list returns it at the empty pattern and at
    // no cell.
    let emptied = |arena: &mut TermArena| {
        let empty = arena.value_list_nil();
        let returned = arena.computation_return(empty);
        let body = arena.computation_lambda(returned);
        arena.value_thunk(body)
    };
    assert!(matches!(
        lists(&mut environment, emptied, 3),
        Err(KernelError::Path(PathError::RoundTrip {
            direction: Direction::Source,
            pattern: PatternPosition(1),
            ..
        }))
    ));
}

/// The identity map `thunk (λx. return x)`.
///
/// # Specification
/// trivial.
fn identity_map(arena: &mut TermArena) -> ValueId
{
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(variable);
    let lambda = arena.computation_lambda(returned);
    arena.value_thunk(lambda)
}

/// The round trip that holds by computation, `thunk (λx. return here(x))`.
///
/// # Specification
/// trivial.
fn reflexive_law(arena: &mut TermArena) -> ValueId
{
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let here = arena.value_here(variable);
    let returned = arena.computation_return(here);
    let lambda = arena.computation_lambda(returned);
    arena.value_thunk(lambda)
}

/// The bi-invertible record `#{to, #{#{g, law}, #{h, law}}}` over the maps
/// `to`, `g` and `h`, each law reflexivity at the bound point.
///
/// # Specification
/// trivial.
fn record(
    arena: &mut TermArena,
    [to, g, h]: [ValueId; 3],
) -> ValueId
{
    let law = reflexive_law(arena);
    let left = arena.value_tuple(&[g, law]);
    let right = arena.value_tuple(&[h, law]);
    let inverses = arena.value_tuple(&[left, right]);
    arena.value_tuple(&[to, inverses])
}

/// `Path(Type, ⌜T⌝, ⌜T⌝)` at the level-zero value universe.
///
/// # Specification
/// trivial.
fn identity_at(
    arena: &mut TermArena,
    ty: ValueTypeId,
) -> ValueTypeId
{
    let universe = arena.value_type_universe(
        gandr_kernel_term::GroundSort::Value,
        gandr_kernel_strata::Level::zero(),
    );
    let code = arena.value_quote(ty);
    arena.value_type_path(universe, code, code)
}

#[test]
fn univalence_is_admitted_on_its_record()
{
    // Lists of booleans admitted by `ua` on the identity's laws checked
    // against the record its identity names.
    let mut environment = Environment::new();
    let checked = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let list = arena.value_type_list(boolean.ty);
        let map = identity_map(arena);
        let equivalence = record(arena, [map, map, map]);
        (
            identity_at(arena, list),
            arena.value_univalence(equivalence),
        )
    });
    assert!(
        checked.is_ok(),
        "a record written out checks against the identity at Type: {checked:?}"
    );

    // The same record admitted at its type, then `ua` of it synthesised under
    // a transport in the decoded binder: the record's type names the codes
    // the transport moves between.
    let declared = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let list = arena.value_type_list(boolean.ty);
        let path_type = identity_at(arena, list);
        let record_type =
            super::univalence_record(arena, path_type).expect("an identity at Type names a record");
        let map = identity_map(arena);
        (record_type, record(arena, [map, map, map]))
    })
    .expect("the record checks against the record type its identity names");
    let transported = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let list = arena.value_type_list(boolean.ty);
        let constant = arena.value_constant(declared.position());
        let path = arena.value_univalence(constant);
        let nil = arena.value_list_nil();
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let motive = arena.value_type_element(bound, gandr_kernel_strata::Level::zero());
        let transport = arena.computation_path_transport(motive, path, nil);
        (list, arena.value_returned(transport))
    });
    assert!(
        transported.is_ok(),
        "`ua` of an admitted record synthesises its identity under a transport: {transported:?}"
    );

    // Negation with the identity as its left inverse: the section `g(to(x))
    // = x` reads `not(x)` against `x`, refused where the record is checked.
    let refused = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let map = identity_map(arena);
        let equivalence = record(arena, [boolean.not, map, boolean.not]);
        (
            identity_at(arena, boolean.ty),
            arena.value_univalence(equivalence),
        )
    });
    assert!(
        matches!(refused, Err(KernelError::Identity(_))),
        "a law that does not hold is a field that does not check: {refused:?}"
    );

    // Off the level-zero universe the identity is no `ua` reading, and a type
    // that is no record of a map reads no codes.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let at_boolean = arena.value_type_path(boolean.ty, boolean.truth, boolean.truth);
    assert_eq!(
        super::identity_codes(&arena, at_boolean),
        Err(PathError::ExpectedPath(at_boolean))
    );
    assert_eq!(
        super::univalence_record(&mut arena, at_boolean),
        Err(PathError::ExpectedPath(at_boolean))
    );
    assert_eq!(
        super::univalence_reading(&mut arena, boolean.ty),
        Err(PathError::ExpectedEquivalence(boolean.ty))
    );
}

/// #1064: an element transport follows a native path written in place, whose
/// type is `Path_U(a, b)`, as it follows one declared at `Path(U₀, a, b)`: the
/// two are readings of one classifier at the level-zero value universe. The
/// transport read the written path's type as an identity and refused it by
/// shape.
#[test]
fn an_element_transport_follows_a_native_path_written_in_place_1064()
{
    let mut environment = Environment::new();
    let transported = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let path = equivalence(arena, boolean, boolean.not, boolean.not);
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(bound, gandr_kernel_strata::Level::zero());
        let motive = arena.value_type_list(element);
        let nil = arena.value_list_nil();
        let truth = arena.value_list_cons(boolean.truth, nil);
        let transport = arena.computation_path_transport(motive, path, truth);
        let list = arena.value_type_list(boolean.ty);
        (list, arena.value_returned(transport))
    });
    assert!(
        transported.is_ok(),
        "a list moves along negation written in place: {transported:?}"
    );
}
