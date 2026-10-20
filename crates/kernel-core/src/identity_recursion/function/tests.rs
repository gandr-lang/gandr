//! Function-relation witnesses with an independent core-nbe producer.

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
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Application;
use super::Component;
use super::Evaluation;
use super::EvaluationSide;
use super::HigherEvaluation;
use super::Mode;
use super::Pointwise;
use super::RelatedArguments;
use super::Relation;
use super::RelationError;
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::identity_recursion::Domain;
use crate::identity_recursion::Fiber;
use crate::identity_recursion::Transport;
use crate::identity_recursion::interpret;
use crate::path_universe::Dialogue;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;

/// Bool terms and three independently written CBPV functions.
pub struct Boolean
{
    /// The sum of units.
    pub ty: ValueTypeId,
    /// Bool-to-Bool thunk type.
    pub function: ValueTypeId,
    /// Quoted thunk code.
    pub code: ValueId,
    /// Left injection.
    pub truth: ValueId,
    /// Right injection.
    pub falsity: ValueId,
    /// Case-switching function.
    pub not: ValueId,
    /// Return its bound argument.
    pub identity: ValueId,
    /// Two sequenced applications of negation.
    pub double: ValueId,
}

/// Construct Bool and actual thunk/force/bind syntax.
///
/// # Specification
/// trivial.
pub fn boolean(arena: &mut TermArena) -> Boolean
{
    let unit_type = arena.value_type_unit();
    let ty = arena.value_type_sum(&[unit_type, unit_type]);
    let returner = arena.comp_type_returner(ty);
    let arrow = arena.comp_type_arrow(ty, returner);
    let function = arena.value_type_thunk(arrow);
    let code = arena.value_quote(function);
    let unit = arena.value_unit();
    let truth = arena.value_injection(Side::Left.into(), unit);
    let falsity = arena.value_injection(Side::Right.into(), unit);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let left = arena.value_injection(Side::Right.into(), variable);
    let right = arena.value_injection(Side::Left.into(), variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let body = arena.computation_case(variable, &[left, right]);
    let lambda = arena.computation_lambda(body);
    let not = arena.value_thunk(lambda);
    let body = arena.computation_return(variable);
    let lambda = arena.computation_lambda(body);
    let identity = arena.value_thunk(lambda);
    // Case-inline the two negations, retaining the first return/bind seam.
    // The annotation-free checker cannot infer a lambda at an application head.
    let payload = arena.computation_return(variable);
    let left = arena.value_injection(Side::Left.into(), variable);
    let right = arena.value_injection(Side::Right.into(), variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let left = arena.computation_bind(payload, left);
    let right = arena.computation_bind(payload, right);
    let body = arena.computation_case(variable, &[left, right]);
    let lambda = arena.computation_lambda(body);
    let double = arena.value_thunk(lambda);
    Boolean {
        ty,
        function,
        code,
        truth,
        falsity,
        not,
        identity,
        double,
    }
}

/// Write a force/application independently of the relation interpreter.
///
/// # Specification
/// trivial.
fn application(
    arena: &mut TermArena,
    function: ValueId,
    argument: ValueId,
) -> ComputationId
{
    let force = arena.computation_force(function);
    arena.computation_application(force, argument)
}

/// Interpret a quoted code for the fixture.
///
/// # Specification
/// trivial.
fn relation(
    arena: &TermArena,
    mode: Mode,
    code: ValueId,
) -> Relation
{
    interpret(
        arena,
        crate::identity_recursion::Interfaces::NONE,
        mode,
        Domain::Elements(code),
    )
    .expect("code")
    .elements()
    .expect("elements")
}

/// The term graph's children, without reduction or relation interpretation.
///
/// # Specification
/// - requires: the root belongs to the supported CBPV fixture fragment.
/// - ensures: direct children retain their order and no child is reduced.
/// - provides: the independent producer's term traversal.
/// - fails: never.
/// - panics: on unsupported or unreadable fixture terms.
///
/// # Adequacy
/// - hypothesis: L3 — swapped Boolean components produce distinct evaluation
///   claims.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
#[spec(ensures: |ret| ret.len() == match node { AnyNode::Value(id) => arena.value(id).map_or(0, |value| match *value { Value::PathEquiv { .. } => 3, Value::Tuple(ref components) => components.len(), Value::StaticApplication(..) | Value::PathProduct(..) => 2, Value::Injection(..) | Value::Lift { .. } | Value::Thunk(_) | Value::Quote(_) | Value::QuoteComputation(_) | Value::PathRefl(_) => 1, Value::Constructor { .. } | Value::Record(_) | Value::SessionPath { .. } | Value::Univalence { .. } | Value::SessionFlow { .. } | Value::Stay { .. } | Value::ForwardFlow { .. } | Value::FunctionFlow { .. } | Value::Then { .. } | Value::FlowProduct(..) | Value::Here { .. } | Value::Returned(_) | Value::Higher { .. } | Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. } | Value::Variable(_) | Value::Constant(_) | Value::Literal(_) | Value::ListNil | Value::ListCons(..) => 0 }), AnyNode::Computation(id) => arena.computation(id).map_or(0, |computation| match *computation { Computation::Case { ref branches, .. } => branches.len().saturating_add(1), Computation::Application(..) | Computation::Bind(..) | Computation::Transport(..) => 2, Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Lambda(_) | Computation::Return(_) | Computation::Force(_) | Computation::SigmaSplit { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::PathTransport { .. } | Computation::TelescopeTransport { .. } | Computation::Ride { .. } | Computation::TelescopeRide { .. } | Computation::RelatedApplication { .. } | Computation::With(..) | Computation::Project(..) | Computation::Fixpoint { .. } => 1 }), AnyNode::ValueType(_) | AnyNode::CompType(_) => 0 })]
fn children(
    arena: &TermArena,
    node: AnyNode,
) -> Vec<AnyNode>
{
    match node {
        AnyNode::Value(id) => match arena.value(id).expect("value") {
            &Value::Tuple(ref components) => {
                components.iter().copied().map(AnyNode::Value).collect()
            },
            &Value::Injection(_, value) => vec![AnyNode::Value(value)],
            &Value::Thunk(body) => vec![AnyNode::Computation(body)],
            &Value::Variable(_) => Vec::new(),
            &Value::Constructor { .. }
            | &Value::Record(_)
            | &Value::SessionPath { .. }
            | &Value::SessionFlow { .. }
            | &Value::Stay { .. }
            | &Value::ForwardFlow { .. }
            | &Value::FunctionFlow { .. }
            | &Value::Then { .. }
            | &Value::FlowProduct(..)
            | &Value::PathRefl(_)
            | &Value::PathProduct(..)
            | &Value::PathEquiv { .. }
            | &Value::Univalence { .. }
            | &Value::Here { .. }
            | &Value::Returned(_)
            | &Value::Higher { .. }
            | &Value::HigherEvaluation { .. }
            | &Value::QuantifiedEvaluation { .. }
            | &Value::Constant(_)
            | &Value::Literal(_)
            | &Value::ListNil
            | &Value::ListCons(..)
            | &Value::Lift { .. }
            | &Value::Quote(_)
            | &Value::QuoteComputation(_)
            | &Value::StaticApplication(..) => panic!("outside producer fixture"),
        },
        AnyNode::Computation(id) => match *arena.computation(id).expect("computation") {
            Computation::Lambda(body) => vec![AnyNode::Computation(body)],
            Computation::Application(head, value) => {
                vec![AnyNode::Computation(head), AnyNode::Value(value)]
            },
            Computation::Return(value) | Computation::Force(value) => vec![AnyNode::Value(value)],
            Computation::Bind(a, b) => vec![AnyNode::Computation(a), AnyNode::Computation(b)],
            Computation::Case {
                scrutinee,
                ref branches,
            } => core::iter::once(AnyNode::Value(scrutinee))
                .chain(branches.iter().copied().map(AnyNode::Computation))
                .collect(),
            Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeRide { .. }
            | Computation::RelatedApplication { .. } => panic!("no native transport in fixtures"),
            Computation::DataCase { .. }
            | Computation::SigmaSplit { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..) => {
                panic!("no nominal or record eliminator in this fixture")
            },
            Computation::Fixpoint { .. } => panic!("no fixpoint in this fixture"),
            Computation::With(..) | Computation::Project(..) => {
                panic!("no lazy product in this fixture")
            },
            Computation::ListFold { .. } | Computation::ListCase { .. } => {
                panic!("eliminator outside fixture fragment")
            },
        },
        AnyNode::ValueType(_) | AnyNode::CompType(_) => panic!("no type nodes"),
    }
}

/// Translate both sides into core-nbe's separate syntax arena.
///
/// # Specification
/// - ensures: preserves binders and constructor order without reducing terms.
/// - panics: on unsupported or malformed fixture syntax.
///
/// # Adequacy
/// - hypothesis: L1/L3 — swapped Bool outputs give distinct producer verdicts.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
#[spec(ensures: |ret| ret.0.value(ret.1).is_some() && ret.0.value(ret.2).is_some() && (left != right || ret.1 == ret.2))]
fn translate(
    arena: &TermArena,
    left: ValueId,
    right: ValueId,
) -> (
    CoreArena,
    gandr_core_term::ValueId,
    gandr_core_term::ValueId,
)
{
    let mut core = CoreArena::new();
    let mut values = BTreeMap::new();
    let mut computations = BTreeMap::new();
    let mut pending = vec![
        (AnyNode::Value(right), false),
        (AnyNode::Value(left), false),
    ];
    // One buffer per operand kind, refilled for each tuple and case.
    let (mut operands, mut branch_ids) = (Vec::new(), Vec::new());
    while let Some((node, expanded)) = pending.pop() {
        if !expanded {
            let known = match node {
                AnyNode::Value(id) => values.contains_key(&id),
                AnyNode::Computation(id) => computations.contains_key(&id),
                AnyNode::ValueType(_) | AnyNode::CompType(_) => false,
            };
            if known {
                continue;
            }
            pending.push((node, true));
            for child in children(arena, node).into_iter().rev() {
                pending.push((child, false));
            }
            continue;
        }
        match node {
            AnyNode::Value(id) => {
                let value = match *arena.value(id).expect("value") {
                    Value::Variable(index) => core.value_variable(Zone::Intuitionistic, index),
                    Value::Tuple(ref components) => {
                        operands.clear();
                        operands.extend(components.iter().map(|component| values[component]));
                        core.value_tuple(&operands)
                    },
                    Value::Injection(summand, value) => {
                        core.value_injection(summand, values[&value])
                    },
                    Value::Thunk(body) => core.value_thunk(computations[&body]),
                    Value::Constructor { .. }
                    | Value::Record(_)
                    | Value::SessionPath { .. }
                    | Value::SessionFlow { .. }
                    | Value::Stay { .. }
                    | Value::ForwardFlow { .. }
                    | Value::FunctionFlow { .. }
                    | Value::Then { .. }
                    | Value::FlowProduct(..)
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Univalence { .. }
                    | Value::Here { .. }
                    | Value::Returned(_)
                    | Value::Higher { .. }
                    | Value::HigherEvaluation { .. }
                    | Value::QuantifiedEvaluation { .. }
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticApplication(..) => panic!("unsupported value"),
                };
                values.insert(id, value);
            },
            AnyNode::Computation(id) => {
                let computation = match *arena.computation(id).expect("computation") {
                    Computation::Return(value) => core.computation_return(values[&value]),
                    Computation::Force(value) => core.computation_force(values[&value]),
                    Computation::Lambda(body) => core.computation_lambda(computations[&body]),
                    Computation::Application(head, value) => {
                        core.computation_application(computations[&head], values[&value])
                    },
                    Computation::Bind(a, b) => {
                        core.computation_bind(computations[&a], computations[&b])
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        branch_ids.clear();
                        branch_ids.extend(branches.iter().map(|branch| computations[branch]));
                        core.computation_case(values[&scrutinee], &branch_ids)
                    },
                    Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Ride { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. } => {
                        panic!("no native transport in fixtures")
                    },
                    Computation::DataCase { .. }
                    | Computation::SigmaSplit { .. }
                    | Computation::RecordProjection(..)
                    | Computation::TupleProjection(..) => {
                        panic!("no nominal or record eliminator in this fixture")
                    },
                    Computation::Fixpoint { .. } => panic!("no fixpoint in this fixture"),
                    Computation::With(..) | Computation::Project(..) => {
                        panic!("no lazy product in this fixture")
                    },
                    Computation::ListFold { .. } | Computation::ListCase { .. } => {
                        panic!("unsupported computation")
                    },
                };
                computations.insert(id, computation);
            },
            AnyNode::ValueType(_) | AnyNode::CompType(_) => panic!("unsupported node"),
        }
    }
    (core, values[&left], values[&right])
}

/// Forget engine-local addresses without changing any trace decisions.
///
/// # Specification
/// trivial.
fn decision(step: ConversionDecision<TraceNode>) -> ConversionDecision<ReplayNode>
{
    step.map(|node| match node {
        TraceNode::Constant(_) => panic!("fixtures contain no constants"),
        TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
    })
}

/// Obtain the real engine's verdict and complete trace on a returned-value
/// claim.
///
/// # Specification
/// - ensures: core-nbe evaluates both sides and searches conversion; no kernel
///   result or hand-authored successful trace enters the producer. The returned
///   dialogue erases all syntax-arena anchors.
/// - panics: on malformed fixture translation or an operational engine error.
///
/// # Adequacy
/// - hypothesis: L1/L3 — false evaluation claims produce traces the kernel
///   refuses.
/// - witness: `identity_recursion::function::tests::lambda_reflexivity_replays_higher_evaluation`
#[spec(ensures: |ret| ret.1.0.iter().all(|step| match *step {
    ConversionDecision::ReduceLeft { redex } | ConversionDecision::ReduceRight { redex } => redex == ReplayNode::Other,
    ConversionDecision::ConstShortcut { constant } | ConversionDecision::Unfold { constant } | ConversionDecision::Postpone { constant } | ConversionDecision::Freeze { constant, .. } => constant == ReplayNode::Other,
    ConversionDecision::EtaExpand { variable, .. } => variable == ReplayNode::Other,
    ConversionDecision::Force { thunk } => thunk == ReplayNode::Other,
    ConversionDecision::ComparedShared { left, right } => left == ReplayNode::Other && right == ReplayNode::Other,
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } | ConversionDecision::ReturnEta { .. } | ConversionDecision::Reassociate { .. } => true,
}))]
fn engine(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    computation: ComputationId,
    value: ValueId,
) -> (MachineVerdict, Dialogue)
{
    let mut returned = arena.computation_return(value);
    for _ in context {
        returned = arena.computation_lambda(returned);
    }
    let returned = arena.value_thunk(returned);
    reaches(arena, context, computation, returned)
}

/// Obtain the real engine's verdict and complete trace on a claim that a
/// computation, closed over its telescope, converts to a closed value.
///
/// # Specification
/// - ensures: as [`engine`], against the closed `target` rather than a returned
///   value.
/// - panics: on malformed fixture translation or an operational engine error.
///
/// # Adequacy
/// - hypothesis: L1/L3 — a stuck normal form's trace replays, and the trace of
///   another form refuses.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
#[spec(ensures: |ret| ret.0 != MachineVerdict::Convertible || arena.value(target).is_some())]
pub fn reaches(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    mut computation: ComputationId,
    target: ValueId,
) -> (MachineVerdict, Dialogue)
{
    for _ in context {
        computation = arena.computation_lambda(computation);
    }
    let left = arena.value_thunk(computation);
    let (core, left, right) = translate(arena, left, target);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let left =
        gandr_core_nbe::eval_value(&core, &mut domain, definitions, Fuel::from(4096_u32), left)
            .expect("left evaluation");
    let right =
        gandr_core_nbe::eval_value(&core, &mut domain, definitions, Fuel::from(4096_u32), right)
            .expect("right evaluation");
    let mut log = TraceLog::new();
    let report = gandr_core_nbe::decide::<_, ResharingMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::values(left, right),
        &mut log,
    )
    .expect("engine");
    (
        report.verdict(),
        Dialogue(log.decisions().copied().map(decision).collect()),
    )
}

/// A return step's claimed evaluation of `computation`, traced by the engine.
///
/// # Specification
/// - requires: `computation` returns `value` beneath `context`.
/// - ensures: the value with the engine's dialogue.
/// - panics: when the engine does not convert the claim.
///
/// # Adequacy
/// - hypothesis: L1/L3 — each return of the quantified witness replays its
///   evaluation, and a wrong returned value refuses.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
#[spec(ensures: |ret| ret.value == value)]
pub fn evaluation(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    computation: ComputationId,
    value: ValueId,
) -> Evaluation
{
    let (verdict, dialogue) = engine(arena, context, computation, value);
    assert_eq!(verdict, MachineVerdict::Convertible);
    Evaluation { value, dialogue }
}

/// An application step's claimed normal form of `computation`, traced by
/// the engine.
///
/// # Specification
/// - requires: `computation`, closed over `context`, converts to `normal`.
/// - ensures: the normal form with the engine's dialogue.
/// - panics: when the engine does not convert the claim.
///
/// # Adequacy
/// - hypothesis: L1/L3 — each application of the quantified witness replays its
///   normal form, and a form applying the other function refuses.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
/// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
#[spec(ensures: |ret| ret.normal == normal)]
pub fn normal_form(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    computation: ComputationId,
    normal: ValueId,
) -> super::NormalForm
{
    let (verdict, dialogue) = reaches(arena, context, computation, normal);
    assert_eq!(verdict, MachineVerdict::Convertible);
    super::NormalForm { normal, dialogue }
}

/// Produce both application traces for one independent pointwise argument.
///
/// # Specification
/// - requires: the function applications are convertible to the proposed
///   outputs.
/// - ensures: preserves left/right output order and the supplied relation
///   proof.
/// - provides: independently generated dialogues for both applications.
/// - fails: never.
/// - panics: if either engine claim disagrees with its proposed output.
///
/// # Adequacy
/// - hypothesis: L3 — Boolean components distinguish negation from identity.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
#[spec(ensures: |ret| matches!(&ret, Pointwise::Return { left, right, proof: returned } if left.value == outputs.0 && right.value == outputs.1 && *returned == proof))]
pub fn pointwise(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    functions: (ValueId, ValueId),
    arguments: (ValueId, ValueId),
    outputs: (ValueId, ValueId),
    proof: ValueId,
) -> Pointwise
{
    let mut evaluations = Vec::new();
    for (function, argument, value) in [
        (functions.0, arguments.0, outputs.0),
        (functions.1, arguments.1, outputs.1),
    ] {
        let applied = application(arena, function, argument);
        let (verdict, dialogue) = engine(arena, context, applied, value);
        assert_eq!(verdict, MachineVerdict::Convertible);
        evaluations.push(Evaluation { value, dialogue });
    }
    let right = evaluations.pop().expect("right");
    let left = evaluations.pop().expect("left");
    Pointwise::Return { left, right, proof }
}

/// Bool's complete two-constructor higher-evaluation introduction.
///
/// # Specification
/// - requires: closed Boolean functions with the stated outputs on both
///   constructors.
/// - ensures: one component per constructor, truth before falsity, with both
///   proposed output values retained in their own direction.
/// - provides: exhaustive Boolean coverage without inspecting a kernel verdict.
/// - fails: never.
/// - panics: when an independently evaluated component disagrees.
///
/// # Adequacy
/// - hypothesis: L3 — omitted, extra and wrong components refuse consumption.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
#[spec(ensures: |ret| ret.0.len() == outputs.len() && ret.0.iter().zip(outputs).all(|(component, output)| matches!(component, Pointwise::Return { left, right, .. } if left.value == output.0 && right.value == output.1)))]
pub fn higher(
    arena: &mut TermArena,
    boolean: &Boolean,
    functions: (ValueId, ValueId),
    outputs: [(ValueId, ValueId); 2],
) -> HigherEvaluation
{
    let proof = arena.value_unit();
    HigherEvaluation(
        [boolean.truth, boolean.falsity]
            .into_iter()
            .zip(outputs)
            .map(|(input, output)| pointwise(arena, &[], functions, (input, input), output, proof))
            .collect(),
    )
}

#[test]
fn function_clause_retains_related_inputs_and_neutrals()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit = arena.value_unit();
    let x = arena.value_variable(DeBruijnIndex::from(1_u32));
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    for mode in [Mode::Identity, Mode::Bridge] {
        let family = relation(&arena, mode, boolean.code);
        let fiber = family
            .fiber(&mut arena, &[boolean.function, boolean.function], x, y)
            .expect("neutral functions");
        assert!(
            matches!(fiber.get(fiber.root()), Ok(Fiber::Function { argument, result, .. }) if argument == boolean.ty && result == boolean.ty)
        );
        // The function fibre is the persisted identity in identity mode and
        // the persisted bridge in bridge mode, at the thunk type either way.
        let lowered = fiber.native(&mut arena);
        let parts = match lowered.ok().and_then(|ty| arena.value_type(ty)) {
            Some(&ValueType::Path {
                domain,
                left,
                right,
            }) if mode == Mode::Identity => Some((domain, left, right)),
            Some(&ValueType::Bridge {
                domain,
                left,
                right,
            }) if mode == Mode::Bridge => Some((domain, left, right)),
            _ => None,
        };
        assert_eq!(parts, Some((boolean.function, x, y)));
        let arguments = RelatedArguments {
            left: boolean.truth,
            right: boolean.truth,
            proof: unit,
        };
        let applied = family
            .apply_related(
                &mut arena,
                &[boolean.function, boolean.function],
                (x, y),
                arguments,
                &Pointwise::Suspended,
                ReplayBudget::DEFAULT,
            )
            .expect("suspended application");
        assert!(
            matches!(applied, Application::Suspended { result, mode: found, .. } if result == boolean.ty && found == mode)
        );
        let unrelated = RelatedArguments {
            right: boolean.falsity,
            ..arguments
        };
        assert!(matches!(
            family.apply_related(
                &mut arena,
                &[],
                (boolean.identity, boolean.identity),
                unrelated,
                &Pointwise::Suspended,
                ReplayBudget::DEFAULT
            ),
            Err(RelationError::Typing(_))
        ));
        let unit_type = arena.value_type_unit();
        let returned = arena.comp_type_returner(boolean.ty);
        let arrow = arena.comp_type_arrow(boolean.ty, returned);
        let outer = arena.comp_type_arrow(unit_type, arrow);
        let outer = arena.value_type_thunk(outer);
        let stuck = application(&mut arena, y, unit);
        let stuck = arena.value_thunk(stuck);
        let fiber = family
            .fiber(&mut arena, &[outer], stuck, stuck)
            .expect("stuck function");
        assert!(matches!(
            fiber.get(fiber.root()),
            Ok(Fiber::Function { .. })
        ));

        let returned = arena.comp_type_returner(unit_type);
        let arrow = arena.comp_type_arrow(unit_type, returned);
        let thunk = arena.value_type_thunk(arrow);
        let code = arena.value_quote(thunk);
        let units = relation(&arena, mode, code);
        let args = RelatedArguments {
            left: x,
            right: y,
            proof: unit,
        };
        let evidence = pointwise(
            &mut arena,
            &[unit_type, unit_type],
            (boolean.identity, boolean.identity),
            (x, y),
            (x, y),
            unit,
        );
        let applied = units
            .apply_related(
                &mut arena,
                &[unit_type, unit_type],
                (boolean.identity, boolean.identity),
                args,
                &evidence,
                ReplayBudget::DEFAULT,
            )
            .expect("distinct related Unit arguments");
        assert!(
            matches!(applied, Application::Return { left, right, ref fiber } if left == x && right == y && fiber.get(fiber.root()).expect("fibre") == Fiber::Unit)
        );
    }
}

#[test]
fn lambda_reflexivity_replays_higher_evaluation()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let family = relation(&arena, Mode::Identity, boolean.code);
    let evidence = higher(&mut arena, &boolean, (boolean.not, boolean.not), [
        (boolean.falsity, boolean.falsity),
        (boolean.truth, boolean.truth),
    ]);
    let identity = family
        .function_reflexivity(&mut arena, boolean.not, evidence, ReplayBudget::DEFAULT)
        .expect("replayed lambda refl");
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    assert_eq!(
        family
            .transport(&mut arena, &[], &identity, unit_type, unit)
            .expect("refl transport"),
        Transport::Return(unit)
    );
    // Reflexivity at a function is its `here`, checked by conversion; the
    // λ's action is the higher evaluation above.
    let reflexive = family
        .reflexivity(&mut arena, &[], boolean.not)
        .expect("function reflexivity");
    assert!(matches!(
        reflexive.native_evidence().map(|proof| arena.value(proof)),
        Ok(Some(&Value::Here { point, .. })) if point == boolean.not
    ));
    assert_eq!(
        family
            .transport(&mut arena, &[], &reflexive, unit_type, unit)
            .expect("here transport"),
        Transport::Return(unit)
    );
    // The diagonal of the function fibre is `here` at one function, and two
    // distinct functions owe a higher evaluation instead.
    let at_one = family
        .evaluate(&arena, boolean.not, boolean.not)
        .expect("one function's fibre");
    assert!(matches!(
        at_one.diagonal(&mut arena).map(|diagonal| arena.value(diagonal.value)),
        Ok(Some(&Value::Here { point, .. })) if point == boolean.not
    ));
    let at_two = family
        .evaluate(&arena, boolean.not, boolean.identity)
        .expect("two functions' fibre");
    assert!(matches!(
        at_two.diagonal(&mut arena),
        Err(RelationError::HigherEvaluationRequired)
    ));
    assert!(matches!(
        identity.native_evidence(),
        Err(RelationError::HigherEvaluationRequired)
    ));
    let mut forged = higher(&mut arena, &boolean, (boolean.not, boolean.not), [
        (boolean.falsity, boolean.falsity),
        (boolean.truth, boolean.truth),
    ]);
    let Pointwise::Return { ref mut left, .. } = forged.0[0]
    else {
        panic!("return")
    };
    left.value = boolean.truth;
    assert!(matches!(
        family.function_reflexivity(&mut arena, boolean.not, forged, ReplayBudget::DEFAULT),
        Err(RelationError::Evaluation(
            Component(0),
            EvaluationSide::Left,
            _
        ))
    ));
}

#[test]
fn funext_computes_and_refuses_wrong_components()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    // Check the case-inlined fixture against actual two-application composition.
    for argument in [boolean.truth, boolean.falsity] {
        let first = application(&mut arena, boolean.not, argument);
        let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
        let second = application(&mut arena, boolean.not, variable);
        let raw_composite = arena.computation_bind(first, second);
        let (verdict, _) = engine(&mut arena, &[], raw_composite, argument);
        assert_eq!(verdict, MachineVerdict::Convertible);
    }
    let evidence = higher(&mut arena, &boolean, (boolean.double, boolean.identity), [
        (boolean.truth, boolean.truth),
        (boolean.falsity, boolean.falsity),
    ]);
    for mode in [Mode::Identity, Mode::Bridge] {
        let family = relation(&arena, mode, boolean.code);
        let mark = arena.watermark();
        family
            .check_higher(
                &mut arena,
                (boolean.double, boolean.identity),
                &evidence,
                ReplayBudget::DEFAULT,
            )
            .expect("all components");
        assert_eq!(arena.watermark(), mark);
        let wrong = higher(&mut arena, &boolean, (boolean.not, boolean.identity), [
            (boolean.falsity, boolean.truth),
            (boolean.truth, boolean.falsity),
        ]);
        assert!(matches!(
            family.check_higher(
                &mut arena,
                (boolean.not, boolean.identity),
                &wrong,
                ReplayBudget::DEFAULT
            ),
            Err(RelationError::Pointwise(Component(0), _))
        ));
        for components in [vec![evidence.0[0].clone()], vec![
            evidence.0[0].clone(),
            evidence.0[1].clone(),
            evidence.0[1].clone(),
        ]] {
            assert!(matches!(
                family.check_higher(
                    &mut arena,
                    (boolean.double, boolean.identity),
                    &HigherEvaluation(components),
                    ReplayBudget::DEFAULT
                ),
                Err(RelationError::Coverage)
            ));
        }
        assert!(matches!(
            family.check_higher(
                &mut arena,
                (boolean.double, boolean.identity),
                &evidence,
                ReplayBudget::from(0_u64)
            ),
            Err(RelationError::Budget)
        ));
        let mut swapped = evidence.clone();
        swapped.0.swap(0, 1);
        assert!(matches!(
            family.check_higher(
                &mut arena,
                (boolean.double, boolean.identity),
                &swapped,
                ReplayBudget::DEFAULT
            ),
            Err(RelationError::Evaluation(
                Component(0),
                EvaluationSide::Left,
                _
            ))
        ));
        let mut forged = evidence.clone();
        let Pointwise::Return { ref mut right, .. } = forged.0[1]
        else {
            panic!("return")
        };
        right.value = boolean.truth;
        assert!(matches!(
            family.check_higher(
                &mut arena,
                (boolean.double, boolean.identity),
                &forged,
                ReplayBudget::DEFAULT
            ),
            Err(RelationError::Evaluation(
                Component(1),
                EvaluationSide::Right,
                _
            ))
        ));
        if mode == Mode::Bridge {
            assert!(matches!(
                family.funext(
                    &mut arena,
                    boolean.double,
                    boolean.identity,
                    evidence.clone(),
                    ReplayBudget::DEFAULT
                ),
                Err(RelationError::NonFibrant)
            ));
        }
    }
    let family = relation(&arena, Mode::Identity, boolean.code);
    let identity = family
        .funext(
            &mut arena,
            boolean.double,
            boolean.identity,
            evidence,
            ReplayBudget::DEFAULT,
        )
        .expect("computed funext");
    assert_eq!(
        equal_values(&arena, boolean.double, boolean.identity),
        Convertibility::Distinct
    );
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    assert!(matches!(
        family.transport(&mut arena, &[], &identity, unit_type, unit),
        Ok(Transport::Neutral { .. })
    ));
}

#[test]
fn application_transport_computes()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let family = relation(&arena, Mode::Identity, boolean.code);
    let evidence = higher(&mut arena, &boolean, (boolean.double, boolean.identity), [
        (boolean.truth, boolean.truth),
        (boolean.falsity, boolean.falsity),
    ]);
    let identity = family
        .funext(
            &mut arena,
            boolean.double,
            boolean.identity,
            evidence,
            ReplayBudget::DEFAULT,
        )
        .expect("function identity");
    let unit = arena.value_unit();
    for argument in [boolean.truth, boolean.falsity] {
        let evidence = pointwise(
            &mut arena,
            &[],
            (boolean.double, boolean.identity),
            (argument, argument),
            (argument, argument),
            unit,
        );
        let result = family
            .transport_application(
                &mut arena,
                &identity,
                argument,
                &evidence,
                ReplayBudget::DEFAULT,
            )
            .expect("application transport");
        assert!(
            matches!(result, Application::Return { right, ref fiber, .. } if right == argument && fiber.get(fiber.root()).expect("output relation") == Fiber::Unit)
        );
        assert!(
            matches!(family.transport_application(&mut arena, &identity, argument, &Pointwise::Suspended, ReplayBudget::DEFAULT), Ok(Application::Suspended { result, .. }) if result == boolean.ty)
        );
    }
}

#[test]
fn symbolic_coverage_keeps_base_variables_independent()
{
    let mut arena = TermArena::new();
    let base = arena.value_type_base(BaseType::String);
    let pair = arena.value_type_product(&[base, base]);
    let returned = arena.comp_type_returner(pair);
    let arrow = arena.comp_type_arrow(pair, returned);
    let thunk = arena.value_type_thunk(arrow);
    let code = arena.value_quote(thunk);
    let family = relation(&arena, Mode::Identity, code);
    let patterns = family
        .related_patterns(&mut arena, ReplayBudget::DEFAULT)
        .expect("symbolic coverage");
    let [ref pattern] = *patterns.as_slice()
    else {
        panic!("one constructor shape")
    };
    assert_eq!(
        pattern.left, pattern.right,
        "a discrete premise is eliminated"
    );
    let &[left, right] = arena
        .value(pattern.left)
        .and_then(Value::components)
        .expect("tuple")
    else {
        panic!("pair")
    };
    assert_eq!(
        arena.value(left),
        Some(&Value::Variable(DeBruijnIndex::from(1_u32)))
    );
    assert_eq!(
        arena.value(right),
        Some(&Value::Variable(DeBruijnIndex::from(0_u32)))
    );
    assert_eq!(pattern.context, vec![base, base]);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let body = arena.computation_return(variable);
    let body = arena.computation_lambda(body);
    let identity = arena.value_thunk(body);
    let evidence = pointwise(
        &mut arena,
        &pattern.context,
        (identity, identity),
        (pattern.left, pattern.right),
        (pattern.left, pattern.right),
        pattern.proof,
    );
    family
        .function_reflexivity(
            &mut arena,
            identity,
            HigherEvaluation(vec![evidence]),
            ReplayBudget::DEFAULT,
        )
        .expect("generic Base refl");
}

/// The thunk type `U(T → F R)` of a function from `T` returning `R`.
///
/// # Specification
/// trivial.
pub fn thunk_type(
    arena: &mut TermArena,
    domain: ValueTypeId,
    result: ValueTypeId,
) -> ValueTypeId
{
    let returned = arena.comp_type_returner(result);
    let arrow = arena.comp_type_arrow(domain, returned);
    arena.value_type_thunk(arrow)
}

/// `λh. return (h, h)`, duplicating a function argument.
///
/// # Specification
/// trivial.
pub fn duplicate(arena: &mut TermArena) -> ValueId
{
    let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
    let both = arena.value_tuple(&[argument, argument]);
    let body = arena.computation_return(both);
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// `λh. force h truth`, applying a function argument.
///
/// # Specification
/// trivial.
pub fn apply_to(
    arena: &mut TermArena,
    argument: ValueId,
) -> ValueId
{
    let function = arena.value_variable(DeBruijnIndex::from(0_u32));
    let applied = application(arena, function, argument);
    let lambda = arena.computation_lambda(applied);
    arena.value_thunk(lambda)
}

#[test]
fn a_higher_order_argument_binds_its_inner_fibre()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let inner = boolean.function;
    let pair = arena.value_type_product(&[inner, inner]);
    let outer = thunk_type(&mut arena, inner, pair);
    let code = arena.value_quote(outer);
    let family = relation(&arena, Mode::Identity, code);

    // The generic related input is two functions and their identity, the
    // inner fibre: nothing is sampled and nothing is split.
    let patterns = family
        .related_patterns(&mut arena, ReplayBudget::DEFAULT)
        .expect("higher-order coverage");
    let [ref pattern] = *patterns.as_slice()
    else {
        panic!("one generic related input")
    };
    let &[first, second, premise] = pattern.context.as_slice()
    else {
        panic!("three binders")
    };
    assert_eq!((first, second), (inner, inner));
    let variable = |index: u32| Some(Value::Variable(DeBruijnIndex::from(index)));
    assert!(matches!(
        arena.value_type(premise),
        Some(&ValueType::Path { domain, left, right })
            if domain == inner
                && arena.value(left).cloned() == variable(1)
                && arena.value(right).cloned() == variable(0)
    ));
    assert_eq!(
        [pattern.left, pattern.right, pattern.proof].map(|value| arena.value(value).cloned()),
        [variable(2), variable(1), variable(0)]
    );
    // A bridge binds the same generic input, two functions and the bridge
    // between them: the family is over argument bridges, not argument paths.
    let bridge = relation(&arena, Mode::Bridge, code);
    let bridged = bridge
        .related_patterns(&mut arena, ReplayBudget::DEFAULT)
        .expect("bridge coverage binds the inner fibre");
    let [ref bridged] = *bridged.as_slice()
    else {
        panic!("one generic related input")
    };
    let &[bridged_first, bridged_second, bridged_premise] = bridged.context.as_slice()
    else {
        panic!("three binders")
    };
    assert_eq!((bridged_first, bridged_second), (inner, inner));
    assert!(matches!(
        arena.value_type(bridged_premise),
        Some(&ValueType::Bridge { domain, left, right })
            if domain == inner
                && arena.value(left).cloned() == variable(1)
                && arena.value(right).cloned() == variable(0)
    ));
    assert_eq!(
        [bridged.left, bridged.right, bridged.proof].map(|value| arena.value(value).cloned()),
        [variable(2), variable(1), variable(0)]
    );

    // Ap of a λ that duplicates its argument relates the two copies by the
    // premise, and the output evidence is checked: `here(f₀)` is not it.
    let duplicate = duplicate(&mut arena);
    let outputs = (
        arena.value_tuple(&[pattern.left, pattern.left]),
        arena.value_tuple(&[pattern.right, pattern.right]),
    );
    let inputs = (pattern.left, pattern.right);
    let proof = arena.value_tuple(&[pattern.proof, pattern.proof]);
    let evidence = pointwise(
        &mut arena,
        &pattern.context,
        (duplicate, duplicate),
        inputs,
        outputs,
        proof,
    );
    family
        .function_reflexivity(
            &mut arena,
            duplicate,
            HigherEvaluation(vec![evidence]),
            ReplayBudget::DEFAULT,
        )
        .expect("ap of a higher-order λ");
    let collapsed = arena.value_here(pattern.left);
    let collapsed = arena.value_tuple(&[pattern.proof, collapsed]);
    let forged = pointwise(
        &mut arena,
        &pattern.context,
        (duplicate, duplicate),
        inputs,
        outputs,
        collapsed,
    );
    assert!(matches!(
        family.function_reflexivity(
            &mut arena,
            duplicate,
            HigherEvaluation(vec![forged]),
            ReplayBudget::DEFAULT
        ),
        Err(RelationError::Pointwise(Component(0), _))
    ));

    // A λ that applies its argument is stuck at the generic pattern: it
    // returns no value there, so no claimed evaluation replays.
    let apply = apply_to(&mut arena, boolean.truth);
    let applying = thunk_type(&mut arena, inner, boolean.ty);
    let applying = arena.value_quote(applying);
    let applying = relation(&arena, Mode::Identity, applying);
    let claimed = Evaluation {
        value: boolean.truth,
        dialogue: Dialogue(Vec::new()),
    };
    let unit = arena.value_unit();
    assert!(matches!(
        applying.function_reflexivity(
            &mut arena,
            apply,
            HigherEvaluation(vec![Pointwise::Return {
                left: claimed.clone(),
                right: claimed,
                proof: unit,
            }]),
            ReplayBudget::DEFAULT
        ),
        Err(RelationError::Evaluation(
            Component(0),
            EvaluationSide::Left,
            _
        ))
    ));

    // At concrete related functions the same application computes: the
    // premise is the persisted identity at the inner fibre.
    let premise = arena.value_here(boolean.not);
    let evidence = pointwise(
        &mut arena,
        &[],
        (apply, apply),
        (boolean.not, boolean.not),
        (boolean.falsity, boolean.falsity),
        unit,
    );
    let applied = applying
        .apply_related(
            &mut arena,
            &[],
            (apply, apply),
            RelatedArguments {
                left: boolean.not,
                right: boolean.not,
                proof: premise,
            },
            &evidence,
            ReplayBudget::DEFAULT,
        )
        .expect("a higher-order argument computes");
    assert!(
        matches!(applied, Application::Return { left, right, ref fiber } if left == boolean.falsity && right == boolean.falsity && matches!(fiber.get(fiber.root()), Ok(Fiber::Unit)))
    );
    let unrelated = arena.value_here(boolean.identity);
    assert!(matches!(
        applying.apply_related(
            &mut arena,
            &[],
            (apply, apply),
            RelatedArguments {
                left: boolean.not,
                right: boolean.not,
                proof: unrelated,
            },
            &evidence,
            ReplayBudget::DEFAULT
        ),
        Err(RelationError::Typing(_))
    ));
}

#[test]
fn coverage_keeps_a_function_coordinate_s_two_sides_apart()
{
    // A function coordinate relates two functions, so the pattern beside or
    // around it relates two different values; neither a sum nor a product
    // may collapse them to the source.
    let mut arena = TermArena::new();
    let inner = boolean(&mut arena).function;
    let unit = arena.value_type_unit();
    let variable = |index: u32| Some(Value::Variable(DeBruijnIndex::from(index)));
    let sum = arena.value_type_sum(&[inner, unit]);
    let product = arena.value_type_product(&[inner, unit]);
    for (domain, what) in [(sum, "a sum"), (product, "a product")] {
        let outer = thunk_type(&mut arena, domain, unit);
        let code = arena.value_quote(outer);
        let patterns = relation(&arena, Mode::Identity, code)
            .related_patterns(&mut arena, ReplayBudget::DEFAULT)
            .expect("first-order coverage");
        let pattern = patterns.first().expect("a function pattern first");
        let sides = [pattern.left, pattern.right].map(|value| {
            let first = match arena.value(value) {
                Some(&Value::Injection(_, payload)) => payload,
                Some(&Value::Tuple(ref components)) => *components.first().expect("a pair"),
                _ => panic!("{what} wraps its coordinate"),
            };
            arena.value(first).cloned()
        });
        assert_eq!(
            sides,
            [variable(2), variable(1)],
            "{what} keeps the two functions"
        );
    }
}

#[test]
fn a_premise_relates_the_two_entries_just_before_it_in_order()
{
    let mut arena = TermArena::new();
    let inner = boolean(&mut arena).function;
    let [zero, one] = [0_u32, 1_u32].map(|index| arena.value_variable(DeBruijnIndex::from(index)));
    let premise = arena.value_type_path(inner, one, zero);
    let bridge = arena.value_type_bridge(inner, one, zero);
    let classify = |arena: &TermArena, mode, premise| {
        super::premise_classifier(
            arena,
            mode,
            &[inner, inner, premise],
            DeBruijnIndex::from(0_u32),
            Component(0),
        )
    };
    assert!(matches!(classify(&arena, Mode::Identity, premise), Ok(domain) if domain == inner));
    assert!(matches!(classify(&arena, Mode::Bridge, bridge), Ok(domain) if domain == inner));
    // Each reading's premise is its own former: a bridge relates no inputs of
    // an identity's step, nor a path those of a bridge's.
    for (mode, premise) in [(Mode::Identity, bridge), (Mode::Bridge, premise)] {
        assert!(matches!(
            classify(&arena, mode, premise),
            Err(RelationError::QuantifiedStep(Component(0)))
        ));
    }
    for (left, right) in [(one, one), (zero, zero), (zero, one)] {
        let premise = arena.value_type_path(inner, left, right);
        assert!(
            matches!(
                classify(&arena, Mode::Identity, premise),
                Err(RelationError::QuantifiedStep(Component(0)))
            ),
            "a premise binding its sides elsewhere is no premise"
        );
    }
}
