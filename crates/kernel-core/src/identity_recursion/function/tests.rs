//! Function-relation witnesses with an independent core-nbe producer.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

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
struct Boolean
{
    /// The sum of units.
    ty: ValueTypeId,
    /// Bool-to-Bool thunk type.
    function: ValueTypeId,
    /// Quoted thunk code.
    code: ValueId,
    /// Left injection.
    truth: ValueId,
    /// Right injection.
    falsity: ValueId,
    /// Case-switching function.
    not: ValueId,
    /// Return its bound argument.
    identity: ValueId,
    /// Two sequenced applications of negation.
    double: ValueId,
}

/// Construct Bool and actual thunk/force/bind syntax.
///
/// # Specification
/// trivial.
fn boolean(arena: &mut TermArena) -> Boolean
{
    let unit_type = arena.value_type_unit();
    let ty = arena.value_type_sum(unit_type, unit_type);
    let returner = arena.comp_type_returner(ty);
    let arrow = arena.comp_type_arrow(ty, returner);
    let function = arena.value_type_thunk(arrow);
    let code = arena.value_quote(function);
    let unit = arena.value_unit();
    let truth = arena.value_injection(Side::Left, unit);
    let falsity = arena.value_injection(Side::Right, unit);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let left = arena.value_injection(Side::Right, variable);
    let right = arena.value_injection(Side::Left, variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let body = arena.computation_case(variable, left, right);
    let lambda = arena.computation_lambda(body);
    let not = arena.value_thunk(lambda);
    let body = arena.computation_return(variable);
    let lambda = arena.computation_lambda(body);
    let identity = arena.value_thunk(lambda);
    // Case-inline the two negations, retaining the first return/bind seam.
    // The annotation-free checker cannot infer a lambda at an application head.
    let payload = arena.computation_return(variable);
    let left = arena.value_injection(Side::Left, variable);
    let right = arena.value_injection(Side::Right, variable);
    let left = arena.computation_return(left);
    let right = arena.computation_return(right);
    let left = arena.computation_bind(payload, left);
    let right = arena.computation_bind(payload, right);
    let body = arena.computation_case(variable, left, right);
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
    interpret(arena, mode, Domain::Elements(code))
        .expect("code")
        .elements()
        .expect("elements")
}

/// The term graph's children, without reduction or relation interpretation.
///
/// # Specification
/// trivial.
fn children(
    arena: &TermArena,
    node: AnyNode,
) -> Vec<AnyNode>
{
    match node {
        | AnyNode::Value(id) => match arena.value(id).expect("value") {
            | &Value::Pair(a, b) => vec![AnyNode::Value(a), AnyNode::Value(b)],
            | &Value::Injection(_, value) => vec![AnyNode::Value(value)],
            | &Value::Thunk(body) => vec![AnyNode::Computation(body)],
            | &Value::Unit | &Value::Variable(_) => Vec::new(),
            | _ => panic!("outside producer fixture"),
        },
        | AnyNode::Computation(id) => match *arena.computation(id).expect("computation") {
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
            | Computation::Transport(..) => panic!("no native transport in fixtures"),
            | Computation::Absurd(_) => panic!("no Empty eliminator in fixtures"),
        },
        | AnyNode::ValueType(_) | AnyNode::CompType(_) => panic!("no type nodes"),
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
    while let Some((node, expanded)) = pending.pop() {
        if !expanded {
            let known = match node {
                | AnyNode::Value(id) => values.contains_key(&id),
                | AnyNode::Computation(id) => computations.contains_key(&id),
                | _ => false,
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
            | AnyNode::Value(id) => {
                let value = match *arena.value(id).expect("value") {
                    | Value::Unit => core.value_unit(),
                    | Value::Variable(index) => core.value_variable(Zone::Intuitionistic, index),
                    | Value::Pair(a, b) => core.value_pair(values[&a], values[&b]),
                    | Value::Injection(side, value) => core.value_injection(side, values[&value]),
                    | Value::Thunk(body) => core.value_thunk(computations[&body]),
                    | _ => panic!("unsupported value"),
                };
                values.insert(id, value);
            },
            | AnyNode::Computation(id) => {
                let computation = match *arena.computation(id).expect("computation") {
                    | Computation::Return(value) => core.computation_return(values[&value]),
                    | Computation::Force(value) => core.computation_force(values[&value]),
                    | Computation::Lambda(body) => core.computation_lambda(computations[&body]),
                    | Computation::Application(head, value) => {
                        core.computation_application(computations[&head], values[&value])
                    },
                    | Computation::Bind(a, b) => {
                        core.computation_bind(computations[&a], computations[&b])
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
                    | Computation::Transport(..) => panic!("no native transport in fixtures"),
                    | Computation::Absurd(_) => panic!("unsupported computation"),
                };
                computations.insert(id, computation);
            },
            | _ => panic!("unsupported node"),
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
        | ConversionDecision::Freeze { .. } => panic!("fixtures contain no constants"),
    }
}

/// Obtain the real engine's verdict and complete trace on a returned-value
/// claim.
///
/// # Specification
/// - ensures: core-nbe evaluates both sides and searches conversion; no kernel
///   result or hand-authored successful trace enters the producer.
/// - panics: on malformed fixture translation or an operational engine error.
///
/// # Adequacy
/// - hypothesis: L1/L3 — false evaluation claims produce traces the kernel
///   refuses.
/// - witness: `identity_recursion::function::tests::lambda_reflexivity_replays_higher_evaluation`
fn engine(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    mut computation: ComputationId,
    value: ValueId,
) -> (MachineVerdict, Dialogue)
{
    let mut returned = arena.computation_return(value);
    for _ in context {
        computation = arena.computation_lambda(computation);
        returned = arena.computation_lambda(returned);
    }
    let left = arena.value_thunk(computation);
    let right = arena.value_thunk(returned);
    let (core, left, right) = translate(arena, left, right);
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

/// Produce both application traces for one independent pointwise argument.
///
/// # Specification
/// trivial.
fn pointwise(
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
/// trivial.
fn higher(
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
        assert!(matches!(
            fiber.native(&mut arena),
            Err(RelationError::NeutralFiber)
        ));
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
    assert!(matches!(
        family.reflexivity(&mut arena, &[], boolean.not),
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
    let pair = arena.value_type_product(base, base);
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
    let Value::Pair(left, right) = *arena.value(pattern.value).expect("pair")
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
        (pattern.value, pattern.value),
        (pattern.value, pattern.value),
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
    let arrow = arena.comp_type_arrow(thunk, returned);
    let outer = arena.value_type_thunk(arrow);
    let code = arena.value_quote(outer);
    let higher = relation(&arena, Mode::Identity, code);
    assert!(matches!(
        higher.related_patterns(&mut arena, ReplayBudget::DEFAULT),
        Err(RelationError::NeutralFiber)
    ));
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let fiber = higher
        .fiber(&mut arena, &[outer], variable, variable)
        .expect("higher-order fibre");
    assert!(
        matches!(fiber.get(fiber.root()), Ok(Fiber::Function { argument, result, .. }) if argument == thunk && result == pair)
    );
}
