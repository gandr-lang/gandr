//! The seven universe-path acceptance witnesses, using the untrusted `NbE`
//! engine.

#[path = "../higher_field/certificate_tests.rs"]
mod higher_field_tests;

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

use super::Dialogue;
use super::Direction;
use super::EliminatorName;
use super::Path;
use super::PathError;
use super::PathId;
use super::Paths;
use super::PatternPosition;
use super::Reduct;
use super::RoundTrips;
use super::Transport;
use super::beta;
use super::convert;
use super::elaborate;
use super::form;
use super::replay_transport;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;

/// Bool code, its two constructors and its closed negation translator.
struct Boolean
{
    /// The quoted sum of units.
    code: ValueId,
    /// The left injection.
    truth: ValueId,
    /// The right injection.
    falsity: ValueId,
    /// The negation thunk.
    not: ValueId,
}

/// Construct Bool and negation entirely as kernel terms.
///
/// # Specification
/// trivial.
fn boolean(arena: &mut TermArena) -> Boolean
{
    let unit_type = arena.value_type_unit();
    let boolean_type = arena.value_type_sum(unit_type, unit_type);
    let code = arena.value_quote(boolean_type);
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
    Boolean {
        code,
        truth,
        falsity,
        not: arena.value_thunk(lambda),
    }
}

/// Build a forced application without evaluating it.
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

/// Compose two closed translators in CBPV, returning a thunk.
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
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// Inline three negations, retaining both payload sequencing boundaries.
///
/// Case beta reduces the second and third known injection eliminations.
/// The two return/bind seams remain, so this is a distinct certificate term.
///
/// # Specification
/// - requires: nothing.
/// - ensures: negates Bool with two return/bind seams in each branch.
/// - provides: a well-typed intensional alternative to negation.
/// - panics: only on an invalid fixed fixture construction.
///
/// # Adequacy
/// - hypothesis: L3 — both inputs agree with raw triple composition, but path
///   conversion still distinguishes the retained seams.
/// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
fn inlined_triple_negation(arena: &mut TermArena) -> ValueId
{
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let payload = arena.computation_return(variable);
    let mut branches = Vec::new();
    for side in [Side::Right, Side::Left] {
        let value = arena.value_injection(side, variable);
        let result = arena.computation_return(value);
        let result = arena.computation_bind(payload, result);
        branches.push(arena.computation_bind(payload, result));
    }
    let right = branches.pop().expect("right branch");
    let left = branches.pop().expect("left branch");
    let body = arena.computation_case(variable, left, right);
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// Produce both Bool round-trip dialogues by running the real conversion
/// engine.
///
/// # Specification
/// - requires: both translators and constructors are closed terms.
/// - ensures: each dialogue is the engine's trace on its actual round-trip
///   claim.
/// - provides: untrusted evidence, including negative traces for bad maps.
/// - panics: if fixture translation or the engine fails operationally.
///
/// # Adequacy
/// - hypothesis: L3 — true/false round trips admit negation and refuse a
///   constant map.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
fn evidence(
    arena: &mut TermArena,
    boolean: &Boolean,
    forward: ValueId,
    backward: ValueId,
) -> RoundTrips
{
    let mut directions = Vec::new();
    for (first, second) in [(forward, backward), (backward, forward)] {
        let mut dialogues = Vec::new();
        for value in [boolean.truth, boolean.falsity] {
            let first = apply(arena, first, value);
            let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
            let second = apply(arena, second, variable);
            let composite = arena.computation_bind(first, second);
            let identity = arena.computation_return(value);
            let (_, dialogue) = engine(arena, composite, identity);
            dialogues.push(dialogue);
        }
        directions.push(dialogues);
    }
    let target = directions.pop().expect("target dialogue");
    let source = directions.pop().expect("source dialogue");
    RoundTrips { source, target }
}

/// Insert the syntactic equivalence, without kernel formation yet.
///
/// # Specification
/// - requires: the fixture roots belong to `arena`.
/// - ensures: raw `equiv forward backward` carries engine round-trip traces.
/// - provides: the shared fixture introduction.
/// - panics: on a fixture-construction error.
///
/// # Adequacy
/// - hypothesis: L3 — the same raw introduction may form or fail based on its
///   maps.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
fn equivalence(
    arena: &mut TermArena,
    paths: &mut Paths,
    boolean: &Boolean,
    forward: ValueId,
    backward: ValueId,
) -> PathId
{
    let round_trips = evidence(arena, boolean, forward, backward);
    paths
        .push(Path::Equiv {
            source: boolean.code,
            target: boolean.code,
            forward,
            backward,
            round_trips,
        })
        .expect("raw equivalence")
}

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
/// - witness: `path_universe::tests::it_computes_through_a_former`
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
            | Computation::Absurd(_) => {
                panic!("empty elimination is outside the path fixture fragment")
            },
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
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
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
                    | Computation::Absurd(_) => {
                        panic!("empty elimination is outside the path fixture fragment")
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
            | AnyNode::ValueType(_) | AnyNode::CompType(_) => {
                panic!("no type nodes in fixture computations")
            },
        }
    }
    (core, computations[&left], computations[&right])
}

/// Run the untrusted engine and retain its complete decision sequence.
///
/// # Specification
/// - requires: the sides are closed computations in the fixture fragment.
/// - ensures: verdict and trace come from `core-nbe::decide`, not kernel
///   replay.
/// - provides: independent computation of each claim.
/// - panics: on fixture translation or an operational engine failure.
///
/// # Adequacy
/// - hypothesis: L3 — independent positive and negative traces replay to their
///   verdicts.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
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

#[test]
fn transport_computes()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let mut paths = Paths::new();
    let path = equivalence(&mut arena, &mut paths, &boolean, boolean.not, boolean.not);
    let expected = arena.computation_return(boolean.truth);
    let applied = apply(&mut arena, boolean.not, boolean.falsity);
    let (claim, dialogue) = engine(&arena, applied, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    let term = Transport {
        path,
        value: boolean.falsity,
    };
    let watermark = arena.watermark();
    assert_eq!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            claim,
            &dialogue,
            ReplayBudget::DEFAULT
        )
        .expect("formed"),
        KernelVerdict::Convertible
    );
    assert_eq!(arena.watermark(), watermark);
    assert!(matches!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            claim,
            &dialogue,
            ReplayBudget::from(0_u64)
        ),
        Err(PathError::Budget)
    ));
    assert_eq!(arena.watermark(), watermark);
}

#[test]
fn it_computes_through_a_former()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let mut paths = Paths::new();
    let negation = equivalence(&mut arena, &mut paths, &boolean, boolean.not, boolean.not);
    let path = paths
        .push(Path::Product(negation, negation))
        .expect("product path");
    let value = arena.value_pair(boolean.truth, boolean.falsity);
    let expected_pair = arena.value_pair(boolean.falsity, boolean.truth);
    let expected = arena.computation_return(expected_pair);
    let term = Transport { path, value };
    assert_eq!(
        beta(&arena, &paths, term).expect("product beta"),
        Reduct::Pair(
            Transport {
                path: negation,
                value: boolean.truth
            },
            Transport {
                path: negation,
                value: boolean.falsity
            }
        )
    );
    // The producer writes its own componentwise reduct; the kernel does not read
    // it.
    let first = apply(&mut arena, boolean.not, boolean.truth);
    let second = apply(&mut arena, boolean.not, boolean.falsity);
    let one = arena.value_variable(DeBruijnIndex::from(1_u32));
    let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
    let pair = arena.value_pair(one, zero);
    let result = arena.computation_return(pair);
    let result = arena.computation_bind(second, result);
    let result = arena.computation_bind(first, result);
    let (claim, dialogue) = engine(&arena, result, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    assert_eq!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            claim,
            &dialogue,
            ReplayBudget::DEFAULT
        )
        .expect("formed"),
        KernelVerdict::Convertible
    );
    let left_expected = arena.computation_return(boolean.falsity);
    let right_expected = arena.computation_return(boolean.truth);
    let (_, first_trace) = engine(&arena, first, left_expected);
    let (_, second_trace) = engine(&arena, second, right_expected);
    let paired = Dialogue::pair(first_trace, second_trace);
    assert_eq!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            EngineClaim::Convertible,
            &paired,
            ReplayBudget::DEFAULT
        )
        .expect("paired dialogue"),
        KernelVerdict::Convertible
    );
    let mut corrupt = paired;
    corrupt.0.push(ConversionDecision::Decompose);
    assert!(matches!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            EngineClaim::Convertible,
            &corrupt,
            ReplayBudget::DEFAULT
        )
        .expect("formed"),
        KernelVerdict::Declined(_)
    ));
}

#[test]
fn refl_collapses()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let mut paths = Paths::new();
    let path = paths.push(Path::Refl(boolean.code)).expect("refl");
    for value in [boolean.truth, boolean.falsity] {
        let term = Transport { path, value };
        assert_eq!(
            beta(&arena, &paths, term).expect("one beta step"),
            Reduct::Return(value)
        );
        let expected = arena.computation_return(value);
        let (claim, dialogue) = engine(&arena, expected, expected);
        assert_eq!(
            replay_transport(
                &mut arena,
                &paths,
                term,
                expected,
                claim,
                &dialogue,
                ReplayBudget::DEFAULT
            )
            .expect("formed"),
            KernelVerdict::Convertible
        );
    }
}

#[test]
fn a_wrong_answer_is_caught()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let mut paths = Paths::new();
    let path = equivalence(&mut arena, &mut paths, &boolean, boolean.not, boolean.not);
    let expected = arena.computation_return(boolean.falsity);
    let applied = apply(&mut arena, boolean.not, boolean.falsity);
    let (claim, dialogue) = engine(&arena, applied, expected);
    assert_eq!(claim, EngineClaim::NotConvertible);
    let term = Transport {
        path,
        value: boolean.falsity,
    };
    assert_eq!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            claim,
            &dialogue,
            ReplayBudget::DEFAULT
        )
        .expect("formed"),
        KernelVerdict::NotConvertible
    );
    assert!(matches!(
        replay_transport(
            &mut arena,
            &paths,
            term,
            expected,
            EngineClaim::Convertible,
            &dialogue,
            ReplayBudget::DEFAULT
        )
        .expect("formed"),
        KernelVerdict::Declined(_)
    ));
}

#[test]
fn a_non_equivalence_is_refused()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let mut paths = Paths::new();
    let returned = arena.computation_return(boolean.truth);
    let lambda = arena.computation_lambda(returned);
    let constant = arena.value_thunk(lambda);
    let path = equivalence(&mut arena, &mut paths, &boolean, constant, constant);
    assert!(matches!(
        form(&mut arena, &paths, path, ReplayBudget::DEFAULT),
        Err(PathError::RoundTrip {
            direction: Direction::Source,
            pattern: PatternPosition(1),
            verdict: KernelVerdict::Declined(_)
        })
    ));
    let missing = paths
        .push(Path::Equiv {
            source: boolean.code,
            target: boolean.code,
            forward: boolean.not,
            backward: boolean.not,
            round_trips: RoundTrips::default(),
        })
        .expect("missing evidence");
    assert!(matches!(
        form(&mut arena, &paths, missing, ReplayBudget::DEFAULT),
        Err(PathError::Coverage(Direction::Source))
    ));
    let unit = arena.value_unit();
    let mistyped = paths
        .push(Path::Equiv {
            source: boolean.code,
            target: boolean.code,
            forward: unit,
            backward: boolean.not,
            round_trips: RoundTrips::default(),
        })
        .expect("mistyped");
    assert!(matches!(
        form(&mut arena, &paths, mistyped, ReplayBudget::DEFAULT),
        Err(PathError::Typing(_))
    ));
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let thunk_type = arena.value_type_thunk(returner);
    let code = arena.value_quote(thunk_type);
    let unsupported = paths.push(Path::Refl(code)).expect("raw unsupported code");
    assert!(
        matches!(form(&mut arena, &paths, unsupported, ReplayBudget::DEFAULT), Err(PathError::UnsupportedType(found)) if found == thunk_type)
    );
    // A real engine trace at one literal is not a universally quantified
    // certificate. A well-typed constant map passes that sample and still fails
    // the kernel's symbolic Base obligation.
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(string);
    let sample = arena.value_literal(gandr_kernel_term::Literal::Text(
        gandr_kernel_term::StringLiteral::new("sample".into()),
    ));
    let returned = arena.computation_return(sample);
    let lambda = arena.computation_lambda(returned);
    let constant_string = arena.value_thunk(lambda);
    let composed = compose(&mut arena, constant_string, constant_string);
    let sampled = apply(&mut arena, composed, sample);
    let (claim, dialogue) = engine(&arena, sampled, returned);
    assert_eq!(claim, EngineClaim::Convertible);
    let bad_base = paths
        .push(Path::Equiv {
            source: code,
            target: code,
            forward: constant_string,
            backward: constant_string,
            round_trips: RoundTrips {
                source: vec![dialogue.clone()],
                target: vec![dialogue],
            },
        })
        .expect("well-typed sampled claim");
    assert!(matches!(
        form(&mut arena, &paths, bad_base, ReplayBudget::DEFAULT),
        Err(PathError::RoundTrip {
            direction: Direction::Source,
            pattern: PatternPosition(0),
            verdict: KernelVerdict::Declined(_),
        })
    ));
    // The same boundary admits an actual polymorphic identity, including a
    // product pattern with two independent base leaves.
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let identity_body = arena.computation_return(variable);
    let identity_lambda = arena.computation_lambda(identity_body);
    let identity = arena.value_thunk(identity_lambda);
    let product = arena.value_type_product(string, string);
    let code = arena.value_quote(product);
    let sample_pair = arena.value_pair(sample, sample);
    let composed = compose(&mut arena, identity, identity);
    let sampled = apply(&mut arena, composed, sample_pair);
    let returned = arena.computation_return(sample_pair);
    let (claim, dialogue) = engine(&arena, sampled, returned);
    assert_eq!(claim, EngineClaim::Convertible);
    let valid_base_product = paths
        .push(Path::Equiv {
            source: code,
            target: code,
            forward: identity,
            backward: identity,
            round_trips: RoundTrips {
                source: vec![dialogue.clone()],
                target: vec![dialogue],
            },
        })
        .expect("symbolic product identity");
    let formed = form(
        &mut arena,
        &paths,
        valid_base_product,
        ReplayBudget::DEFAULT,
    )
    .expect("generic product round trips replay");
    assert_eq!(formed.source, product);
    assert_eq!(formed.target, product);
}

#[test]
fn certificate_identity_stays_out_of_conversion()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let twice = compose(&mut arena, boolean.not, boolean.not);
    let original = compose(&mut arena, twice, boolean.not);
    let thrice = inlined_triple_negation(&mut arena);
    for value in [boolean.truth, boolean.falsity] {
        let original = apply(&mut arena, original, value);
        let inlined = apply(&mut arena, thrice, value);
        assert_eq!(
            engine(&arena, original, inlined).0,
            EngineClaim::Convertible
        );
    }
    let mut paths = Paths::new();
    let first = equivalence(&mut arena, &mut paths, &boolean, boolean.not, boolean.not);
    let second = equivalence(&mut arena, &mut paths, &boolean, boolean.not, thrice);
    let first_type =
        form(&mut arena, &paths, first, ReplayBudget::DEFAULT).expect("not/not equivalence");
    let second_type = form(&mut arena, &paths, second, ReplayBudget::DEFAULT)
        .expect("not/triple-not equivalence");
    assert_eq!(first_type, second_type);
    assert_eq!(
        convert(&arena, &paths, first, second, ReplayBudget::DEFAULT).expect("conversion"),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        convert(&arena, &paths, first, first, ReplayBudget::DEFAULT).expect("reflexive conversion"),
        KernelVerdict::Convertible
    );
}

#[test]
fn no_k()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let mut paths = Paths::new();
    let path = equivalence(&mut arena, &mut paths, &boolean, boolean.not, boolean.not);
    let term = Transport {
        path,
        value: boolean.falsity,
    };
    assert_eq!(
        elaborate(
            &mut arena,
            &paths,
            EliminatorName::from("transport"),
            term,
            ReplayBudget::DEFAULT
        )
        .expect("transport elaborates"),
        term
    );
    let k = EliminatorName::from("K");
    assert!(
        matches!(elaborate(&mut arena, &paths, k.clone(), term, ReplayBudget::DEFAULT), Err(PathError::UnknownEliminator(name)) if name == k)
    );
    let refl = paths.push(Path::Refl(boolean.code)).expect("refl");
    assert_eq!(
        convert(&arena, &paths, path, refl, ReplayBudget::DEFAULT).expect("no collapse"),
        KernelVerdict::NotConvertible
    );
}
