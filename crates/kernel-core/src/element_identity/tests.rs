//! Element-identity witnesses: formation, reflexivity, native evidence, higher
//! fields, higher evaluation, transport and a persisted certificate.

use alloc::boxed::Box;
use alloc::string::ToString as _;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::EvaluationComponent;
use gandr_kernel_term::EvaluationDialogues;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::HigherDepth;
use gandr_kernel_term::HigherLayer;
use gandr_kernel_term::HigherProgram;
use gandr_kernel_term::LayerPosition;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Literal;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::ElementTransport;
use super::IdentityError;
use super::RelatedStep;
use super::evaluation_obligations;
use super::higher_codata;
use super::related_beta;
use super::transport_beta;
use crate::check::check_closed_value;
use crate::check::synth_closed_value;
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::encoding::content_digest;
use crate::env::Environment;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::error::NonInferableForm;
use crate::higher_field::Cell;
use crate::higher_field::Depth;
use crate::higher_field::ObservationBudget;
use crate::higher_field::symmetry;
use crate::identity_recursion::Component;
use crate::identity_recursion::EvaluationSide;
use crate::identity_recursion::HigherEvaluation;
use crate::identity_recursion::Pointwise;
use crate::identity_recursion::function_fixtures::boolean;
use crate::identity_recursion::function_fixtures::higher;
use crate::path_universe::Reduction;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

/// Replay a computation against its claimed reduct with an empty dialogue:
/// every step the claim needs is a search-free reduction.
///
/// # Specification
/// trivial.
fn computes(
    arena: &mut TermArena,
    computation: ComputationId,
    reduct: ComputationId,
) -> KernelVerdict
{
    crate::replay::replay(
        arena,
        &Unfoldings::default(),
        ReplaySides::Computations(computation, reduct),
        EngineClaim::Convertible,
        core::iter::empty(),
        ReplayBudget::DEFAULT,
    )
}

/// The level-zero value universe.
///
/// # Specification
/// trivial.
fn universe(arena: &mut TermArena) -> ValueTypeId
{
    arena.value_type_universe(GroundSort::Value, Level::zero())
}

/// Forget a replay anchor, as the wire does.
///
/// # Specification
/// trivial.
fn erase(decision: ConversionDecision<ReplayNode>) -> ConversionDecision<()>
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
            ConversionDecision::EtaExpand { side, variable: () }
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

/// Persist an in-memory higher evaluation as the kernel node's two payloads.
///
/// # Specification
/// trivial.
fn persisted(
    arena: &mut TermArena,
    evaluation: &HigherEvaluation,
) -> ValueId
{
    let mut dialogues = Vec::new();
    let mut components = Vec::new();
    for pointwise in &evaluation.0 {
        let &Pointwise::Return {
            ref left,
            ref right,
            proof,
        } = pointwise
        else {
            panic!("the fixture returns at every component");
        };
        dialogues.push(EvaluationDialogues {
            left: left.dialogue.0.iter().copied().map(erase).collect(),
            right: right.dialogue.0.iter().copied().map(erase).collect(),
        });
        components.push(EvaluationComponent {
            left: left.value,
            right: right.value,
            evidence: proof,
        });
    }
    arena.value_higher_evaluation(Arc::from(dialogues), Box::from(components))
}

/// A guarded higher field of one self-looping guard over one evidence value.
///
/// # Specification
/// trivial.
fn guarded(
    arena: &mut TermArena,
    depth: HigherDepth,
    evidence: ValueId,
) -> ValueId
{
    let program = HigherProgram {
        depth,
        root: LayerPosition(0),
        layers: Vec::from([HigherLayer::Guard {
            tail: LayerPosition(0),
        }]),
    };
    arena.value_higher(Arc::new(program), Box::from([evidence]))
}

#[test]
fn identity_at_an_open_type_is_a_neutral_fibre()
{
    // A sealed atom: reflexivity at it admits, and native evidence there
    // refuses, since the fold has no clause to read.
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = universe(staging.arena());
    let declaration = staging.abstract_type(LevelSignature::monomorphic(), kind);
    let atom = environment
        .add_decl(declaration)
        .expect("an abstract type at the value universe")
        .position();
    let mut staging = environment.stage();
    let sealed = staging.arena().value_type_abstract(atom);
    let declaration = staging.axiom(LevelSignature::monomorphic(), sealed);
    let point = environment
        .add_decl(declaration)
        .expect("a sealed point")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let sealed = arena.value_type_abstract(atom);
    let point_value = arena.value_constant(point);
    let identity = arena.value_type_path(sealed, point_value, point_value);
    let here = arena.value_here(point_value);
    let declaration = staging.def(LevelSignature::monomorphic(), identity, here);
    environment
        .add_decl(declaration)
        .expect("reflexivity at a sealed atom");
    let mut staging = environment.stage();
    let arena = staging.arena();
    let sealed = arena.value_type_abstract(atom);
    let point_value = arena.value_constant(point);
    let identity = arena.value_type_path(sealed, point_value, point_value);
    let unit = arena.value_unit();
    let declaration = staging.def(LevelSignature::monomorphic(), identity, unit);
    let Err(error) = environment.add_decl(declaration)
    else {
        panic!("native evidence inhabited the identity at a sealed atom");
    };
    assert!(matches!(
        error,
        KernelError::Identity(IdentityError::NeutralFibre)
    ));
    assert_eq!(error.to_string(), "an identity fibre is neutral");

    // A domain that reads a binder: `Π (x : U). Π (y : El x). F (Path(El x, y,
    // y))` forms, `here(y)` checks against it and synthesizes at it, and the
    // unit as native evidence refuses as a neutral fibre.
    let mut arena = TermArena::new();
    let universe_type = universe(&mut arena);
    let decoded = |arena: &mut TermArena, index: u32| {
        let code = arena.value_variable(DeBruijnIndex::from(index));
        arena.value_type_element(code, Level::zero())
    };
    let element = decoded(&mut arena, 0);
    let open = decoded(&mut arena, 1);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let identity = arena.value_type_path(open, bound, bound);
    let returner = arena.comp_type_returner(identity);
    let inner = arena.comp_type_pi(element, returner);
    let outer = arena.comp_type_pi(universe_type, inner);
    let declared = arena.value_type_thunk(outer);
    let here = arena.value_here(bound);
    let lambdas = |arena: &mut TermArena, body: ComputationId| {
        let body = arena.computation_lambda(body);
        let body = arena.computation_lambda(body);
        arena.value_thunk(body)
    };
    let returned_here = arena.computation_return(here);
    let reflexive = lambdas(&mut arena, returned_here);
    check_closed_value(&mut arena, reflexive, declared).expect("reflexivity at an open type");
    let unit = arena.value_unit();
    let returned_unit = arena.computation_return(unit);
    let native = lambdas(&mut arena, returned_unit);
    assert!(matches!(
        check_closed_value(&mut arena, native, declared),
        Err(KernelError::Identity(IdentityError::NeutralFibre))
    ));
    let unit_type = arena.value_type_unit();
    let unit_returner = arena.comp_type_returner(unit_type);
    let synthesized = arena.computation_bind(returned_here, returned_unit);
    let inner = arena.comp_type_pi(element, unit_returner);
    let outer = arena.comp_type_pi(universe_type, inner);
    let discarded = arena.value_type_thunk(outer);
    let synthesized = lambdas(&mut arena, synthesized);
    check_closed_value(&mut arena, synthesized, discarded)
        .expect("reflexivity synthesized at an open type");

    // A closed Bool between two variables is a neutral fibre too.
    let boolean = boolean(&mut arena);
    let first = arena.value_variable(DeBruijnIndex::from(1_u32));
    let second = arena.value_variable(DeBruijnIndex::from(0_u32));
    let apart = arena.value_type_path(boolean.ty, first, second);
    let returner = arena.comp_type_returner(apart);
    let inner = arena.comp_type_pi(boolean.ty, returner);
    let outer = arena.comp_type_pi(boolean.ty, inner);
    let declared = arena.value_type_thunk(outer);
    assert!(matches!(
        check_closed_value(&mut arena, native, declared),
        Err(KernelError::Identity(IdentityError::NeutralFibre))
    ));

    // `Π (x : U). Π (y z : El x). Path(El x, y, z) → F (Path(El x, y, z))`:
    // a path inhabits its own neutral fibre by structural conversion, never
    // the reversed one, and transport in the singleton family along it sends
    // `here(y)` to the path itself.
    let typed = |arena: &mut TermArena, result: ValueTypeId| {
        let x = decoded(arena, 2);
        let y = arena.value_variable(DeBruijnIndex::from(1_u32));
        let z = arena.value_variable(DeBruijnIndex::from(0_u32));
        let premise = arena.value_type_path(x, y, z);
        let returns = arena.comp_type_returner(result);
        let arrow = arena.comp_type_arrow(premise, returns);
        let element_z = decoded(arena, 1);
        let arrow = arena.comp_type_pi(element_z, arrow);
        let element_y = decoded(arena, 0);
        let arrow = arena.comp_type_pi(element_y, arrow);
        let arrow = arena.comp_type_pi(universe_type, arrow);
        arena.value_type_thunk(arrow)
    };
    let four = |arena: &mut TermArena, body: ComputationId| {
        let body = arena.computation_lambda(body);
        let body = arena.computation_lambda(body);
        lambdas(arena, body)
    };
    let x = decoded(&mut arena, 2);
    let y = arena.value_variable(DeBruijnIndex::from(1_u32));
    let z = arena.value_variable(DeBruijnIndex::from(0_u32));
    let forward = arena.value_type_path(x, y, z);
    let reversed = arena.value_type_path(x, z, y);
    let declared = typed(&mut arena, forward);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returned_path = arena.computation_return(path);
    let echo = four(&mut arena, returned_path);
    check_closed_value(&mut arena, echo, declared).expect("a path at its own neutral fibre");
    let swapped = typed(&mut arena, reversed);
    let refused = check_closed_value(&mut arena, echo, swapped);
    assert!(
        matches!(refused, Err(KernelError::ValueTypeMismatch(_))),
        "{refused:?}"
    );
    let family_domain = decoded(&mut arena, 4);
    let family_left = arena.value_variable(DeBruijnIndex::from(3_u32));
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let singleton = arena.value_type_path(family_domain, family_left, endpoint);
    let y = arena.value_variable(DeBruijnIndex::from(2_u32));
    let reflexive_y = arena.value_here(y);
    let transport = arena.computation_path_transport(singleton, path, reflexive_y);
    let derived_j = four(&mut arena, transport);
    check_closed_value(&mut arena, derived_j, declared)
        .expect("transport in the singleton family at an open type");
    assert_eq!(
        computes(&mut arena, transport, returned_path),
        KernelVerdict::Convertible
    );

    // In a family that reads its binder otherwise, transport along the
    // neutral path is stuck, and along `here` it reduces.
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    let cosingleton = arena.value_type_path(family_domain, endpoint, family_left);
    assert_eq!(
        transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
            motive: cosingleton,
            path,
            value: reflexive_y,
        }),
        Ok(Reduction::Stuck)
    );
    let Ok(Reduction::Reduced(reduct)) =
        transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
            motive: cosingleton,
            path: reflexive_y,
            value: reflexive_y,
        })
    else {
        panic!("transport along here reduces at an open type");
    };
    assert_eq!(
        arena.computation(reduct),
        Some(&Computation::Return(reflexive_y))
    );
}

#[test]
fn native_evidence_checks_against_the_fold_fibre()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();

    // Bool: equal endpoints relate by the unit fibre, distinct ones by none.
    let diagonal = arena.value_type_path(boolean.ty, boolean.truth, boolean.truth);
    let apart = arena.value_type_path(boolean.ty, boolean.truth, boolean.falsity);
    check_closed_value(&mut arena, unit, diagonal).expect("unit evidence at true = true");
    assert!(matches!(
        check_closed_value(&mut arena, unit, apart),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));

    // `here` checks by the kernel's conversion and names both endpoints.
    let here = arena.value_here(boolean.truth);
    check_closed_value(&mut arena, here, diagonal).expect("here(true) : true = true");
    let left = content_digest(&arena, AnyNode::Value(boolean.truth));
    let right = content_digest(&arena, AnyNode::Value(boolean.falsity));
    let refused = check_closed_value(&mut arena, here, apart);
    assert_eq!(
        refused,
        Err(KernelError::Identity(IdentityError::EndpointsDiffer {
            left,
            right
        }))
    );
    // `here` synthesizes only where its point does, as every annotation-free
    // introduction: a literal's diagonal is inferable, an injection's is not.
    let text = arena.value_literal(Literal::Text(StringLiteral::new("a".into())));
    let diagonal_text = arena.value_here(text);
    let synthesized = synth_closed_value(&mut arena, diagonal_text).expect("here synthesizes");
    assert!(matches!(
        arena.value_type(synthesized),
        Some(&ValueType::Path { domain, left, right })
            if matches!(arena.value_type(domain), Some(&ValueType::Base(BaseType::String)))
                && left == text && right == text
    ));
    assert_eq!(
        synth_closed_value(&mut arena, here),
        Err(KernelError::NotInferable {
            form: NonInferableForm::Injection
        })
    );

    // A product relates componentwise.
    let pair_type = arena.value_type_product(&[boolean.ty, unit_type]);
    let pair = arena.value_tuple(&[boolean.truth, unit]);
    let pair_identity = arena.value_type_path(pair_type, pair, pair);
    let evidence = arena.value_tuple(&[unit, unit]);
    check_closed_value(&mut arena, evidence, pair_identity).expect("componentwise evidence");

    // The universe relates codes by native universe paths.
    let universe_type = universe(&mut arena);
    let code = arena.value_quote(boolean.ty);
    let codes = arena.value_type_path(universe_type, code, code);
    let refl = arena.value_path_refl(code);
    check_closed_value(&mut arena, refl, codes).expect("Path_U evidence at Path(U, Bool, Bool)");

    // An identity of identities reads the inner fibre, `here` as its diagonal.
    let iterated = arena.value_type_path(diagonal, here, unit);
    check_closed_value(&mut arena, unit, iterated).expect("unit evidence between diagonals");

    // A neutral inhabits an identity by its own type; a neutral of the fibre
    // type does not, because conversion stays structural.
    let returns = arena.comp_type_returner(diagonal);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let body = arena.computation_return(variable);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let by_type = arena.comp_type_arrow(diagonal, returns);
    let by_type = arena.value_type_thunk(by_type);
    check_closed_value(&mut arena, body, by_type).expect("a variable at its identity type");
    let by_fibre = arena.comp_type_arrow(unit_type, returns);
    let by_fibre = arena.value_type_thunk(by_fibre);
    assert!(matches!(
        check_closed_value(&mut arena, body, by_fibre),
        Err(KernelError::ValueTypeMismatch(_))
    ));

    // A type the fold does not cover is refused by name.
    let list = arena.value_type_list(boolean.ty);
    let nil = arena.value_list_nil();
    let lists = arena.value_type_path(list, nil, nil);
    assert!(matches!(
        check_closed_value(&mut arena, unit, lists),
        Err(KernelError::Identity(IdentityError::RecursiveObservation))
    ));
}

#[test]
fn a_higher_field_checks_and_computes_square_symmetry()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit = arena.value_unit();
    let here = arena.value_here(boolean.truth);
    let inner = arena.value_type_path(boolean.ty, boolean.truth, boolean.truth);
    let squares = arena.value_type_path(inner, here, here);
    let field = guarded(&mut arena, HigherDepth(8), unit);
    check_closed_value(&mut arena, field, squares).expect("eight guarded layers");

    // The persisted field reads back as the guarded program symmetry observes.
    let Some(node) = arena.value(field)
    else {
        panic!("a readable field");
    };
    let Value::Higher {
        ref program,
        ref evidence,
    } = *node
    else {
        panic!("a higher field");
    };
    let program = Arc::clone(program);
    let evidence = evidence.clone();
    let codata = higher_codata(&program, &evidence).expect("one guard, one evidence");
    let path = Cell {
        code: arena.value_quote(boolean.ty),
        left: boolean.truth,
        right: boolean.truth,
        evidence: unit,
    };
    let budget = ObservationBudget {
        depth: Depth(program.depth.0),
        replay: ReplayBudget::DEFAULT,
    };
    let square = symmetry(&mut arena, &[], path, &codata, budget).expect("square symmetry");
    assert_eq!(square.top, path);
    assert_eq!(
        (square.right.left, square.right.right),
        (path.right, path.left)
    );
    assert_eq!(square.filler.depth, Depth(8));
    assert_eq!(
        equal_values(&arena, square.right.evidence, unit),
        Convertibility::Convertible
    );

    // Evidence outside the guard's fibre refuses at its own goal, and the
    // evidence count must match the guards.
    let wrong = guarded(&mut arena, HigherDepth(2), boolean.truth);
    assert!(matches!(
        check_closed_value(&mut arena, wrong, squares),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Sum,
            ..
        })
    ));
    let program = HigherProgram {
        depth: HigherDepth(1),
        root: LayerPosition(0),
        layers: Vec::from([HigherLayer::Guard {
            tail: LayerPosition(0),
        }]),
    };
    let surplus = arena.value_higher(Arc::new(program), Box::from([unit, unit]));
    assert_eq!(
        check_closed_value(&mut arena, surplus, squares),
        Err(KernelError::Identity(IdentityError::GuardEvidence))
    );
}

#[test]
fn a_non_productive_higher_field_is_refused_by_name()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let here = arena.value_here(boolean.truth);
    let inner = arena.value_type_path(boolean.ty, boolean.truth, boolean.truth);
    let squares = arena.value_type_path(inner, here, here);
    for layers in [
        Vec::from([HigherLayer::Redirect(LayerPosition(0))]),
        Vec::from([
            HigherLayer::Redirect(LayerPosition(1)),
            HigherLayer::Redirect(LayerPosition(0)),
        ]),
    ] {
        let program = HigherProgram {
            depth: HigherDepth(4),
            root: LayerPosition(0),
            layers,
        };
        let field = arena.value_higher(Arc::new(program), Box::from([]));
        let refused = check_closed_value(&mut arena, field, squares);
        assert_eq!(
            refused,
            Err(KernelError::Identity(IdentityError::NonProductive(
                LayerPosition(0)
            )))
        );
        assert_eq!(
            refused.expect_err("refused").to_string(),
            "non-productive higher field"
        );
    }
    let unit = arena.value_unit();
    let shallow = guarded(&mut arena, HigherDepth(0), unit);
    assert_eq!(
        check_closed_value(&mut arena, shallow, squares),
        Err(KernelError::Identity(IdentityError::ZeroDepth))
    );
    let field = guarded(&mut arena, HigherDepth(1), unit);
    assert!(matches!(
        check_closed_value(&mut arena, field, boolean.ty),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            ..
        })
    ));
    assert_eq!(
        synth_closed_value(&mut arena, field),
        Err(KernelError::NotInferable {
            form: NonInferableForm::HigherField
        })
    );
}

#[test]
fn a_higher_evaluation_proves_function_extensionality()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let functions = boolean.function;
    let extensional = arena.value_type_path(functions, boolean.double, boolean.identity);
    let evidence = higher(&mut arena, &boolean, (boolean.double, boolean.identity), [
        (boolean.truth, boolean.truth),
        (boolean.falsity, boolean.falsity),
    ]);
    let funext = persisted(&mut arena, &evidence);
    check_closed_value(&mut arena, funext, extensional).expect("not ∘ not = id");

    // A false claim refuses at its output evidence, a swapped component at
    // its replay, and a missing component at coverage.
    let negation = arena.value_type_path(functions, boolean.not, boolean.identity);
    let wrong = higher(&mut arena, &boolean, (boolean.not, boolean.identity), [
        (boolean.falsity, boolean.truth),
        (boolean.truth, boolean.falsity),
    ]);
    let wrong = persisted(&mut arena, &wrong);
    assert!(matches!(
        check_closed_value(&mut arena, wrong, negation),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));
    let mut swapped = evidence.clone();
    swapped.0.swap(0, 1);
    let swapped = persisted(&mut arena, &swapped);
    assert!(matches!(
        check_closed_value(&mut arena, swapped, extensional),
        Err(KernelError::Identity(IdentityError::Evaluation {
            component: Component(0),
            side: EvaluationSide::Left,
            ..
        }))
    ));
    let mut partial = evidence.clone();
    let _dropped = partial.0.pop();
    let partial = persisted(&mut arena, &partial);
    assert_eq!(
        check_closed_value(&mut arena, partial, extensional),
        Err(KernelError::Identity(IdentityError::Coverage))
    );
    assert_eq!(
        synth_closed_value(&mut arena, funext),
        Err(KernelError::NotInferable {
            form: NonInferableForm::HigherEvaluation
        })
    );
    let open = arena.value_variable(DeBruijnIndex::from(0_u32));
    let open = arena.value_type_path(functions, open, boolean.identity);
    let Some(node) = arena.value(funext)
    else {
        panic!("a readable evaluation");
    };
    let Value::HigherEvaluation {
        ref dialogues,
        ref components,
    } = *node
    else {
        panic!("a higher evaluation");
    };
    let (dialogues, components) = (Arc::clone(dialogues), components.clone());
    assert!(matches!(
        evaluation_obligations(&mut arena, open, &dialogues, &components),
        Err(KernelError::Identity(IdentityError::OpenFunctions))
    ));

    // Related application types its body under both results and their
    // identity, at a function identity bound by a lambda.
    let unit = arena.value_unit();
    let source = arena.value_variable(DeBruijnIndex::from(2_u32));
    let body = arena.computation_return(source);
    let returns = arena.comp_type_returner(boolean.ty);
    let eliminate = |arena: &mut TermArena, identity: ValueTypeId, arguments| {
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let applied = arena.computation_related_application(bound, arguments, unit, body);
        let lambda = arena.computation_lambda(applied);
        let lambda = arena.value_thunk(lambda);
        let arrow = arena.comp_type_arrow(identity, returns);
        (lambda, arena.value_type_thunk(arrow))
    };
    let reflexive = arena.value_type_path(functions, boolean.not, boolean.not);
    let related_arguments = (boolean.truth, boolean.truth);
    for identity in [reflexive, extensional] {
        let (lambda, declared) = eliminate(&mut arena, identity, related_arguments);
        check_closed_value(&mut arena, lambda, declared).expect("related application");
    }
    let (unrelated, declared) = eliminate(&mut arena, reflexive, (boolean.truth, boolean.falsity));
    assert!(matches!(
        check_closed_value(&mut arena, unrelated, declared),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Product,
            ..
        })
    ));
    let points = arena.value_type_path(boolean.ty, boolean.truth, boolean.truth);
    let (misapplied, declared) = eliminate(&mut arena, points, related_arguments);
    assert!(matches!(
        check_closed_value(&mut arena, misapplied, declared),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Thunk,
            ..
        })
    ));

    // It computes on `here` at convertible arguments, by replay.
    let here = arena.value_here(boolean.not);
    let related = arena.computation_related_application(here, related_arguments, unit, body);
    let falsity = arena.computation_return(boolean.falsity);
    assert_eq!(
        computes(&mut arena, related, falsity),
        KernelVerdict::Convertible
    );
    let truth = arena.computation_return(boolean.truth);
    assert_ne!(
        computes(&mut arena, related, truth),
        KernelVerdict::Convertible
    );

    // At function-identity evidence it stays neutral: the site carries no
    // pointwise evaluation.
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    let stuck = related_beta(&mut arena, &mut table, &mut memo, RelatedStep {
        path: funext,
        left: boolean.truth,
        right: boolean.truth,
        body,
    });
    assert_eq!(stuck, Ok(Reduction::Stuck));
    let neutral = arena.computation_related_application(funext, related_arguments, unit, body);
    assert_ne!(
        computes(&mut arena, neutral, truth),
        KernelVerdict::Convertible
    );
}

#[test]
fn transport_on_here_is_the_identity_by_replay()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let code = arena.value_quote(boolean.ty);

    // Along `here(Bool)` in the universe family, an element of `El(Bool)`
    // transports to itself, typed at both instantiations of the motive.
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(endpoint, Level::zero());
    let here = arena.value_here(code);
    let element = arena.value_type_element(code, Level::zero());
    let input = arena.value_variable(DeBruijnIndex::from(0_u32));
    let transport = arena.computation_path_transport(motive, here, input);
    let lambda = arena.computation_lambda(transport);
    let lambda = arena.value_thunk(lambda);
    let returns = arena.comp_type_returner(element);
    let arrow = arena.comp_type_arrow(element, returns);
    let declared = arena.value_type_thunk(arrow);
    check_closed_value(&mut arena, lambda, declared).expect("transport in El along here");

    let closed = arena.computation_path_transport(motive, here, boolean.truth);
    let truth = arena.computation_return(boolean.truth);
    let falsity = arena.computation_return(boolean.falsity);
    assert_eq!(
        computes(&mut arena, closed, truth),
        KernelVerdict::Convertible
    );
    assert_ne!(
        computes(&mut arena, closed, falsity),
        KernelVerdict::Convertible
    );
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    let Ok(Reduction::Reduced(reduct)) =
        transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
            motive,
            path: here,
            value: boolean.truth,
        })
    else {
        panic!("transport along here reduces");
    };
    assert_eq!(
        arena.computation(reduct),
        Some(&Computation::Return(boolean.truth))
    );

    // In the identity family at a string, `here(a)` transports to itself too.
    let string = arena.value_type_base(BaseType::String);
    let text = arena.value_literal(Literal::Text(StringLiteral::new("a".into())));
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let singleton = arena.value_type_path(string, text, endpoint);
    let here = arena.value_here(text);
    let transport = arena.computation_path_transport(singleton, here, here);
    let thunk = arena.value_thunk(transport);
    let identity = arena.value_type_path(string, text, text);
    let returns = arena.comp_type_returner(identity);
    let declared = arena.value_type_thunk(returns);
    check_closed_value(&mut arena, thunk, declared).expect("transport in the singleton family");
    let returned = arena.computation_return(here);
    assert_eq!(
        computes(&mut arena, transport, returned),
        KernelVerdict::Convertible
    );
}

#[test]
fn transport_computes_through_the_fold_clauses()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(boolean.ty);
    let path = arena.value_path_refl(code);
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(endpoint, Level::zero());

    // The universe clause: `El(x)` at level zero is native universe transport.
    let universe_step = arena.computation_path_transport(element, path, boolean.truth);
    let truth = arena.computation_return(boolean.truth);
    assert_eq!(
        computes(&mut arena, universe_step, truth),
        KernelVerdict::Convertible
    );

    // A product transports componentwise; its constant part passes through.
    let product = arena.value_type_product(&[element, boolean.ty]);
    let pair = arena.value_tuple(&[boolean.truth, boolean.falsity]);
    let product_step = arena.computation_path_transport(product, path, pair);
    let returned_pair = arena.computation_return(pair);
    assert_eq!(
        computes(&mut arena, product_step, returned_pair),
        KernelVerdict::Convertible
    );
    let swapped = arena.value_tuple(&[boolean.falsity, boolean.truth]);
    let returned_swapped = arena.computation_return(swapped);
    assert_ne!(
        computes(&mut arena, product_step, returned_swapped),
        KernelVerdict::Convertible
    );

    // A sum transports within the injected summand.
    let sum = arena.value_type_sum(&[element, unit_type]);
    let injected = arena.value_injection(Side::Left.into(), boolean.falsity);
    let sum_step = arena.computation_path_transport(sum, path, injected);
    let returned_injection = arena.computation_return(injected);
    assert_eq!(
        computes(&mut arena, sum_step, returned_injection),
        KernelVerdict::Convertible
    );

    // A motive that ignores its binder is constant, also when it reads an
    // outer variable.
    let falsity = arena.computation_return(boolean.falsity);
    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
    let outer = arena.value_type_element(outer, Level::zero());
    for motive in [boolean.ty, outer] {
        let constant_step = arena.computation_path_transport(motive, path, boolean.falsity);
        assert_eq!(
            computes(&mut arena, constant_step, falsity),
            KernelVerdict::Convertible
        );
    }

    // The singleton family sends `here` to the path itself.
    let singleton = arena.value_type_path(boolean.ty, boolean.truth, endpoint);
    let here = arena.value_here(boolean.truth);
    let singleton_step = arena.computation_path_transport(singleton, unit, here);
    let returned_unit = arena.computation_return(unit);
    assert_eq!(
        computes(&mut arena, singleton_step, returned_unit),
        KernelVerdict::Convertible
    );

    // A neutral path in a family that reads its binder stays neutral.
    let neutral = arena.value_variable(DeBruijnIndex::from(0_u32));
    let stuck = arena.computation_path_transport(element, neutral, boolean.truth);
    assert_ne!(
        computes(&mut arena, stuck, truth),
        KernelVerdict::Convertible
    );
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    assert_eq!(
        transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
            motive: sum,
            path,
            value: unit,
        }),
        Ok(Reduction::Stuck)
    );
}

#[test]
fn a_dependent_motive_instantiates_by_substitution()
{
    // λx : U. λy : El x. λp : Path(U, x, Bool).
    //   transport(e. El e × El x, p, (y, y)) : F (El Bool × El x)
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let universe_type = universe(&mut arena);
    let code = arena.value_quote(boolean.ty);
    let decoded = |arena: &mut TermArena, index: u32| {
        let code = arena.value_variable(DeBruijnIndex::from(index));
        arena.value_type_element(code, Level::zero())
    };
    let endpoint = decoded(&mut arena, 0);
    let outer = decoded(&mut arena, 3);
    let motive = arena.value_type_product(&[endpoint, outer]);
    let bound = arena.value_variable(DeBruijnIndex::from(1_u32));
    let pair = arena.value_tuple(&[bound, bound]);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let transport = arena.computation_path_transport(motive, path, pair);
    let body = arena.computation_lambda(transport);
    let body = arena.computation_lambda(body);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let typed = |arena: &mut TermArena, result: ValueTypeId| {
        let x = arena.value_variable(DeBruijnIndex::from(1_u32));
        let identity = arena.value_type_path(universe_type, x, code);
        let returns = arena.comp_type_returner(result);
        let arrow = arena.comp_type_arrow(identity, returns);
        let element = decoded(arena, 0);
        let inner = arena.comp_type_pi(element, arrow);
        let outer = arena.comp_type_pi(universe_type, inner);
        arena.value_type_thunk(outer)
    };
    let target = arena.value_type_element(code, Level::zero());
    let x = decoded(&mut arena, 1);
    let instantiated = arena.value_type_product(&[target, x]);
    let declared = typed(&mut arena, instantiated);
    check_closed_value(&mut arena, body, declared).expect("the motive at the target endpoint");

    // The motive at the source endpoint is not the result type.
    let source = arena.value_type_product(&[x, x]);
    let wrong = typed(&mut arena, source);
    assert!(matches!(
        check_closed_value(&mut arena, body, wrong),
        Err(KernelError::ComputationTypeMismatch(_))
    ));

    // A path whose classifier is not an identity refuses by shape.
    let refl = arena.value_path_refl(code);
    let misused = arena.computation_path_transport(motive, refl, pair);
    let misused = arena.value_thunk(misused);
    let returns = arena.comp_type_returner(boolean.ty);
    let suspended = arena.value_type_thunk(returns);
    assert!(matches!(
        check_closed_value(&mut arena, misused, suspended),
        Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            ..
        })
    ));
}

#[test]
fn a_certificate_with_identity_decodes_checks_and_replays()
{
    let mut environment = Environment::new();
    let mut declarations = Vec::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let first = boolean(arena);
    let identity = arena.value_type_path(first.ty, first.truth, first.truth);
    let here = arena.value_here(first.truth);
    let declaration = staging.def(LevelSignature::monomorphic(), identity, here);
    declarations.push(MarkedDeclaration::new(
        AdmissionMark::Checked,
        declaration.declaration().clone(),
    ));
    let reflexivity = environment.add_decl(declaration).expect("here(true)");
    assert!(environment.audit(reflexivity).axioms().is_empty());

    let mut staging = environment.stage();
    let arena = staging.arena();
    let string = arena.value_type_base(BaseType::String);
    let text = arena.value_literal(Literal::Text(StringLiteral::new("a".into())));
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let singleton = arena.value_type_path(string, text, endpoint);
    let here = arena.value_here(text);
    let transport = arena.computation_path_transport(singleton, here, here);
    let body = arena.value_thunk(transport);
    let identity = arena.value_type_path(string, text, text);
    let returns = arena.comp_type_returner(identity);
    let declared = arena.value_type_thunk(returns);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
    declarations.push(MarkedDeclaration::new(
        AdmissionMark::Checked,
        declaration.declaration().clone(),
    ));
    let transported = environment
        .add_decl(declaration)
        .expect("transport of here");
    assert!(environment.audit(transported).axioms().is_empty());

    let bytes = gandr_kernel_term::encode(environment.arena(), &declarations);
    let decoded = gandr_kernel_term::decode(bytes.as_image()).expect("identity nodes decode");
    assert_eq!(
        gandr_kernel_term::encode(decoded.arena(), decoded.declarations()),
        bytes
    );
    let mut arena = decoded.arena().clone();
    let mut transports = Vec::new();
    for marked in decoded.declarations() {
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("definitions retained");
        };
        check_closed_value(&mut arena, body, declared).expect("decoded identity checks");
        if let Some(&Value::Thunk(computation)) = arena.value(body) {
            transports.push(computation);
        }
    }
    let [transport] = transports[..]
    else {
        panic!("one transport");
    };
    let Some(&Computation::PathTransport { value, .. }) = arena.computation(transport)
    else {
        panic!("the transport decoded");
    };
    let returned = arena.computation_return(value);
    assert_eq!(
        computes(&mut arena, transport, returned),
        KernelVerdict::Convertible
    );
}
