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
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::DecodedArtifact;
use gandr_kernel_term::EndpointDialogues;
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
use gandr_kernel_term::QuantifiedStep;
use gandr_kernel_term::RelatedEndpoints;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::ElementTransport;
use super::EndpointSide;
use super::IdentityError;
use super::RelatedStep;
use super::TelescopeStep;
use super::evaluation_obligations;
use super::higher_codata;
use super::related_beta;
use super::telescope_beta;
use super::transport_beta;
use crate::check::check_closed_value;
use crate::check::synth_closed_value;
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::encoding::content_digest;
use crate::env::CheckedId;
use crate::env::Environment;
use crate::env::StagedDeclaration;
use crate::error::ExpectedComputationShape;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::error::NonInferableForm;
use crate::error::ValueTypeHead;
use crate::higher_field::Cell;
use crate::higher_field::Depth;
use crate::higher_field::ObservationBudget;
use crate::higher_field::symmetry;
use crate::identity_recursion::Component;
use crate::identity_recursion::EvaluationSide;
use crate::identity_recursion::HigherEvaluation;
use crate::identity_recursion::Pointwise;
use crate::identity_recursion::Quantified;
use crate::identity_recursion::function_fixtures::apply_to;
use crate::identity_recursion::function_fixtures::boolean;
use crate::identity_recursion::function_fixtures::duplicate;
use crate::identity_recursion::function_fixtures::evaluation;
use crate::identity_recursion::function_fixtures::higher;
use crate::identity_recursion::function_fixtures::normal_form;
use crate::identity_recursion::function_fixtures::pointwise;
use crate::identity_recursion::function_fixtures::thunk_type;
use crate::path_universe::Reduction;
use crate::replay::EndpointReading;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayDecline;
use crate::replay::ReplayNode;
use crate::replay::ReplayRefusal;
use crate::replay::ReplaySides;
use crate::replay::TracePosition;
use crate::replay::Unfoldable;
use crate::replay::Unfoldings;
use crate::replay::read_endpoints;

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
    decision.map(|_| ())
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
    let integer = staging
        .arena()
        .value_type_base(gandr_kernel_term::BaseType::Integer);
    let declaration = staging.abstract_type(
        LevelSignature::monomorphic(),
        kind,
        integer,
        gandr_kernel_term::SealScope::Closed(gandr_kernel_term::SealExtent::from(0_usize)),
    );
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
fn reflexivity_converts_its_endpoints_by_the_laws_of_bind()
{
    // Under `g : U (Bool → F Bool)`, `here(r)` at `Path(U (Bool → F Bool),
    // l, r)` for three `l`s against `r = thunk (λ b. force g b)`.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let variable =
        |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    // `force g a` with `g` and `a` at the given indices.
    let applied = |arena: &mut TermArena, function: u32, argument: u32| {
        let function = variable(arena, function);
        let forced = arena.computation_force(function);
        let argument = variable(arena, argument);
        arena.computation_application(forced, argument)
    };
    let suspended = |arena: &mut TermArena, body: ComputationId| {
        let lambda = arena.computation_lambda(body);
        arena.value_thunk(lambda)
    };
    let reflexive = |arena: &mut TermArena, left: ValueId, point: ValueId| {
        let identity = arena.value_type_path(boolean.function, left, point);
        let returner = arena.comp_type_returner(identity);
        let pi = arena.comp_type_pi(boolean.function, returner);
        let declared = arena.value_type_thunk(pi);
        let here = arena.value_here(point);
        let returned = arena.computation_return(here);
        let lambda = arena.computation_lambda(returned);
        let term = arena.value_thunk(lambda);
        check_closed_value(arena, term, declared)
    };
    let direct = applied(&mut arena, 1, 0);
    let point = suspended(&mut arena, direct);

    // F-η: `λ b. force g b to x. return x` is `r`.
    let bound = variable(&mut arena, 0);
    let returned = arena.computation_return(bound);
    let expanded = arena.computation_bind(direct, returned);
    let expanded = suspended(&mut arena, expanded);
    reflexive(&mut arena, expanded, point).expect("reflexivity across F-η");

    // Associativity: `λ b. (force g b to x. force g x) to y. force g y`
    // against `λ b. force g b to x. (force g x to y. force g y)`.
    let once = applied(&mut arena, 2, 0);
    let inner = arena.computation_bind(direct, once);
    let nested = arena.computation_bind(inner, once);
    let nested = suspended(&mut arena, nested);
    let twice = applied(&mut arena, 3, 0);
    let fused = arena.computation_bind(once, twice);
    let reassociated = arena.computation_bind(direct, fused);
    let reassociated = suspended(&mut arena, reassociated);
    reflexive(&mut arena, nested, reassociated).expect("reflexivity across associativity");

    // Not pointwise: `λ b. force g b to x. return true` is not `r`, and the
    // refusal names both endpoints and the one the point did not reach.
    let constant = arena.computation_return(boolean.truth);
    let apart = arena.computation_bind(direct, constant);
    let apart = suspended(&mut arena, apart);
    let left = content_digest(&arena, AnyNode::Value(apart));
    let right = content_digest(&arena, AnyNode::Value(point));
    assert!(matches!(
        reflexive(&mut arena, apart, point),
        Err(KernelError::Identity(IdentityError::EndpointsDiffer {
            left: refused_left,
            right: refused_right,
            side: EndpointSide::Left,
            verdict: KernelVerdict::Declined(ReplayDecline::Refused(_)),
        })) if refused_left == left && refused_right == right
    ));
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
    assert!(matches!(
        refused,
        Err(KernelError::Identity(IdentityError::EndpointsDiffer {
            left: refused_left,
            right: refused_right,
            side: EndpointSide::Right,
            verdict: KernelVerdict::Declined(ReplayDecline::Refused(_)),
        })) if refused_left == left && refused_right == right
    ));
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

    // A returned endpoint inhabits an identity as a neutral does, by the type
    // its computation returns, as the checker's value bridge reads it: a
    // returned path checks at its identity type, a returned unit does not
    // stand for the unit fibre's evidence.
    let string_type = arena.value_type_base(BaseType::String);
    let at_text = arena.value_type_path(string_type, text, text);
    let returns_path = arena.computation_return(diagonal_text);
    let returned_path = arena.value_returned(returns_path);
    check_closed_value(&mut arena, returned_path, at_text)
        .expect("a returned path at its identity type");
    let returns_unit = arena.computation_return(unit);
    let returned_unit = arena.value_returned(returns_unit);
    assert!(matches!(
        check_closed_value(&mut arena, returned_unit, at_text),
        Err(KernelError::ValueTypeMismatch(mismatch))
            if mismatch.expected().head() == ValueTypeHead::Path
                && mismatch.actual().head() == ValueTypeHead::Product
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
fn a_pair_of_paths_inhabits_the_identity_of_a_dependent_pair()
{
    // Σ (b : Bool). Path(Bool, b, b), between #{true, here(true)} and itself.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let family = arena.value_type_path(boolean.ty, bound, bound);
    let sigma = arena.value_type_sigma(boolean.ty, family);
    let here_truth = arena.value_here(boolean.truth);
    let pair = arena.value_tuple(&[boolean.truth, here_truth]);
    check_closed_value(&mut arena, pair, sigma).expect("the pair lies in its first's fibre");
    let skewed = arena.value_tuple(&[boolean.falsity, here_truth]);
    assert!(
        matches!(
            check_closed_value(&mut arena, skewed, sigma),
            Err(KernelError::Identity(IdentityError::EndpointsDiffer { .. }))
        ),
        "the same second component over `false` lies in another fibre"
    );

    // The identity reads a path between the first components and, over it,
    // a path from the left second component transported to the right one.
    let identity = arena.value_type_path(sigma, pair, pair);
    let here_here = arena.value_here(here_truth);
    let paths = arena.value_tuple(&[here_truth, here_here]);
    check_closed_value(&mut arena, paths, identity).expect("two reflexivities relate a pair");
    let here_falsity = arena.value_here(boolean.falsity);
    let strayed = arena.value_tuple(&[here_falsity, here_here]);
    assert!(
        matches!(
            check_closed_value(&mut arena, strayed, identity),
            Err(KernelError::Identity(IdentityError::EndpointsDiffer { .. }))
        ),
        "the first path must join the first components"
    );
}

#[test]
fn a_declared_pair_relates_by_its_body_s_components_337()
{
    // A declared pair's identity reads the components of its admitted body,
    // so the reflexivities of those components relate it to itself; an
    // axiom's is read through its projections, which no dialogue relates.
    declared_pair_identity(Admitted::Defined)
        .expect("a declared pair relates by its body's components");
    assert!(
        matches!(
            declared_pair_identity(Admitted::Assumed),
            Err(KernelError::Identity(IdentityError::EndpointsDiffer { .. }))
        ),
        "an axiom's projections do not unfold"
    );
}

/// Admit `c : Σ (b : Bool). Path(Bool, b, b)` — as `#{true, here(true)}`, or
/// as an axiom — then `Path(Σ…, c, c)` as `#{here(true), here(here(true))}`.
///
/// # Specification
/// trivial.
fn declared_pair_identity(admitted: Admitted) -> Result<(), KernelError>
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let boolean = boolean(arena);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let family = arena.value_type_path(boolean.ty, bound, bound);
    let sigma = arena.value_type_sigma(boolean.ty, family);
    let here_truth = arena.value_here(boolean.truth);
    let pair = arena.value_tuple(&[boolean.truth, here_truth]);
    let declaration = match admitted {
        Admitted::Defined => staging.def(LevelSignature::monomorphic(), sigma, pair),
        Admitted::Assumed => staging.axiom(LevelSignature::monomorphic(), sigma),
    };
    let position = environment.add_decl(declaration)?.position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let named = arena.value_constant(position);
    let identity = arena.value_type_path(sigma, named, named);
    let here_here = arena.value_here(here_truth);
    let paths = arena.value_tuple(&[here_truth, here_here]);
    let declaration = staging.def(LevelSignature::monomorphic(), identity, paths);
    environment.add_decl(declaration).map(|_admitted| ())
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
        evaluation_obligations(
            &mut arena,
            &Unfoldings::default(),
            open,
            &dialogues,
            &components
        ),
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

/// Splice one anchor-free δ-step on the left side after a dialogue's opening
/// pair of forces, the two thunks every evaluation claim compares.
///
/// # Specification
/// trivial.
fn unfolding_left(dialogue: &[ConversionDecision<()>]) -> Vec<ConversionDecision<()>>
{
    let (forces, rest) = dialogue.split_at(2);
    assert!(
        forces
            .iter()
            .all(|decision| matches!(decision, ConversionDecision::Force { .. }))
    );
    let mut spliced = forces.to_vec();
    spliced.push(ConversionDecision::Unfold { constant: () });
    spliced.push(ConversionDecision::ReduceLeft { redex: () });
    spliced.extend_from_slice(rest);
    spliced
}

#[test]
fn a_higher_evaluation_unfolds_what_the_environment_admitted()
{
    // Negation is admitted as a definition, then related to its own inlined
    // body. The left evaluation forces the constant, so each of its dialogues
    // owes one δ-step, which a persisted dialogue names by its side alone.
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let defined = boolean(arena);
    let declaration = staging.def(LevelSignature::monomorphic(), defined.function, defined.not);
    let negation = environment
        .add_decl(declaration)
        .expect("negation")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let axiom = boolean(arena);
    let declaration = staging.axiom(LevelSignature::monomorphic(), axiom.function);
    let postulated = environment
        .add_decl(declaration)
        .expect("a postulated function")
        .position();

    let offer = |environment: &mut Environment, head, splice: bool| {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let boolean = boolean(arena);
        let constant = arena.value_constant(head);
        let evidence = higher(arena, &boolean, (boolean.not, boolean.not), [
            (boolean.falsity, boolean.falsity),
            (boolean.truth, boolean.truth),
        ]);
        let mut dialogues = Vec::new();
        let mut components = Vec::new();
        for pointwise in &evidence.0 {
            let &Pointwise::Return {
                ref left,
                ref right,
                proof,
            } = pointwise
            else {
                panic!("the fixture returns at every component");
            };
            let erased = left
                .dialogue
                .0
                .iter()
                .copied()
                .map(erase)
                .collect::<Vec<_>>();
            dialogues.push(EvaluationDialogues {
                left: if splice {
                    unfolding_left(&erased)
                }
                else {
                    erased
                },
                right: right.dialogue.0.iter().copied().map(erase).collect(),
            });
            components.push(EvaluationComponent {
                left: left.value,
                right: right.value,
                evidence: proof,
            });
        }
        let funext = arena.value_higher_evaluation(Arc::from(dialogues), Box::from(components));
        let extensional = arena.value_type_path(boolean.function, constant, boolean.not);
        let declaration = staging.def(LevelSignature::monomorphic(), extensional, funext);
        environment.add_decl(declaration).map(|_admitted| ())
    };
    offer(&mut environment, negation, true).expect("the constant unfolds to its body");
    for (head, splice) in [(negation, false), (postulated, true)] {
        assert!(matches!(
            offer(&mut environment, head, splice),
            Err(KernelError::Identity(IdentityError::Evaluation {
                component: Component(0),
                side: EvaluationSide::Left,
                ..
            }))
        ));
    }
}

/// `λh. return (h, second)`, pairing a function argument with a closed one.
///
/// # Specification
/// trivial.
fn paired_with(
    arena: &mut TermArena,
    second: ValueId,
) -> ValueId
{
    let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
    let both = arena.value_tuple(&[argument, second]);
    let body = arena.computation_return(both);
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

#[test]
fn a_higher_evaluation_covers_a_higher_order_argument()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let inner = boolean.function;
    let pair = arena.value_type_product(&[inner, inner]);
    let outer = thunk_type(&mut arena, inner, pair);
    // The kernel's coverage telescope at a function argument: two functions
    // and their identity, `f₀ f₁ : T, p : Path(T, f₀, f₁)`.
    let [first, second, premise] =
        [2_u32, 1, 0].map(|index| arena.value_variable(DeBruijnIndex::from(index)));
    let identity_type = arena.value_type_path(inner, second, premise);
    let context = [inner, inner, identity_type];

    // Ap of a λ that duplicates its argument replays through the node.
    let duplicate = duplicate(&mut arena);
    let outputs = (
        arena.value_tuple(&[first, first]),
        arena.value_tuple(&[second, second]),
    );
    let proof = arena.value_tuple(&[premise, premise]);
    let reflexivity = HigherEvaluation(Vec::from([pointwise(
        &mut arena,
        &context,
        (duplicate, duplicate),
        (first, second),
        outputs,
        proof,
    )]));
    let reflexivity = persisted(&mut arena, &reflexivity);
    let reflexive = arena.value_type_path(outer, duplicate, duplicate);
    check_closed_value(&mut arena, reflexivity, reflexive).expect("ap of a higher-order λ");

    // Two λs that pair their argument with `not ∘ not` and with `id`: the
    // output relates the arguments by the premise and the closed halves by
    // the first-order funext, nested.
    let nested = higher(&mut arena, &boolean, (boolean.double, boolean.identity), [
        (boolean.truth, boolean.truth),
        (boolean.falsity, boolean.falsity),
    ]);
    let nested = persisted(&mut arena, &nested);
    let with_double = paired_with(&mut arena, boolean.double);
    let with_identity = paired_with(&mut arena, boolean.identity);
    let identity_output = arena.value_tuple(&[second, boolean.identity]);
    let proof = arena.value_tuple(&[premise, nested]);
    let double_output = arena.value_tuple(&[first, boolean.double]);
    let funext = HigherEvaluation(Vec::from([pointwise(
        &mut arena,
        &context,
        (with_double, with_identity),
        (first, second),
        (double_output, identity_output),
        proof,
    )]));
    let funext = persisted(&mut arena, &funext);
    let extensional = arena.value_type_path(outer, with_double, with_identity);
    check_closed_value(&mut arena, funext, extensional).expect("funext at a higher-order domain");

    // Pairing with `not` instead is not pointwise equal to pairing with `id`:
    // the nested evaluation refuses at its first component.
    let with_not = paired_with(&mut arena, boolean.not);
    let not_output = arena.value_tuple(&[first, boolean.not]);
    let wrong = HigherEvaluation(Vec::from([pointwise(
        &mut arena,
        &context,
        (with_not, with_identity),
        (first, second),
        (not_output, identity_output),
        proof,
    )]));
    let wrong = persisted(&mut arena, &wrong);
    let negated = arena.value_type_path(outer, with_not, with_identity);
    assert!(matches!(
        check_closed_value(&mut arena, wrong, negated),
        Err(KernelError::Identity(IdentityError::Evaluation {
            component: Component(0),
            side: EvaluationSide::Left,
            ..
        }))
    ));
}

/// Persist quantified steps as the kernel node's two payloads.
///
/// # Specification
/// trivial.
fn quantified(
    arena: &mut TermArena,
    steps: &[Quantified],
) -> ValueId
{
    let mut words = Vec::new();
    let mut children = Vec::new();
    for step in steps {
        match *step {
            Quantified::Return {
                ref left,
                ref right,
                proof,
            } => {
                words.push(QuantifiedStep::Return(EvaluationDialogues {
                    left: left.dialogue.0.iter().copied().map(erase).collect(),
                    right: right.dialogue.0.iter().copied().map(erase).collect(),
                }));
                children.extend([left.value, right.value, proof]);
            },
            Quantified::Apply {
                fibre,
                ref left,
                ref right,
            } => {
                words.push(QuantifiedStep::Apply {
                    fibre,
                    dialogues: EvaluationDialogues {
                        left: left.dialogue.0.iter().copied().map(erase).collect(),
                        right: right.dialogue.0.iter().copied().map(erase).collect(),
                    },
                });
                children.extend([left.normal, right.normal]);
            },
        }
    }
    arena.value_quantified_evaluation(Arc::from(words), Box::from(children))
}

/// The generic higher-order pattern's telescope at the thunk type `inner`:
/// `f₀ f₁ : inner, p : Path(inner, f₀, f₁)`, with `f₀`, `f₁` beneath it.
///
/// # Specification
/// trivial.
fn generic(
    arena: &mut TermArena,
    inner: ValueTypeId,
) -> ([ValueTypeId; 3], (ValueId, ValueId))
{
    let [first, second, premise] =
        [2_u32, 1, 0].map(|index| arena.value_variable(DeBruijnIndex::from(index)));
    let identity_type = arena.value_type_path(inner, second, premise);
    ([inner, inner, identity_type], (first, second))
}

/// `force f a`, as the kernel writes an application.
///
/// # Specification
/// trivial.
fn forced(
    arena: &mut TermArena,
    function: ValueId,
    argument: ValueId,
) -> ComputationId
{
    let forced = arena.computation_force(function);
    arena.computation_application(forced, argument)
}

/// A closed normal form: `body` beneath one lambda per telescope entry.
///
/// # Specification
/// trivial.
fn closed(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    body: ComputationId,
) -> ValueId
{
    let mut body = body;
    for _ in context {
        body = arena.computation_lambda(body);
    }
    arena.value_thunk(body)
}

/// The two return steps closing a branch at each Bool output, both sides
/// returning the same constructor with unit evidence.
///
/// # Specification
/// trivial.
fn bool_returns(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    boolean: &crate::identity_recursion::function_fixtures::Boolean,
) -> [Quantified; 2]
{
    let unit = arena.value_unit();
    [boolean.truth, boolean.falsity].map(|output| {
        let returned = arena.computation_return(output);
        Quantified::Return {
            left: evaluation(arena, context, returned, output),
            right: evaluation(arena, context, returned, output),
            proof: unit,
        }
    })
}

#[test]
fn a_quantified_evaluation_replays_under_the_quantifier()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let inner = boolean.function;
    let outer = thunk_type(&mut arena, inner, boolean.ty);
    let (context, (first, second)) = generic(&mut arena, inner);
    let fibre = DeBruijnIndex::from(0_u32);

    // `λf. f(true)` relates to itself: both sides stick at their own function
    // applied to `true`, and each Bool output returns on both.
    let apply_true = apply_to(&mut arena, boolean.truth);
    let stuck = |arena: &mut TermArena, function: ValueId| {
        let claim = forced(arena, apply_true, function);
        let body = forced(arena, function, boolean.truth);
        let normal = closed(arena, &context, body);
        normal_form(arena, &context, claim, normal)
    };
    let application = Quantified::Apply {
        fibre,
        left: stuck(&mut arena, first),
        right: stuck(&mut arena, second),
    };
    let [on_true, on_false] = bool_returns(&mut arena, &context, &boolean);
    let steps = [application.clone(), on_true.clone(), on_false.clone()];
    let reflexivity = quantified(&mut arena, &steps);
    let reflexive = arena.value_type_path(outer, apply_true, apply_true);
    check_closed_value(&mut arena, reflexivity, reflexive)
        .expect("λf. f(true) under the quantifier");
    assert_eq!(
        synth_closed_value(&mut arena, reflexivity),
        Err(KernelError::NotInferable {
            form: NonInferableForm::HigherEvaluation
        })
    );

    // Its bind form `λf. x ← f(true); return x` relates to it: the left side
    // sticks with a continuation, resumed at each output.
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let resumed = arena.computation_return(bound);
    let function = arena.value_variable(DeBruijnIndex::from(0_u32));
    let call = forced(&mut arena, function, boolean.truth);
    let body = arena.computation_bind(call, resumed);
    let body = arena.computation_lambda(body);
    let bind_true = arena.value_thunk(body);
    let claim = forced(&mut arena, bind_true, first);
    let call = forced(&mut arena, first, boolean.truth);
    let body = arena.computation_bind(call, resumed);
    let normal = closed(&mut arena, &context, body);
    let left = normal_form(&mut arena, &context, claim, normal);
    let Quantified::Apply { ref right, .. } = application
    else {
        panic!("an application step")
    };
    let steps = [
        Quantified::Apply {
            fibre,
            left,
            right: right.clone(),
        },
        on_true,
        on_false,
    ];
    let funext = quantified(&mut arena, &steps);
    let extensional = arena.value_type_path(outer, bind_true, apply_true);
    check_closed_value(&mut arena, funext, extensional).expect("the bind form relates");

    // `λf. x ← f(true); f(x)` applies its argument twice: each output of the
    // first application opens the second at that output.
    let function = arena.value_variable(DeBruijnIndex::from(1_u32));
    let again = forced(&mut arena, function, bound);
    let function = arena.value_variable(DeBruijnIndex::from(0_u32));
    let call = forced(&mut arena, function, boolean.truth);
    let body = arena.computation_bind(call, again);
    let body = arena.computation_lambda(body);
    let twice = arena.value_thunk(body);
    // Beneath the bound result, the side's function sits one index further.
    let [under_first, under_second] =
        [3_u32, 2].map(|index| arena.value_variable(DeBruijnIndex::from(index)));
    let first_call = |arena: &mut TermArena, function: ValueId, beneath: ValueId| {
        let claim = forced(arena, twice, function);
        let call = forced(arena, function, boolean.truth);
        let again = forced(arena, beneath, bound);
        let body = arena.computation_bind(call, again);
        let normal = closed(arena, &context, body);
        normal_form(arena, &context, claim, normal)
    };
    let second_call = |arena: &mut TermArena, function: ValueId, output: ValueId| {
        let claim = forced(arena, function, output);
        let normal = closed(arena, &context, claim);
        normal_form(arena, &context, claim, normal)
    };
    let mut steps = Vec::from([Quantified::Apply {
        fibre,
        left: first_call(&mut arena, first, under_first),
        right: first_call(&mut arena, second, under_second),
    }]);
    for output in [boolean.truth, boolean.falsity] {
        steps.push(Quantified::Apply {
            fibre,
            left: second_call(&mut arena, first, output),
            right: second_call(&mut arena, second, output),
        });
        steps.extend(bool_returns(&mut arena, &context, &boolean));
    }
    let nested = quantified(&mut arena, &steps);
    let reflexive = arena.value_type_path(outer, twice, twice);
    check_closed_value(&mut arena, nested, reflexive).expect("a body applying its argument twice");
}

#[test]
fn a_quantified_evaluation_refuses_what_it_cannot_relate()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let inner = boolean.function;
    let outer = thunk_type(&mut arena, inner, boolean.ty);
    let (context, (first, second)) = generic(&mut arena, inner);
    let fibre = DeBruijnIndex::from(0_u32);
    let stuck_at = |arena: &mut TermArena, closure: ValueId, function: ValueId, input: ValueId| {
        let claim = forced(arena, closure, function);
        let body = forced(arena, function, input);
        let normal = closed(arena, &context, body);
        normal_form(arena, &context, claim, normal)
    };
    let apply_true = apply_to(&mut arena, boolean.truth);
    let apply_false = apply_to(&mut arena, boolean.falsity);
    let [on_true, on_false] = bool_returns(&mut arena, &context, &boolean);

    // `λf. f(true)` and `λf. f(false)` apply at different inputs.
    let left = stuck_at(&mut arena, apply_true, first, boolean.truth);
    let right = stuck_at(&mut arena, apply_false, second, boolean.falsity);
    let differing = quantified(&mut arena, &[
        Quantified::Apply { fibre, left, right },
        on_true.clone(),
        on_false.clone(),
    ]);
    let distinct = arena.value_type_path(outer, apply_true, apply_false);
    assert_eq!(
        check_closed_value(&mut arena, differing, distinct),
        Err(KernelError::Identity(IdentityError::QuantifiedStep {
            component: Component(0)
        }))
    );

    // A fibre naming a function binder is not a premise, and a step past the
    // tree is outside the coverage.
    let left = stuck_at(&mut arena, apply_true, first, boolean.truth);
    let right = stuck_at(&mut arena, apply_true, second, boolean.truth);
    let misplaced = quantified(&mut arena, &[
        Quantified::Apply {
            fibre: DeBruijnIndex::from(1_u32),
            left: left.clone(),
            right: right.clone(),
        },
        on_true.clone(),
        on_false.clone(),
    ]);
    let reflexive = arena.value_type_path(outer, apply_true, apply_true);
    assert_eq!(
        check_closed_value(&mut arena, misplaced, reflexive),
        Err(KernelError::Identity(IdentityError::QuantifiedStep {
            component: Component(0)
        }))
    );
    let extra = quantified(&mut arena, &[
        Quantified::Apply { fibre, left, right },
        on_true,
        on_false.clone(),
        on_false,
    ]);
    assert_eq!(
        check_closed_value(&mut arena, extra, reflexive),
        Err(KernelError::Identity(IdentityError::Coverage))
    );

    // `λh. h(not)` applies a function whose own domain is a function: the
    // fragment boundary refuses it by name before any input is compared.
    let higher = thunk_type(&mut arena, inner, boolean.ty);
    let outermost = thunk_type(&mut arena, higher, boolean.ty);
    let (context, (first, second)) = generic(&mut arena, higher);
    let apply_not = apply_to(&mut arena, boolean.not);
    let stuck_at = |arena: &mut TermArena, function: ValueId| {
        let claim = forced(arena, apply_not, function);
        let body = forced(arena, function, boolean.not);
        let normal = closed(arena, &context, body);
        normal_form(arena, &context, claim, normal)
    };
    let application = Quantified::Apply {
        fibre,
        left: stuck_at(&mut arena, first),
        right: stuck_at(&mut arena, second),
    };
    let [on_true, on_false] = bool_returns(&mut arena, &context, &boolean);
    let boundary = quantified(&mut arena, &[application, on_true, on_false]);
    let reflexive = arena.value_type_path(outermost, apply_not, apply_not);
    assert_eq!(
        check_closed_value(&mut arena, boundary, reflexive),
        Err(KernelError::Identity(IdentityError::HigherOrderDomain {
            component: Component(0)
        }))
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

/// Bool's conjunction as a monoid.
struct Conjunction
{
    /// The carrier, Bool.
    ty: ValueTypeId,
    /// Bool's `false`, absorbing.
    falsity: ValueId,
    /// The neutral element's position.
    neutral: ConstantIndex,
    /// The multiplication's position.
    mul: ConstantIndex,
}

/// Whether a fixture's constant unfolds: admitted as a definition, or as an
/// axiom of the same type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Admitted
{
    /// A definition the reading may unfold.
    Defined,
    /// An axiom, opaque to every reading.
    Assumed,
}

/// Which unit law a fixture states.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unit
{
    /// `mul(neutral, x) = x`.
    Left,
    /// `mul(x, neutral) = x`.
    Right,
}

/// Admit `staged`, recording it for the artifact once it is admitted.
///
/// # Specification
/// trivial.
fn admit(
    environment: &mut Environment,
    declarations: &mut Vec<MarkedDeclaration>,
    staged: StagedDeclaration,
) -> Result<CheckedId, KernelError>
{
    let marked = MarkedDeclaration::new(AdmissionMark::Checked, staged.declaration().clone());
    let admitted = environment.add_decl(staged)?;
    declarations.push(marked);
    Ok(admitted)
}

/// Admit Bool's conjunction: `neutral : Bool = true`, a definition or an axiom
/// as `neutral` says, then `mul : U(Bool → Bool → F Bool) = thunk { λa. λb.
/// case a { true ⇒ return b ; false ⇒ return false } }`.
///
/// # Specification
/// trivial.
fn conjunction(
    environment: &mut Environment,
    declarations: &mut Vec<MarkedDeclaration>,
    neutral: Admitted,
) -> Conjunction
{
    let mut staging = environment.stage();
    let boolean = boolean(staging.arena());
    let declaration = match neutral {
        Admitted::Defined => staging.def(LevelSignature::monomorphic(), boolean.ty, boolean.truth),
        Admitted::Assumed => staging.axiom(LevelSignature::monomorphic(), boolean.ty),
    };
    let neutral = admit(environment, declarations, declaration)
        .expect("the neutral element")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let returns = arena.comp_type_returner(boolean.ty);
    let inner = arena.comp_type_arrow(boolean.ty, returns);
    let outer = arena.comp_type_arrow(boolean.ty, inner);
    let declared = arena.value_type_thunk(outer);
    // Under `λa. λb` the scrutinee `a` is index 1; under a branch's payload
    // binder, `b` is index 1 too.
    let scrutinee = arena.value_variable(DeBruijnIndex::from(1_u32));
    let second = arena.value_variable(DeBruijnIndex::from(1_u32));
    let on_true = arena.computation_return(second);
    let on_false = arena.computation_return(boolean.falsity);
    let body = arena.computation_case(scrutinee, &[on_true, on_false]);
    let body = arena.computation_lambda(body);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
    let mul = admit(environment, declarations, declaration)
        .expect("conjunction")
        .position();
    Conjunction {
        ty: boolean.ty,
        falsity: boolean.falsity,
        neutral,
        mul,
    }
}

/// The returned endpoint `⟨force head arguments…⟩`.
///
/// # Specification
/// trivial.
fn applied(
    arena: &mut TermArena,
    head: ConstantIndex,
    arguments: &[ValueId],
) -> ValueId
{
    let head = arena.value_constant(head);
    let mut computation = arena.computation_force(head);
    for &argument in arguments {
        computation = arena.computation_application(computation, argument);
    }
    arena.value_returned(computation)
}

/// Stage `law : U(Π x : Bool. F Path(Bool, ⟨mul a b⟩, x)) = thunk { λx.
/// return here(⟨mul a b⟩) }` at `(a, b) = (neutral, x)` for the left unit, or
/// at `(x, neutral)` for the right, the `here` relating its point to `x` by
/// `dialogue`.
///
/// # Specification
/// trivial.
fn unit_law(
    environment: &mut Environment,
    monoid: &Conjunction,
    unit: Unit,
    dialogue: &[ConversionDecision<()>],
) -> StagedDeclaration
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let neutral = arena.value_constant(monoid.neutral);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let arguments = match unit {
        Unit::Left => [neutral, bound],
        Unit::Right => [bound, neutral],
    };
    let endpoint = applied(arena, monoid.mul, &arguments);
    let identity = arena.value_type_path(monoid.ty, endpoint, bound);
    let returns = arena.comp_type_returner(identity);
    let family = arena.comp_type_pi(monoid.ty, returns);
    let declared = arena.value_type_thunk(family);
    let here = arena.value_here_relating(
        endpoint,
        Arc::new(EndpointDialogues {
            left: Vec::new(),
            right: dialogue.to_vec(),
        }),
    );
    let body = arena.computation_return(here);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    staging.def(LevelSignature::monomorphic(), declared, body)
}

/// The dialogue relating `⟨mul neutral x⟩` to `x`: `mul` unfolds on the left,
/// β binds both arguments, then `neutral` unfolds under the case and the case
/// selects `x`.
const LEFT_UNIT: [ConversionDecision<()>; 4] = [
    ConversionDecision::Unfold { constant: () },
    ConversionDecision::ReduceLeft { redex: () },
    ConversionDecision::Unfold { constant: () },
    ConversionDecision::ReduceLeft { redex: () },
];

/// Admit a decoded artifact's declarations, in order, into a fresh
/// environment that starts from the artifact's arena.
///
/// # Specification
/// trivial.
fn readmit(artifact: &DecodedArtifact) -> Result<Environment, KernelError>
{
    let mut environment = Environment::new();
    for (position, marked) in artifact.declarations().iter().enumerate() {
        let mut staging = environment.stage();
        if position == 0 {
            *staging.arena() = artifact.arena().clone();
        }
        let levels = marked.declaration().levels().clone();
        let staged = match *marked.declaration().content() {
            DeclarationContent::Def { declared, body } => staging
                .def(levels, declared, body)
                .relating(marked.declaration().related().to_vec()),
            DeclarationContent::Axiom { declared } => staging.axiom(levels, declared),
            DeclarationContent::Data { .. } | DeclarationContent::AbstractType { .. } => {
                panic!("the fixture holds definitions and axioms")
            },
        };
        environment.add_decl(staged)?;
    }
    Ok(environment)
}

#[test]
fn a_certificate_with_a_returned_endpoint_decodes_checks_and_replays()
{
    let mut environment = Environment::new();
    let mut declarations = Vec::new();
    let monoid = conjunction(&mut environment, &mut declarations, Admitted::Defined);
    let declaration = unit_law(&mut environment, &monoid, Unit::Left, &LEFT_UNIT);
    let law = admit(&mut environment, &mut declarations, declaration)
        .expect("the endpoint reads as `x` through both definitions");
    assert!(environment.audit(law).axioms().is_empty());

    let bytes = gandr_kernel_term::encode(environment.arena(), &declarations);
    let decoded =
        gandr_kernel_term::decode(bytes.as_image()).expect("the returned endpoint decodes");
    assert_eq!(
        gandr_kernel_term::encode(decoded.arena(), decoded.declarations()),
        bytes
    );
    let readmitted = readmit(&decoded).expect("the decoded law checks");
    assert_eq!(readmitted.entries().len(), 3);

    // The kernel replays the endpoint's reduction over the decoded bodies:
    // `mul` and `neutral` unfold, the case selects `b`, and `x` is returned.
    let declared = decoded
        .declarations()
        .last()
        .map(|marked| marked.declaration().declared_id())
        .expect("the law");
    let arena = decoded.arena();
    let Some(&ValueType::Thunk(family)) = arena.value_type(declared)
    else {
        panic!("the law is a suspended family");
    };
    let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(family)
    else {
        panic!("over Bool");
    };
    let Some(&CompType::Returner(identity)) = arena.comp_type(codomain)
    else {
        panic!("returning an identity");
    };
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(identity)
    else {
        panic!("between the endpoint and `x`");
    };
    assert!(matches!(arena.value(left), Some(&Value::Returned(_))));
    let bodies: Vec<_> = decoded
        .declarations()
        .iter()
        .map(|marked| match *marked.declaration().content() {
            DeclarationContent::Def { body, .. } => Unfoldable::Body(body),
            DeclarationContent::Data { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::AbstractType { .. } => Unfoldable::Opaque,
        })
        .collect();
    let mut arena = decoded.arena().clone();
    let replayed = |arena: &mut TermArena, bodies: Vec<Unfoldable>| {
        read_endpoints(
            arena,
            &Unfoldings::new(bodies),
            &[crate::conv::SetAside::Values(left, right)],
            ReplayBudget::DEFAULT,
        )
    };
    assert_eq!(
        replayed(&mut arena, bodies.clone()),
        EndpointReading::Converts
    );
    // Drop the δ-step at `neutral`: the case stands on an opaque constant and
    // the endpoint stays apart from `x`.
    let mut dropped = bodies;
    if let Some(first) = dropped.first_mut() {
        *first = Unfoldable::Opaque;
    }
    assert_eq!(replayed(&mut arena, dropped), EndpointReading::Apart);

    // Swap the arguments: the case stands on `x` and refuses by name.
    let declaration = unit_law(&mut environment, &monoid, Unit::Right, &LEFT_UNIT);
    assert!(matches!(
        environment.add_decl(declaration),
        Err(KernelError::Identity(IdentityError::EndpointsDiffer {
            side: EndpointSide::Right,
            ..
        }))
    ));
    // Withhold `neutral`'s definition: the case stands on an axiom, so the
    // goal closes apart with the dialogue's second unfolding unread.
    let mut withheld = Environment::new();
    let opaque = conjunction(&mut withheld, &mut Vec::new(), Admitted::Assumed);
    let declaration = unit_law(&mut withheld, &opaque, Unit::Left, &LEFT_UNIT);
    assert_eq!(
        endpoint_refusal(&withheld.add_decl(declaration)),
        Some((
            EndpointSide::Right,
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(2_usize),
            })),
        ))
    );
}

#[test]
fn a_stuck_returned_endpoint_compares_structurally()
{
    // axiom f, g : U(Bool → F Bool) ; under `λx`, `here(⟨f x⟩)` relates
    // `⟨f x⟩` to itself by structure, and neither to `⟨g x⟩` nor to `x`.
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let boolean = boolean(staging.arena());
    let arena = staging.arena();
    let returns = arena.comp_type_returner(boolean.ty);
    let arrow = arena.comp_type_arrow(boolean.ty, returns);
    let suspended = arena.value_type_thunk(arrow);
    let declaration = staging.axiom(LevelSignature::monomorphic(), suspended);
    let f = environment.add_decl(declaration).expect("f").position();
    let staging = environment.stage();
    let declaration = staging.axiom(LevelSignature::monomorphic(), suspended);
    let g = environment.add_decl(declaration).expect("g").position();
    let related = |environment: &mut Environment, right: Option<ConstantIndex>| {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let left = applied(arena, f, &[bound]);
        let right = right.map_or(bound, |head| applied(arena, head, &[bound]));
        let identity = arena.value_type_path(boolean.ty, left, right);
        let returns = arena.comp_type_returner(identity);
        let family = arena.comp_type_pi(boolean.ty, returns);
        let declared = arena.value_type_thunk(family);
        let here = arena.value_here(left);
        let body = arena.computation_return(here);
        let body = arena.computation_lambda(body);
        let body = arena.value_thunk(body);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        environment.add_decl(declaration)
    };
    related(&mut environment, Some(f)).expect("a stuck endpoint relates to itself");
    for right in [Some(g), None] {
        assert!(matches!(
            related(&mut environment, right),
            Err(KernelError::Identity(IdentityError::EndpointsDiffer { .. }))
        ));
    }
}

/// `law : Path(U(Bool → F Bool), ⟨force delay⟩, k) = here(k)` over `def k :
/// U(Bool → F Bool) = thunk { λx. return x }`, `j = k` (a definition, or an
/// axiom in the control) and `def delay : U(F U(Bool → F Bool)) = thunk {
/// return thunk { force j } }`, the `here` relating `k` to `⟨force delay⟩` by
/// `dialogue`. `⟨force delay⟩` reduces to `thunk { force j }`, so relating it
/// to `k` unfolds `j` under the thunk.
///
/// # Specification
/// trivial.
fn delayed_law(
    alias: Admitted,
    dialogue: &[ConversionDecision<()>],
) -> Result<CheckedId, KernelError>
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let boolean = boolean(staging.arena());
    let declaration = staging.def(
        LevelSignature::monomorphic(),
        boolean.function,
        boolean.identity,
    );
    let k = environment.add_decl(declaration)?.position();
    let mut staging = environment.stage();
    let named_k = staging.arena().value_constant(k);
    let declaration = match alias {
        Admitted::Defined => staging.def(LevelSignature::monomorphic(), boolean.function, named_k),
        Admitted::Assumed => staging.axiom(LevelSignature::monomorphic(), boolean.function),
    };
    let j = environment.add_decl(declaration)?.position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let named_j = arena.value_constant(j);
    let forced = arena.computation_force(named_j);
    let inner = arena.value_thunk(forced);
    let returned = arena.computation_return(inner);
    let body = arena.value_thunk(returned);
    let returns = arena.comp_type_returner(boolean.function);
    let declared = arena.value_type_thunk(returns);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
    let delay = environment.add_decl(declaration)?.position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let endpoint = applied(arena, delay, &[]);
    let named_k = arena.value_constant(k);
    let identity = arena.value_type_path(boolean.function, endpoint, named_k);
    let here = arena.value_here_relating(
        named_k,
        Arc::new(EndpointDialogues {
            left: dialogue.to_vec(),
            right: Vec::new(),
        }),
    );
    let declaration = staging.def(LevelSignature::monomorphic(), identity, here);
    environment.add_decl(declaration)
}

/// The dialogue relating `k` to `⟨force delay⟩`: `delay` unfolds on the right
/// and returns its thunk; `k` unfolds on the left; both thunks are forced;
/// then `j` and `k` unfold on the right, under the thunk `delay` returned.
const DELAYED: [ConversionDecision<()>; 10] = [
    ConversionDecision::Unfold { constant: () },
    ConversionDecision::ReduceRight { redex: () },
    ConversionDecision::Unfold { constant: () },
    ConversionDecision::ReduceLeft { redex: () },
    ConversionDecision::Force { thunk: () },
    ConversionDecision::Force { thunk: () },
    ConversionDecision::Unfold { constant: () },
    ConversionDecision::ReduceRight { redex: () },
    ConversionDecision::Unfold { constant: () },
    ConversionDecision::ReduceRight { redex: () },
];

/// The side and replay verdict a reflexivity refusal names, if `admitted` is
/// one.
///
/// # Specification
/// trivial.
fn endpoint_refusal(
    admitted: &Result<CheckedId, KernelError>
) -> Option<(EndpointSide, KernelVerdict)>
{
    match *admitted {
        Err(KernelError::Identity(IdentityError::EndpointsDiffer { side, verdict, .. })) => {
            Some((side, verdict))
        },
        _ => None,
    }
}

#[test]
fn an_endpoint_unfolding_under_a_thunk_replays_its_dialogue()
{
    delayed_law(Admitted::Defined, &DELAYED).expect("the dialogue unfolds `j` under the thunk");
    // No dialogue: the forced conversion unfolds nothing, and the empty
    // dialogue names no unfolding.
    assert_eq!(
        endpoint_refusal(&delayed_law(Admitted::Defined, &[])),
        Some((
            EndpointSide::Left,
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Exhausted)),
        ))
    );
}

#[test]
fn a_dialogue_naming_the_wrong_unfolding_is_refused_by_name()
{
    let refused = |alias: Admitted, dialogue: &[ConversionDecision<()>]| {
        endpoint_refusal(&delayed_law(alias, dialogue))
    };
    let at = |position: usize| {
        Some((
            EndpointSide::Left,
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(position),
            })),
        ))
    };
    // The wrong side: `delay` is the right side's head, not the left's.
    let mut wrong_side = DELAYED;
    if let Some(reduction) = wrong_side.get_mut(1) {
        *reduction = ConversionDecision::ReduceLeft { redex: () };
    }
    assert_eq!(refused(Admitted::Defined, &wrong_side), at(1));
    // The wrong constant: the wire names a constant by its side's head, so
    // the dialogue's unfolding of `j` names an axiom in the control.
    assert_eq!(refused(Admitted::Assumed, &DELAYED), at(6));
    // Fewer unfoldings than the endpoint needs: without `k`'s second
    // unfolding, `force k` stays apart from `λx. return x`.
    let short = DELAYED.get(.. 8).expect("a prefix");
    assert_eq!(
        refused(Admitted::Defined, short),
        Some((
            EndpointSide::Left,
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Exhausted)),
        ))
    );
}

/// Stage `law : Path(U(Bool → F Bool), k, k) = given` over the definitions of
/// [`delayed_law`] and `axiom given : Path(U(Bool → F Bool), ⟨force delay⟩,
/// k)`, every earlier declaration admitted and recorded. The ascription
/// converts the two path types only where `k` converts with `⟨force delay⟩`,
/// which unfolds `j` under a thunk: the shape of a definition whose declared
/// type and body's type state compound endpoints related through a
/// definition's body. Returns the law unadmitted, with `k` and `⟨force
/// delay⟩` minted in its content.
///
/// # Specification
/// trivial.
fn ascribed_law(
    alias: Admitted
) -> Result<
    (
        Environment,
        Vec<MarkedDeclaration>,
        StagedDeclaration,
        [ValueId; 2],
    ),
    KernelError,
>
{
    let mut environment = Environment::new();
    let mut declarations = Vec::new();
    let mut staging = environment.stage();
    let boolean = boolean(staging.arena());
    let declaration = staging.def(
        LevelSignature::monomorphic(),
        boolean.function,
        boolean.identity,
    );
    let k = admit(&mut environment, &mut declarations, declaration)?.position();
    let mut staging = environment.stage();
    let named_k = staging.arena().value_constant(k);
    let declaration = match alias {
        Admitted::Defined => staging.def(LevelSignature::monomorphic(), boolean.function, named_k),
        Admitted::Assumed => staging.axiom(LevelSignature::monomorphic(), boolean.function),
    };
    let j = admit(&mut environment, &mut declarations, declaration)?.position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let named_j = arena.value_constant(j);
    let forced = arena.computation_force(named_j);
    let inner = arena.value_thunk(forced);
    let returned = arena.computation_return(inner);
    let body = arena.value_thunk(returned);
    let returns = arena.comp_type_returner(boolean.function);
    let declared = arena.value_type_thunk(returns);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
    let delay = admit(&mut environment, &mut declarations, declaration)?.position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let endpoint = applied(arena, delay, &[]);
    let named_k = arena.value_constant(k);
    let stated = arena.value_type_path(boolean.function, endpoint, named_k);
    let declaration = staging.axiom(LevelSignature::monomorphic(), stated);
    let given = admit(&mut environment, &mut declarations, declaration)?.position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let named_k = arena.value_constant(k);
    let endpoint = applied(arena, delay, &[]);
    let diagonal = arena.value_type_path(boolean.function, named_k, named_k);
    let body = arena.value_constant(given);
    let law = staging.def(LevelSignature::monomorphic(), diagonal, body);
    Ok((environment, declarations, law, [named_k, endpoint]))
}

/// The pair and replay verdict a relation refusal names, if `admitted` is
/// one.
///
/// # Specification
/// trivial.
fn relation_refusal(admitted: &Result<CheckedId, KernelError>) -> Option<KernelVerdict>
{
    match *admitted {
        Err(KernelError::Identity(IdentityError::RelatedEndpointsDiffer { verdict, .. })) => {
            Some(verdict)
        },
        _ => None,
    }
}

#[test]
fn a_definition_relating_compound_endpoints_admits_274()
{
    // Without a relation the forced reading leaves `k` apart from `⟨force
    // delay⟩`: the refusal the ascription met before definitions carried
    // their dialogues.
    let (mut environment, _, law, _) = ascribed_law(Admitted::Defined).expect("the fixture");
    assert!(matches!(
        environment.add_decl(law),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    // A relation between other terms is not read: matching is by content.
    let (mut environment, _, law, [_, endpoint]) =
        ascribed_law(Admitted::Defined).expect("the fixture");
    let elsewhere = law.relating(alloc::vec![RelatedEndpoints {
        left: endpoint,
        right: endpoint,
        dialogue: DELAYED.to_vec(),
    }]);
    assert!(matches!(
        environment.add_decl(elsewhere),
        Err(KernelError::ValueTypeMismatch(_))
    ));
    // The relation the producer's conversion kept admits the law, and crosses
    // the wire with it.
    let (mut environment, mut declarations, law, [k, endpoint]) =
        ascribed_law(Admitted::Defined).expect("the fixture");
    let relation = RelatedEndpoints {
        left: k,
        right: endpoint,
        dialogue: DELAYED.to_vec(),
    };
    let law = law.relating(alloc::vec![relation]);
    admit(&mut environment, &mut declarations, law)
        .expect("the dialogue unfolds `j` under the thunk");
    let bytes = gandr_kernel_term::encode(environment.arena(), &declarations);
    let decoded = gandr_kernel_term::decode(bytes.as_image()).expect("the relation decodes");
    let readmitted = Environment::replay(decoded.arena().clone(), decoded.declarations())
        .expect("the decoded law replays its relation");
    assert_eq!(readmitted.entries().len(), 5);
    let mut stripped = decoded.declarations().to_vec();
    if let Some(last) = stripped.last_mut() {
        *last =
            MarkedDeclaration::new(last.mark(), last.declaration().clone().relating(Vec::new()));
    }
    let refusal = Environment::replay(decoded.arena().clone(), &stripped)
        .expect_err("the law without its relation is refused");
    assert_eq!(refusal.position(), ConstantIndex::from(4_usize));
    assert!(matches!(
        refusal.error(),
        &KernelError::ValueTypeMismatch(_)
    ));
}

#[test]
fn a_relation_stated_the_other_way_round_admits()
{
    // A relation matches the set-aside pair in either orientation; its
    // dialogue relates the relation's own sides, so the mirror of
    // [`DELAYED`] relates `⟨force delay⟩` to `k`.
    let mirrored = DELAYED.map(|decision| {
        if let ConversionDecision::ReduceLeft { redex } = decision {
            ConversionDecision::ReduceRight { redex }
        }
        else if let ConversionDecision::ReduceRight { redex } = decision {
            ConversionDecision::ReduceLeft { redex }
        }
        else {
            decision
        }
    });
    let (mut environment, mut declarations, law, [k, endpoint]) =
        ascribed_law(Admitted::Defined).expect("the fixture");
    let law = law.relating(alloc::vec![RelatedEndpoints {
        left: endpoint,
        right: k,
        dialogue: mirrored.to_vec(),
    }]);
    admit(&mut environment, &mut declarations, law)
        .expect("the reversed relation is the same relation");
}

#[test]
fn a_pair_s_components_stop_at_a_body_naming_its_own_position()
{
    // An unchecked log may hold a definition whose body names itself; the
    // δ-walk unfolds only strictly earlier positions, so it stops and
    // projects rather than unfold the same body forever.
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = arena.value_type_unit();
    let itself = arena.value_constant(ConstantIndex::from(0_usize));
    let declaration = staging.def(LevelSignature::monomorphic(), declared, itself);
    environment.add_decl_unchecked(declaration);
    let entries = environment.entries().to_vec();
    let mut arena = environment.arena().clone();
    let itself = arena.value_constant(ConstantIndex::from(0_usize));
    let components = super::pair_components(&mut arena, &entries, itself);
    for (index, component) in components.into_iter().enumerate() {
        let Some(&Value::Returned(projected)) = arena.value(component)
        else {
            panic!("component {index} is a returned projection");
        };
        assert_eq!(
            arena.computation(projected),
            Some(&Computation::TupleProjection(
                itself,
                gandr_kernel_term::Component::from(index)
            ))
        );
    }
}

#[test]
fn a_quantified_evaluation_refuses_either_open_endpoint()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit_type);
    let arrow = arena.comp_type_arrow(unit_type, returns);
    let domain = arena.value_type_thunk(arrow);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let constant = arena.computation_lambda(returned);
    let closed = arena.value_thunk(constant);
    let open = arena.value_variable(DeBruijnIndex::from(0_u32));
    for (left, right) in [(open, closed), (closed, open)] {
        let expected = arena.value_type_path(domain, left, right);
        assert_eq!(
            super::quantified_obligations(&mut arena, &Unfoldings::default(), expected, &[], &[])
                .err(),
            Some(KernelError::Identity(IdentityError::OpenFunctions)),
            "one open endpoint is enough to refuse"
        );
    }
}

#[test]
fn a_corrupted_relation_is_refused_by_name()
{
    let refused = |alias: Admitted, dialogue: &[ConversionDecision<()>]| {
        let (mut environment, _, law, [k, endpoint]) = ascribed_law(alias).expect("the fixture");
        let law = law.relating(alloc::vec![RelatedEndpoints {
            left: k,
            right: endpoint,
            dialogue: dialogue.to_vec(),
        }]);
        relation_refusal(&environment.add_decl(law))
    };
    let at = |position: usize| {
        Some(KernelVerdict::Declined(ReplayDecline::Refused(
            ReplayRefusal::Inapplicable {
                at: TracePosition::from(position),
            },
        )))
    };
    // The wrong side: `delay` is the right side's head, not the left's.
    let mut wrong_side = DELAYED;
    if let Some(reduction) = wrong_side.get_mut(1) {
        *reduction = ConversionDecision::ReduceLeft { redex: () };
    }
    assert_eq!(refused(Admitted::Defined, &wrong_side), at(1));
    // A decision pointing at an unrelated definition: in the control `j` is
    // an axiom, so the dialogue's unfolding of it has nothing to unfold.
    assert_eq!(refused(Admitted::Assumed, &DELAYED), at(6));
    // The empty dialogue names no unfolding.
    assert_eq!(
        refused(Admitted::Defined, &[]),
        Some(KernelVerdict::Declined(ReplayDecline::Refused(
            ReplayRefusal::Exhausted
        )))
    );
}

#[test]
fn a_returned_endpoint_over_a_non_returner_is_refused_by_name()
{
    // `⟨mul neutral⟩` stops at a function: it returns nothing to stand for.
    // An impure endpoint has no kernel image to refuse: a kernel returner
    // carries no effect row.
    let mut environment = Environment::new();
    let monoid = conjunction(&mut environment, &mut Vec::new(), Admitted::Defined);
    let mut staging = environment.stage();
    let arena = staging.arena();
    let neutral = arena.value_constant(monoid.neutral);
    let partial = applied(arena, monoid.mul, &[neutral]);
    let identity = arena.value_type_path(monoid.ty, partial, partial);
    let here = arena.value_here(partial);
    let declaration = staging.def(LevelSignature::monomorphic(), identity, here);
    let Err(error) = environment.add_decl(declaration)
    else {
        panic!("a returned endpoint over a function admitted");
    };
    assert!(matches!(
        error,
        KernelError::Identity(IdentityError::ReturnedNonReturner(_))
    ));
    assert_eq!(error.to_string(), "a returned endpoint over a non-returner");
}

#[test]
fn a_returned_endpoint_reads_at_a_mode_switch()
{
    // def switched : U(Π x : Bool. Path(Bool, ⟨mul a x⟩, x) → F Path(Bool, x, x))
    //   = thunk { λx. λp. return p } ;
    // checks at `a = neutral`, where the endpoint reads as `x`, and refuses at
    // `a = false`, where it reads as `false`.
    let mut environment = Environment::new();
    let monoid = conjunction(&mut environment, &mut Vec::new(), Admitted::Defined);
    let switched = |environment: &mut Environment, unit: bool| {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let first = if unit {
            arena.value_constant(monoid.neutral)
        }
        else {
            monoid.falsity
        };
        let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
        let endpoint = applied(arena, monoid.mul, &[first, bound]);
        let given = arena.value_type_path(monoid.ty, endpoint, bound);
        let diagonal = arena.value_type_path(monoid.ty, bound, bound);
        let returns = arena.comp_type_returner(diagonal);
        let arrow = arena.comp_type_arrow(given, returns);
        let family = arena.comp_type_pi(monoid.ty, arrow);
        let declared = arena.value_type_thunk(family);
        let path = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(path);
        let body = arena.computation_lambda(body);
        let body = arena.computation_lambda(body);
        let body = arena.value_thunk(body);
        let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
        environment.add_decl(declaration)
    };
    switched(&mut environment, true).expect("the given path's endpoint reads as `x`");
    assert!(matches!(
        switched(&mut environment, false),
        Err(KernelError::ValueTypeMismatch(_))
    ));
}

#[test]
fn a_returned_endpoint_replays_as_its_computation()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let returned = arena.computation_return(boolean.truth);
    let endpoint = arena.value_returned(returned);

    // A value goal holding a returned endpoint replays as its computation.
    let replayed = |arena: &mut TermArena, right: ValueId| {
        crate::replay::replay(
            arena,
            &Unfoldings::default(),
            ReplaySides::Values(endpoint, right),
            EngineClaim::Convertible,
            core::iter::empty(),
            ReplayBudget::DEFAULT,
        )
    };
    assert_eq!(
        replayed(&mut arena, boolean.truth),
        KernelVerdict::Convertible
    );
    assert_ne!(
        replayed(&mut arena, boolean.falsity),
        KernelVerdict::Convertible
    );
    // Against another returned endpoint, the two computations meet.
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let passed = arena.computation_return(bound);
    let sequenced = arena.computation_bind(returned, passed);
    let other = arena.value_returned(sequenced);
    assert_eq!(replayed(&mut arena, other), KernelVerdict::Convertible);

    // A case over it binds what its computation returns.
    let on_true = arena.computation_return(boolean.falsity);
    let on_false = arena.computation_return(boolean.truth);
    let negated = arena.computation_case(endpoint, &[on_true, on_false]);
    assert_eq!(
        computes(&mut arena, negated, on_true),
        KernelVerdict::Convertible
    );
    assert_ne!(
        computes(&mut arena, negated, on_false),
        KernelVerdict::Convertible
    );
    // A force over it runs the thunk its computation returns.
    let suspended = arena.value_thunk(on_true);
    let returns_thunk = arena.computation_return(suspended);
    let thunked = arena.value_returned(returns_thunk);
    let forced = arena.computation_force(thunked);
    assert_eq!(
        computes(&mut arena, forced, on_true),
        KernelVerdict::Convertible
    );
    assert_ne!(
        computes(&mut arena, forced, on_false),
        KernelVerdict::Convertible
    );
}

#[test]
fn a_returned_endpoint_a_computation_returns_replays_as_its_computation()
{
    let mut arena = TermArena::new();
    let function = arena.value_variable(DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(function);
    let endpoint = arena.value_returned(forced);
    let returns_endpoint = arena.computation_return(endpoint);
    let other_function = arena.value_variable(DeBruijnIndex::from(1_u32));
    let other_forced = arena.computation_force(other_function);
    let converted = |arena: &mut TermArena, left, right| {
        crate::replay::convert(
            arena,
            &Unfoldings::default(),
            ReplaySides::Computations(left, right),
            ReplayBudget::DEFAULT,
        )
    };

    // `return (returned (force f))` is `force f`, on either side.
    assert_eq!(
        converted(&mut arena, returns_endpoint, forced),
        KernelVerdict::Convertible
    );
    assert_eq!(
        converted(&mut arena, forced, returns_endpoint),
        KernelVerdict::Convertible
    );
    // And not `force g`.
    assert_ne!(
        converted(&mut arena, returns_endpoint, other_forced),
        KernelVerdict::Convertible
    );
}

/// A suspended function of dependent type: `body` under one lambda per
/// domain, typed by the Pi chain over `domains`, the first outermost, each
/// domain standing under the binders before it, returning `result`.
///
/// # Specification
/// trivial.
fn function(
    arena: &mut TermArena,
    domains: &[ValueTypeId],
    result: ValueTypeId,
    body: ComputationId,
) -> (ValueId, ValueTypeId)
{
    let mut ty = arena.comp_type_returner(result);
    let mut term = body;
    for &domain in domains.iter().rev() {
        ty = arena.comp_type_pi(domain, ty);
        term = arena.computation_lambda(term);
    }
    (arena.value_thunk(term), arena.value_type_thunk(ty))
}

#[test]
fn a_dependent_motive_replays_its_substitution_law()
{
    // λa b : Bool. λp : Path(Bool, a, b). λz₀ z₁ : Bool.
    // λq : Path(Bool, z₀, z₁). λv : Path(Bool, a, z₀).
    //   transport((y : Bool, z : Bool) => Path(Bool, y, z), p, z₀, q, v)
    //   : F Path(Bool, b, z₁)
    // The path's endpoints instantiate the outer entry and the identity
    // over it the inner one, each by one substitution.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    let between = |arena: &mut TermArena, left: u32, right: u32| {
        let left = var(arena, left);
        let right = var(arena, right);
        arena.value_type_path(boolean.ty, left, right)
    };
    let pointed = between(&mut arena, 1, 0);
    let returns = arena.comp_type_returner(pointed);
    let inner = arena.comp_type_pi(boolean.ty, returns);
    let motive = arena.comp_type_pi(boolean.ty, inner);
    let [path, start, over, value] = [4, 3, 1, 0].map(|index| var(&mut arena, index));
    let transport = arena.computation_telescope_transport(motive, path, start, over, value);
    let carrier = between(&mut arena, 1, 0);
    let fibre = between(&mut arena, 1, 0);
    let input = between(&mut arena, 5, 2);
    let domains = [
        boolean.ty, boolean.ty, carrier, boolean.ty, boolean.ty, fibre, input,
    ];

    let target = between(&mut arena, 5, 2);
    let (term, declared) = function(&mut arena, &domains, target, transport);
    check_closed_value(&mut arena, term, declared).expect("the body at the target pair");

    // Neither the source pair nor the entries exchanged is the result type.
    for (left, right) in [(6, 3), (2, 5)] {
        let wrong = between(&mut arena, left, right);
        let (term, declared) = function(&mut arena, &domains, wrong, transport);
        assert!(matches!(
            check_closed_value(&mut arena, term, declared),
            Err(KernelError::ComputationTypeMismatch(_))
        ));
    }

    // A path over another carrier than the motive's first entry is refused.
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let elsewhere = arena.value_type_path(unit_type, unit, unit);
    let mut domains = domains;
    domains[2] = elsewhere;
    let (term, declared) = function(&mut arena, &domains, target, transport);
    let refused = check_closed_value(&mut arena, term, declared);
    assert!(
        matches!(refused, Err(KernelError::ValueTypeMismatch(_))),
        "{refused:?}"
    );
    // A carrier that is the first entry only once its returned code runs is
    // read through it: `El(⟨return 'Bool⟩)` is Bool.
    let code = arena.value_quote(boolean.ty);
    let returned = arena.computation_return(code);
    let returned = arena.value_returned(returned);
    let read = arena.value_type_element(returned, Level::zero());
    let left = var(&mut arena, 1);
    let right = var(&mut arena, 0);
    domains[2] = arena.value_type_path(read, left, right);
    let (term, declared) = function(&mut arena, &domains, target, transport);
    let admitted = check_closed_value(&mut arena, term, declared);
    assert!(admitted.is_ok(), "{admitted:?}");
}

#[test]
fn a_one_entry_telescope_motive_is_refused_by_its_shape()
{
    // A motive with one entry is a one-binder transport's, not a telescope.
    // λp : Path(Bool, T, T). transport(y : Bool => Bool, p, T, p, T)
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let returns = arena.comp_type_returner(boolean.ty);
    let motive = arena.comp_type_pi(boolean.ty, returns);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let transport =
        arena.computation_telescope_transport(motive, path, boolean.truth, path, boolean.truth);
    let reflexive = arena.value_type_path(boolean.ty, boolean.truth, boolean.truth);
    let (term, declared) = function(&mut arena, &[reflexive], boolean.ty, transport);
    assert!(matches!(
        check_closed_value(&mut arena, term, declared),
        Err(KernelError::ComputationShapeMismatch {
            expected: ExpectedComputationShape::Telescope,
            ..
        })
    ));
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    let here = arena.value_here(boolean.truth);
    assert_eq!(
        telescope_beta(&mut arena, &mut table, &mut memo, TelescopeStep {
            motive,
            path: here,
            start: boolean.truth,
            over: here,
            value: boolean.truth,
        }),
        Ok(Reduction::Stuck)
    );
}

#[test]
fn telescope_transport_along_here_reduces()
{
    // In `(y : Bool, z : Bool) => Path(Bool, y, z)`: `here` along both
    // identities returns the value; `here` along the path alone transports
    // in the fibre `z. Path(Bool, T, z)`; a neutral path sticks.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
    let inner = arena.value_variable(DeBruijnIndex::from(0_u32));
    let pointed = arena.value_type_path(boolean.ty, outer, inner);
    let returns = arena.comp_type_returner(pointed);
    let entry = arena.comp_type_pi(boolean.ty, returns);
    let motive = arena.comp_type_pi(boolean.ty, entry);
    let here = arena.value_here(boolean.truth);
    let step = |arena: &mut TermArena, path: ValueId, over: ValueId| {
        let mut table = ContentTable::new();
        let mut memo = gandr_kernel_check_memo::NullMemo;
        telescope_beta(arena, &mut table, &mut memo, TelescopeStep {
            motive,
            path,
            start: boolean.truth,
            over,
            value: here,
        })
    };

    let along_here = arena.computation_telescope_transport(motive, here, boolean.truth, here, here);
    let returned = arena.computation_return(here);
    assert_eq!(
        computes(&mut arena, along_here, returned),
        KernelVerdict::Convertible
    );
    let other = arena.value_here(boolean.falsity);
    let returned_other = arena.computation_return(other);
    assert_ne!(
        computes(&mut arena, along_here, returned_other),
        KernelVerdict::Convertible
    );
    let Ok(Reduction::Reduced(reduct)) = step(&mut arena, here, here)
    else {
        panic!("transport along here reduces");
    };
    assert_eq!(arena.computation(reduct), Some(&Computation::Return(here)));

    let neutral = arena.value_variable(DeBruijnIndex::from(0_u32));
    let Ok(Reduction::Reduced(reduct)) = step(&mut arena, here, neutral)
    else {
        panic!("transport along a here path reduces into its fibre");
    };
    let Some(&Computation::PathTransport {
        motive: fibre,
        path,
        value,
    }) = arena.computation(reduct)
    else {
        panic!("the fibre transport is a one-binder transport");
    };
    let expected = arena.value_type_path(boolean.ty, boolean.truth, inner);
    assert_eq!(
        crate::conv::convertible_value_types(&arena, fibre, expected),
        Convertibility::Convertible
    );
    assert_eq!((path, value), (neutral, here));

    assert_eq!(step(&mut arena, neutral, here), Ok(Reduction::Stuck));
}

#[test]
fn j_derived_in_the_singleton_checks_and_computes()
{
    // J := λx : Bool. λp : Path(Bool, T, x). λd : C[T, here(T)].
    //   transport((y : Bool, z : Path(Bool, T, y)) => C, p, here(T), here(p), d)
    //   : F C[x, p]
    // where C(y, z) = Path(Path(Bool, T, y), z, z) reads both entries.
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let truth = boolean.truth;
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    let singleton = |arena: &mut TermArena, end: u32| {
        let end = var(arena, end);
        arena.value_type_path(boolean.ty, truth, end)
    };
    let body_at = |arena: &mut TermArena, point: u32, element: u32| {
        let fibre = singleton(arena, point);
        let element = var(arena, element);
        arena.value_type_path(fibre, element, element)
    };
    let family = singleton(&mut arena, 0);
    let body = body_at(&mut arena, 1, 0);
    let returns = arena.comp_type_returner(body);
    let entry = arena.comp_type_pi(family, returns);
    let motive = arena.comp_type_pi(boolean.ty, entry);
    let start = arena.value_here(truth);
    let reflexive = arena.value_type_path(boolean.ty, truth, truth);
    let at_source = arena.value_type_path(reflexive, start, start);
    let carrier = singleton(&mut arena, 0);
    let result = body_at(&mut arena, 2, 1);
    let derived = |arena: &mut TermArena, over: ValueId| {
        let path = var(arena, 1);
        let held = var(arena, 0);
        let j = arena.computation_telescope_transport(motive, path, start, over, held);
        function(arena, &[boolean.ty, carrier, at_source], result, j)
    };

    let path = var(&mut arena, 1);
    let over = arena.value_here(path);
    let (term, declared) = derived(&mut arena, over);
    check_closed_value(&mut arena, term, declared).expect("J in the singleton family");

    // `d` is an identity in the fibre over the source, from `here(T)` to
    // itself, not one over `p`: the family's dependency on the path's
    // endpoint is refused by name.
    let held = var(&mut arena, 0);
    let (term, declared) = derived(&mut arena, held);
    let error = check_closed_value(&mut arena, term, declared)
        .expect_err("an identity over the source is not over the path");
    assert!(matches!(
        error,
        KernelError::Identity(IdentityError::NotOver { .. })
    ));
    assert_eq!(
        error.to_string(),
        "an identity that does not lie over its path"
    );

    // On `here(T)` J computes to its base case.
    let base = arena.value_here(start);
    let at_here = arena.computation_telescope_transport(motive, start, start, base, base);
    let returned = arena.computation_return(base);
    assert_eq!(
        computes(&mut arena, at_here, returned),
        KernelVerdict::Convertible
    );
    let returned_start = arena.computation_return(start);
    assert_ne!(
        computes(&mut arena, at_here, returned_start),
        KernelVerdict::Convertible
    );
}

#[test]
fn transport_reads_its_family_s_shape_before_it_reduces()
{
    let mut arena = TermArena::new();
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    let binder = arena.value_variable(DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
    let path = arena.value_variable(DeBruijnIndex::from(5_u32));
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();
    let reads = arena.value_type_element(binder, Level::zero());

    assert_eq!(
        super::binder_use(
            &mut arena,
            &mut table,
            &mut memo,
            super::Family::Value(outer)
        ),
        super::BinderUse::Ignored,
        "a family over an outer variable alone is constant in its binder"
    );
    assert_eq!(
        super::binder_use(
            &mut arena,
            &mut table,
            &mut memo,
            super::Family::Value(binder)
        ),
        super::BinderUse::Read,
        "and the binder itself reads it"
    );

    let product = arena.value_type_product(&[reads, unit_type]);
    let short = arena.value_tuple(&[unit]);
    let raised = arena.value_type_element(
        binder,
        Level::constant(gandr_kernel_strata::LevelConstant::from(1)),
    );
    let base = arena.value_type_base(BaseType::Integer);
    let point = arena.value_literal(Literal::Text(StringLiteral::new(
        alloc::string::String::from("p"),
    )));
    let singleton = arena.value_type_path(base, point, binder);
    let moving_domain = arena.value_type_path(reads, unit, binder);
    let here = arena.value_here(point);
    for (motive, value, what) in [
        (
            product,
            short,
            "a product family over a tuple of another arity",
        ),
        (raised, unit, "an element family above the value universe"),
        (
            moving_domain,
            here,
            "a path family whose carrier reads the binder",
        ),
    ] {
        assert_eq!(
            transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
                motive,
                path,
                value,
            }),
            Ok(Reduction::Stuck),
            "{what} sticks"
        );
    }
    let Ok(Reduction::Reduced(reduct)) =
        transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
            motive: singleton,
            path,
            value: here,
        })
    else {
        panic!("reflexivity carried in the singleton family reduces");
    };
    assert_eq!(
        arena.computation(reduct),
        Some(&Computation::Return(path)),
        "to the path it was carried along"
    );
}

#[test]
fn a_decoded_endpoint_passes_exactly_where_its_code_reads_as_the_other_type()
{
    use crate::conv::ConversionGoal;
    use crate::replay::EndpointReading;
    use crate::replay::Unfoldings;

    let mut arena = TermArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let code = arena.value_quote(integer);
    let returns = arena.computation_return(code);
    let returned = arena.value_returned(returns);
    let decoded = arena.value_type_element(returned, Level::zero());
    for (other, reading) in [
        (integer, EndpointReading::Converts),
        (string, EndpointReading::Apart),
    ] {
        assert_eq!(
            super::related_endpoints(
                &mut arena,
                &Unfoldings::default(),
                &[],
                ConversionGoal::ValueType(decoded, other),
            ),
            Ok(reading)
        );
    }
}
