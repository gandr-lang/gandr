use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionError;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ScopeId;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;

use super::Bound;
use super::Definitions;
use super::Endpoints;
use super::EvalFault;
use super::Evaluation;
use super::Fuel;
use super::LoweredChain;
use super::Progress;
use super::eval_comp_within;
use super::eval_computation;
use super::eval_value;
use super::face_of;
use super::run_held;
use crate::arena::DomainArena;
use crate::closure::Environment;
use crate::conv::Settlement;
use crate::conv::convert_computations;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::LevelEntry;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::readback::ReadbackMode;
use crate::readback::readback_value;

/// Ample fuel for every case that is meant to finish.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a budget far above the step count any fixture below needs, so an
///   exhaustion refusal in one of them is a defect rather than a tight budget.
/// - provides: the budget every finishing case is run with; the exhaustion
///   cases name their own small budgets.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the positive budget is sufficient for the finite beta,
///   bind and case fixtures, whose exact results would instead be `OutOfFuel`
///   if the budget did not cover their work.
/// - witness: `eval::tests::a_redex_fires_and_the_body_sees_the_argument`
/// - witness: `eval::tests::a_bind_passes_the_returned_value_on`
/// - witness: `eval::tests::a_case_picks_the_branch_the_injection_names`
#[spec(
        ensures: |ret| ret.0 > 0_u32,
    )]
fn ample() -> Fuel
{
    Fuel::from(4_096_u32)
}

/// The index at the innermost binder.
///
/// # Specification
/// trivial.
fn innermost() -> DeBruijnIndex
{
    DeBruijnIndex::from(0_u32)
}

/// An empty chain and environment, which unfold nothing.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an empty chain and an empty definitional environment, so every
///   constant reads as not manifest and no run unfolds.
/// - provides: the definition side of every fixture that is about reduction
///   rather than unfolding.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constant under the empty chain remains a rigid neutral
///   and its eliminations remain stuck. Introducing a body would change the
///   unfolding face and the normalization path.
/// - witness: `eval::tests::an_eliminator_on_a_neutral_grows_its_spine`
/// - witness: `eval::tests::normalization_preserves_a_stuck_application`
#[spec(
        ensures: |ret| ret.0.chain.entries().is_empty() && ret.0.bodies.is_empty(),
    )]
fn nothing_unfolds() -> (LoweredChain, DefinitionalEnvironment)
{
    (LoweredChain::new(), DefinitionalEnvironment::new())
}

/// Lower every body of `chain` to one core value.
///
/// # Specification
/// - requires: `lowered` resolves in the arena the fixture evaluates against.
/// - ensures: a lowered chain whose every body is `lowered`.
/// - provides: the lowering side of every fixture that reads an unfolding face
///   without forcing it, where what the body lowers to is not what is asserted.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one lowered definition is manifest or sealed according to
///   the chosen scope, and its unforced face names the admitted body. Losing a
///   body mapping or using another lowering prevents the advertised definition
///   from being forced.
/// - witness: `eval::tests::a_manifest_definition_carries_its_body_unforced`
/// - witness: `eval::tests::a_sealed_definition_is_rigid`
#[spec(
        captures: [entry_count = chain.entries().len()],
        ensures: |ret| ret.chain.entries().len() == entry_count
            && ret.bodies.values().all(|body| *body == lowered)
            && ret.chain.entries().iter().all(|entry| ret.bodies.get(&entry.body()) == Some(&lowered)),
    )]
fn lowered_to(
    chain: DefinitionChain,
    lowered: ValueId,
) -> LoweredChain
{
    let Ok(chain) = LoweredChain::lower(chain, |_| Ok::<_, Infallible>(lowered));
    chain
}

#[test]
fn an_unreduced_composite_keeps_its_source_face()
{
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_unit();
    let pair = core.value_tuple(&[first, second]);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_value(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        pair,
    )
    .expect("a closed pair of units evaluates");

    assert_eq!(
        Some(TermFace::Source(pair)),
        face_of(&domain, evaluated),
        "nothing inside reduced, so the pair still denotes its own source node"
    );
    let Some(&[left, right]) = domain
        .value(evaluated)
        .and_then(|held| domain.components(held))
    else {
        panic!("the result is a pair");
    };
    assert_eq!(Some(TermFace::Source(first)), face_of(&domain, left));
    assert_eq!(
        Some(TermFace::Source(second)),
        face_of(&domain, right),
        "and each child denotes the source child it came from"
    );
}

#[test]
fn the_leaf_and_lift_arms_evaluate_and_keep_their_faces()
{
    let mut core = CoreArena::new();
    let literal = core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::zero(),
    )));
    let lifted = core.value_unit();
    let target = Level::zero().succ().expect("level one exists");
    let lift = core.value_lift(target.clone(), lifted);
    let pair = core.value_tuple(&[literal, lift]);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_value(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        pair,
    )
    .expect("a closed pair of a literal and a lift evaluates");

    assert_eq!(
        Some(TermFace::Source(pair)),
        face_of(&domain, evaluated),
        "nothing inside reduced, so both arms kept their faces and the pair kept its own"
    );
    let Some(&[first, second]) = domain
        .value(evaluated)
        .and_then(|held| domain.components(held))
    else {
        panic!("the result is a pair");
    };
    assert!(
        matches!(
            domain.value(first),
            Some(&DomainValue::Literal { literal: held, .. }) if held == literal
        ),
        "the literal arm points at the core node holding the payload rather than copying it"
    );
    let Some(&DomainValue::Lift {
        target: held,
        body,
        face,
    }) = domain.value(second)
    else {
        panic!("the second component is a lift");
    };
    assert_eq!(TermFace::Source(lift), face);
    assert_eq!(
        Some(TermFace::Source(lifted)),
        face_of(&domain, body),
        "and its body kept the source it came from"
    );
    assert_eq!(
        Some(&target),
        domain.level(held).map(LevelEntry::level),
        "the lift arm is the only producer of the level family, and it filled it"
    );
}

#[test]
fn a_lift_over_a_substituted_body_loses_its_face()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let target = Level::zero().succ().expect("level one exists");
    let lift = core.value_lift(target, occurrence);
    let body = core.computation_return(lift);
    let lambda = core.computation_lambda(body);
    let redex = core.computation_application(lambda, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        redex,
    )
    .expect("the redex fires");

    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the weak head is a returner");
    };
    assert_eq!(
        Some(TermFace::Reduced),
        face_of(&domain, value),
        "the lift's body resolved out of the environment, so the lift lost its source"
    );
    let Some(&DomainValue::Lift { body, .. }) = domain.value(value)
    else {
        panic!("the returned value is a lift");
    };
    assert_eq!(
        Some(TermFace::Source(argument)),
        face_of(&domain, body),
        "while the body it lifted denotes the argument"
    );
}

#[test]
fn a_term_from_another_arena_is_refused()
{
    let mut evaluated_arena = CoreArena::new();
    let _padding = evaluated_arena.value_unit();

    let mut other = CoreArena::new();
    let mut stranger = other.value_unit();
    let mut remaining = 8_usize;
    while remaining > 0 {
        stranger = other.value_tuple(&[stranger, stranger]);
        remaining = remaining.saturating_sub(1);
    }

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    assert_eq!(
        Err(EvalFault::DanglingTerm),
        eval_value(
            &evaluated_arena,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            stranger,
        ),
        "a term id minted by one arena names no node of another, and the refusal says \
             the term dangled rather than blaming the domain"
    );
}

#[test]
fn an_application_reports_its_arguments_fault_first()
{
    // Both sides are faulty, and — the load-bearing part — each faults
    // *during its own evaluation* rather than at the application's own
    // frame. The argument is an occurrence with no binder over it; the head
    // forces a unit, which its own `Force` frame refuses. The application's
    // frame runs after both operands, so a fault raised there would surface
    // under either order and would constrain nothing.
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let head = core.computation_force(unit);
    let loose = core.value_variable(Zone::Intuitionistic, innermost());
    let applied = core.computation_application(head, loose);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    assert_eq!(
        Err(EvalFault::UnboundVariable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            applied,
        ),
        "the argument is evaluated first, so its fault is the one that surfaces; \
             evaluating the head first would answer ForcedNonThunk"
    );
}

#[test]
fn a_substituted_child_costs_the_composite_its_face()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let held = core.value_unit();
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let pair = core.value_tuple(&[bound, held]);
    let body = core.computation_return(pair);
    let lambda = core.computation_lambda(body);
    let redex = core.computation_application(lambda, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        redex,
    )
    .expect("the redex fires");

    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the weak head is a returner");
    };
    assert_eq!(
        Some(TermFace::Reduced),
        face_of(&domain, value),
        "the variable resolved out of the environment, so the pair no longer denotes its source"
    );
    let Some(&[first, _]) = domain.value(value).and_then(|held| domain.components(held))
    else {
        panic!("the returned value is a pair");
    };
    assert_eq!(
        Some(TermFace::Source(argument)),
        face_of(&domain, first),
        "and the substituted child denotes the argument rather than the variable"
    );
}

#[test]
fn a_variable_resolves_out_of_the_environment()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let body = core.computation_return(bound);
    let lambda = core.computation_lambda(body);
    let redex = core.computation_application(lambda, argument);
    let loose = core.computation_return(bound);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let evaluated =
        eval_computation(&core, &mut domain, definitions, ample(), redex).expect("the redex fires");
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the weak head is a returner");
    };
    assert_eq!(
        Some(TermFace::Source(argument)),
        face_of(&domain, value),
        "the bound occurrence stands for what the environment holds"
    );

    assert_eq!(
        Err(EvalFault::UnboundVariable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        eval_computation(&core, &mut domain, definitions, ample(), loose),
        "and an occurrence with no binder over it is refused rather than guessed at"
    );
}

#[test]
fn a_closed_lambda_keeps_its_source_face()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let inner_body = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let returner = core.computation_return(inner_body);
    let inner = core.computation_lambda(returner);
    let outer = core.computation_lambda(inner);
    let applied = core.computation_application(outer, argument);
    let different = core.value_tuple(&[argument, argument]);
    let applied_twice = core.computation_application(applied, different);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();

    let closed = eval_computation(&core, &mut domain, definitions, ample(), outer)
        .expect("a lambda is already a weak head");
    let Some(&DomainComp::Lambda { face, .. }) = domain.computation(closed)
    else {
        panic!("the weak head is a lambda");
    };
    assert_eq!(
        CompTermFace::Source(outer),
        face,
        "a lambda over the empty environment denotes its own source node"
    );

    let captured = eval_computation(&core, &mut domain, definitions, ample(), applied)
        .expect("the outer redex fires");
    let Some(&DomainComp::Lambda { face, .. }) = domain.computation(captured)
    else {
        panic!("the weak head is the inner lambda");
    };
    assert_eq!(
        CompTermFace::Reduced,
        face,
        "one that captured a binding denotes its body only up to what the environment supplies"
    );
    let twice = eval_computation(&core, &mut domain, definitions, ample(), applied_twice)
        .expect("the captured outer binding survives the second application");
    let Some(&DomainComp::Return { value, .. }) = domain.computation(twice)
    else {
        panic!("the outer-bound variable returns its argument");
    };
    assert_eq!(
        Some(TermFace::Source(argument)),
        face_of(&domain, value),
        "the captured unit, not the inner pair argument, is returned"
    );
}

#[test]
fn a_redex_fires_and_the_body_sees_the_argument()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let returner = core.computation_return(bound);
    let identity = core.computation_lambda(returner);
    let thunked = core.value_thunk(identity);
    let forced = core.computation_force(thunked);
    let applied = core.computation_application(forced, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        applied,
    )
    .expect("forcing a thunk of a lambda and applying it fires");

    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the weak head is a returner");
    };
    assert_eq!(
        Some(TermFace::Source(argument)),
        face_of(&domain, value),
        "force entered the closure and the application bound the argument in it"
    );
}

#[test]
fn a_bind_passes_the_returned_value_on()
{
    let mut core = CoreArena::new();
    let produced = core.value_unit();
    let bound_comp = core.computation_return(produced);
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let continuation = core.computation_return(occurrence);
    let sequenced = core.computation_bind(bound_comp, continuation);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        sequenced,
    )
    .expect("a bind over a returner runs its continuation");

    let Some(&DomainComp::Return { value, face }) = domain.computation(evaluated)
    else {
        panic!("the weak head is a returner");
    };
    assert_eq!(
        Some(TermFace::Source(produced)),
        face_of(&domain, value),
        "the continuation sees exactly what the bound computation returned"
    );
    assert_eq!(
        CompTermFace::Reduced,
        face,
        "and the returner it built no longer denotes its own source, because the \
             occurrence resolved"
    );
}

#[test]
fn a_realised_fill_evaluates_as_its_induction()
{
    let mut core = CoreArena::new();
    let cell = core.value_unit();
    let generator = core.computation_return(cell);
    let fill = core.value_fill(
        gandr_core_term::compose::Composite::binary(),
        generator,
        alloc::boxed::Box::from([cell]),
    );
    let induced = core.value_unit();
    let induction = core.computation_return(induced);

    let (mut chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let inert = eval_value(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        fill,
    )
    .expect("an unrealised fill evaluates");
    assert_eq!(
        Some(TermFace::Source(fill)),
        face_of(&domain, inert),
        "a fill no checker realised is inert, its own source"
    );

    chain.realise(fill, induction);
    let realised = eval_value(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        fill,
    )
    .expect("a realised fill evaluates");
    assert_eq!(
        Some(TermFace::Source(induced)),
        face_of(&domain, realised),
        "a realised fill is what its induction returns"
    );
}

#[test]
fn native_certificate_conversion_retains_map_syntax()
{
    let mut core = CoreArena::new();
    let unit_type = core.value_type_unit();
    let code = core.value_quote(unit_type);
    let path_type = core.value_type_path_universe(code, code);
    let variable = core.value_variable(Zone::Intuitionistic, innermost());
    let returned = core.computation_return(variable);
    let direct = core.computation_lambda(returned);
    let direct = core.value_thunk(direct);
    let sequenced = core.computation_bind(returned, returned);
    let expanded = core.computation_lambda(sequenced);
    let expanded = core.value_thunk(expanded);
    let proof = alloc::sync::Arc::new(gandr_kernel_term::PathEvidence {
        source: Vec::from([Vec::new()]),
        target: Vec::from([Vec::new()]),
    });
    let first = core.value_path_equiv(path_type, direct, direct, alloc::sync::Arc::clone(&proof));
    let other = core.value_path_equiv(path_type, direct, expanded, proof);
    let altered = alloc::sync::Arc::new(gandr_kernel_term::PathEvidence {
        source: Vec::from([Vec::from([
            gandr_kernel_conversion_trace::ConversionDecision::ComparedShared {
                left: (),
                right: (),
            },
        ])]),
        target: Vec::from([Vec::new()]),
    });
    let evidence_only = core.value_path_equiv(path_type, direct, direct, altered);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let first =
        eval_value(&core, &mut domain, definitions, ample(), first).expect("closed certificate");
    let other =
        eval_value(&core, &mut domain, definitions, ample(), other).expect("closed certificate");
    let evidence_only =
        eval_value(&core, &mut domain, definitions, ample(), evidence_only).expect("closed syntax");
    assert_eq!(
        Ok(crate::conv::Convertibility::Distinct),
        crate::conv::convert_values(&core, &domain, first, other).map(Settlement::verdict),
        "extensionally equal maps do not identify certificate programs"
    );
    assert_eq!(
        Ok(crate::conv::Convertibility::Convertible),
        crate::conv::convert_values(&core, &domain, first, evidence_only).map(Settlement::verdict),
        "comparison erases evidence; only kernel admission can certify it"
    );
}

#[test]
fn native_transport_sequences_product_components()
{
    for (first_stuck, second_stuck) in [(false, false), (true, false), (false, true), (true, true)]
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let unit_type = core.value_type_unit();
        let boolean = core.value_type_sum(&[unit_type, unit_type]);
        let code = core.value_quote(boolean);
        let refl = core.value_path_refl(code);
        let first_path = if first_stuck {
            core.value_constant(ConstantIndex::from(0_usize))
        }
        else {
            refl
        };
        let second_path = if second_stuck {
            core.value_constant(ConstantIndex::from(1_usize))
        }
        else {
            refl
        };
        let path = core.value_path_product(first_path, second_path);
        let left = core.value_injection(Side::Left.into(), unit);
        let right = core.value_injection(Side::Right.into(), unit);
        let operand = core.value_tuple(&[left, right]);
        let transported = core.computation_transport(path, operand);
        let first = if first_stuck {
            core.value_variable(
                Zone::Intuitionistic,
                DeBruijnIndex::from(u32::from(second_stuck)),
            )
        }
        else {
            left
        };
        let second = if second_stuck {
            core.value_variable(Zone::Intuitionistic, innermost())
        }
        else {
            right
        };
        let pair = core.value_tuple(&[first, second]);
        let mut expected = core.computation_return(pair);
        if second_stuck {
            let transport = core.computation_transport(second_path, right);
            expected = core.computation_bind(transport, expected);
        }
        if first_stuck {
            let transport = core.computation_transport(first_path, left);
            expected = core.computation_bind(transport, expected);
        }
        let expected = core.value_thunk(expected);
        let (chain, environment) = nothing_unfolds();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), transported)
            .expect("neutral components suspend; reflexivity returns");
        for mode in [ReadbackMode::ZeroUnfold, ReadbackMode::Unfolding] {
            let normal = crate::readback::readback_computation(
                &mut core,
                &mut domain,
                definitions,
                mode,
                ample(),
                evaluated,
            )
            .expect("captured product continuations reopen under binders");
            let normal = core.value_thunk(normal);
            assert!(
                gandr_core_term::equal_certificate_syntax(&core, normal, expected)
                    == gandr_core_term::CertificateEquality::Equal,
                "product sequencing preserves both coordinates and binder depths: {first_stuck:?}, {second_stuck:?}, {mode:?}"
            );
        }
    }
}

#[test]
fn transport_along_univalence_is_refused_as_underived()
{
    use alloc::boxed::Box;
    use alloc::sync::Arc;

    use gandr_core_term::ua::Description;
    use gandr_core_term::ua::Sides;
    use gandr_core_term::ua::Stratum;

    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let empty = || Description {
        name: From::from("Point"),
        generators: Box::from([]),
    };
    let sides = Arc::new(Sides {
        source: empty(),
        target: empty(),
    });
    let translator = core.value_record(alloc::collections::BTreeMap::new());
    let stratum = Stratum {
        degree: From::from(1_usize),
        bound: From::from(4_usize),
    };
    let path = core.value_ua(stratum, sides, translator, translator);
    let transported = core.computation_transport(path, unit);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    assert_eq!(
        Err(EvalFault::TransportedUnderived),
        eval_computation(&core, &mut domain, definitions, ample(), transported),
        "a univalence path carries no translator transport can run"
    );
}

#[test]
fn a_telescope_motive_has_a_body_only_when_its_result_type_lives()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let mut elsewhere = CoreArena::new();
    let mut dangling = elsewhere.value_type_unit();
    for _ in 0_u8 .. 16 {
        dangling = elsewhere.value_type_list(dangling);
    }
    let motive = |core: &mut CoreArena, result| {
        let returned = core.comp_type_returner(result);
        let entry = core.comp_type_pi(unit, returned);
        core.comp_type_pi(unit, entry)
    };
    let held = motive(&mut core, unit);
    assert_eq!(Ok(unit), super::telescope_body(&core, held));
    let unheld = motive(&mut core, dangling);
    assert_eq!(
        Err(EvalFault::MachineInvariant),
        super::telescope_body(&core, unheld),
        "a result type the arena does not hold is no body"
    );
}

#[test]
fn a_held_endpoint_is_read_only_at_its_spine_root()
{
    let mut domain = DomainArena::new();
    let argument = domain.value_unit(TermFace::Reduced);
    let computation = domain.comp_return(argument, CompTermFace::Reduced);
    let mut held = |spine| {
        let neutral = domain
            .neutral_node(NeutralHead::Returned(computation), spine, Unfolding::Rigid)
            .expect("a returned computation heads a neutral");
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a static application leaves a value")
    };
    let bare = held(Vec::new());
    let applied = held(Vec::from([Elimination::StaticApply(argument)]));
    assert_eq!(Ok(Some(computation)), super::held_endpoint(&domain, bare));
    assert_eq!(
        Ok(None),
        super::held_endpoint(&domain, applied),
        "an endpoint applied further is no longer the computation it holds"
    );
}

#[test]
fn a_case_picks_the_branch_the_injection_names()
{
    let mut core = CoreArena::new();
    let injected = core.value_unit();
    let untaken = core.value_unit();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let on_left = core.computation_return(occurrence);
    let on_right = core.computation_return(untaken);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    for (side, expected) in [(Side::Left, injected), (Side::Right, untaken)] {
        let scrutinee = core.value_injection(side.into(), injected);
        let cased = core.computation_case(scrutinee, &[on_left, on_right]);
        let mut domain = DomainArena::new();
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased)
            .expect("a case over an injection picks a branch");
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("the weak head is a returner");
        };
        assert_eq!(
            Some(TermFace::Source(expected)),
            face_of(&domain, value),
            "the side of the injection decides which branch ran"
        );
    }
}

#[test]
fn an_eliminator_on_a_neutral_grows_its_spine()
{
    let mut core = CoreArena::new();
    let opaque = core.value_constant(ConstantIndex::from(0_usize));
    let argument = core.value_unit();
    let forced = core.computation_force(opaque);
    let applied = core.computation_application(forced, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        applied,
    )
    .expect("an eliminator over a rigid constant gets stuck rather than failing");

    let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
    else {
        panic!("the weak head is stuck");
    };
    let held = domain.neutral(neutral).expect("the neutral resolves");
    assert_eq!(
        NeutralHead::Constant(ConstantIndex::from(0_usize)),
        held.head(),
        "the head is the constant that could not step"
    );
    assert_eq!(
        2_usize,
        held.spine().len(),
        "both eliminations stacked rather than either being dropped"
    );
    assert_eq!(
        Some(&Elimination::Force),
        held.spine().first(),
        "innermost first"
    );
    assert!(
        matches!(held.spine().get(1_usize), Some(&Elimination::Apply(_))),
        "outermost last"
    );
    assert_eq!(
        Unfolding::Rigid,
        held.unfolding(),
        "an unknown constant has no body, so growing the spine kept it rigid"
    );
}

/// `fix rec. λx. case x of { zero ↦ return zero; succ ↦ λp. r ← (force
/// rec) p; return (succ (succ r)) }` over the nominal `nat`, with the
/// constructors `zero` and `succ` at tags 0 and 1.
///
/// # Specification
/// trivial.
fn doubling(
    core: &mut CoreArena,
    nat: gandr_core_term::ValueTypeId,
    evidence: gandr_kernel_term::FixpointEvidence,
) -> gandr_core_term::ComputationId
{
    let zero = core.value_constructor(
        nat,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        Vec::new(),
    );
    let returner = core.comp_type_returner(nat);
    let on_zero = core.computation_return(zero);
    let field = core.value_variable(Zone::Intuitionistic, innermost());
    let recursive = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let forced = core.computation_force(recursive);
    let call = core.computation_application(forced, field);
    let result = core.value_variable(Zone::Intuitionistic, innermost());
    let successor = gandr_kernel_term::ConstructorTag::from(1_usize);
    let once = core.value_constructor(nat, successor, Vec::from([result]));
    let twice = core.value_constructor(nat, successor, Vec::from([once]));
    let returned = core.computation_return(twice);
    let bound = core.computation_bind(call, returned);
    let on_successor = core.computation_lambda(bound);
    let argument = core.value_variable(Zone::Intuitionistic, innermost());
    let case = core.computation_data_case(
        argument,
        returner,
        Vec::from([on_zero, on_successor]),
        [0_usize, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let body = core.computation_lambda(case);
    core.computation_fixpoint(body, evidence)
}

#[test]
fn a_fixpoint_unfolds_at_a_constructor_and_sticks_at_a_neutral()
{
    let mut core = CoreArena::new();
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let successor = gandr_kernel_term::ConstructorTag::from(1_usize);
    let zero = core.value_constructor(
        nat,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        Vec::new(),
    );
    let one = core.value_constructor(nat, successor, Vec::from([zero]));
    let two = core.value_constructor(nat, successor, Vec::from([one]));
    let three = core.value_constructor(nat, successor, Vec::from([two]));
    let four = core.value_constructor(nat, successor, Vec::from([three]));
    let fixpoint = doubling(
        &mut core,
        nat,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let applied = core.computation_application(fixpoint, two);
    let expected = core.computation_return(four);
    let variable = core.value_variable(Zone::Intuitionistic, innermost());
    let stuck = core.computation_application(fixpoint, variable);
    let abstracted = core.computation_lambda(stuck);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    for (term, normal) in [(applied, expected), (abstracted, abstracted)] {
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), term)
            .expect("a gated fixpoint reaches its weak head");
        let read = crate::readback::readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the weak head reads back");
        let read = core.value_thunk(read);
        let normal = core.value_thunk(normal);
        assert_eq!(
            gandr_core_term::CertificateEquality::Equal,
            gandr_core_term::equal_certificate_syntax(&core, read, normal),
            "at a constructor the fixpoint unfolds to the doubled numeral; at a neutral \
                 it stands, and reads back as itself"
        );
    }
}

/// `fix count. λacc. λb. case b { Z ⇒ return acc; S(x) ⇒ count (S acc) x }`,
/// staged at its second binder: the accumulator varies on every call.
///
/// # Specification
/// trivial.
fn counting(
    core: &mut CoreArena,
    nat: gandr_core_term::ValueTypeId,
) -> gandr_core_term::ComputationId
{
    let successor = gandr_kernel_term::ConstructorTag::from(1_usize);
    let returner = core.comp_type_returner(nat);
    let accumulated = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let on_zero = core.computation_return(accumulated);
    let recursive = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let forced = core.computation_force(recursive);
    let accumulator = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let grown = core.value_constructor(nat, successor, Vec::from([accumulator]));
    let leading = core.computation_application(forced, grown);
    let field = core.value_variable(Zone::Intuitionistic, innermost());
    let call = core.computation_application(leading, field);
    let on_successor = core.computation_lambda(call);
    let scrutinee = core.value_variable(Zone::Intuitionistic, innermost());
    let case = core.computation_data_case(
        scrutinee,
        returner,
        Vec::from([on_zero, on_successor]),
        [0_usize, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let staged = core.computation_lambda(case);
    let body = core.computation_lambda(staged);
    core.computation_fixpoint(body, gandr_kernel_term::FixpointEvidence::Staged {
        position: gandr_kernel_term::StagedPosition::from(1_usize),
    })
}

#[test]
fn a_fixpoint_staged_past_its_first_binder_carries_its_leading_arguments_626()
{
    let mut core = CoreArena::new();
    let nat = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let successor = gandr_kernel_term::ConstructorTag::from(1_usize);
    let zero = core.value_constructor(
        nat,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        Vec::new(),
    );
    let one = core.value_constructor(nat, successor, Vec::from([zero]));
    let two = core.value_constructor(nat, successor, Vec::from([one]));
    let fixpoint = counting(&mut core, nat);
    let taken = core.computation_application(fixpoint, zero);
    let applied = core.computation_application(taken, two);
    let expected = core.computation_return(two);
    let variable = core.value_variable(Zone::Intuitionistic, innermost());
    let stuck = core.computation_application(taken, variable);
    let abstracted = core.computation_lambda(stuck);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let partial = eval_computation(&core, &mut domain, definitions, ample(), taken)
        .expect("a fixpoint takes an argument before its staged one");
    let Some(&DomainComp::Fixpoint { leading, .. }) = domain.computation(partial)
    else {
        panic!("an argument before the staged one is held, not gated");
    };
    assert_eq!(
        domain.fields(leading).map(<[_]>::len),
        Ok(1_usize),
        "the fixpoint holds the one argument it took"
    );
    for (term, normal) in [
        (applied, expected),
        (abstracted, abstracted),
        (taken, taken),
    ] {
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), term)
            .expect("a gated fixpoint reaches its weak head");
        let read = crate::readback::readback_computation(
            &mut core,
            &mut domain,
            definitions,
            ReadbackMode::Unfolding,
            ample(),
            evaluated,
        )
        .expect("the weak head reads back");
        let read = core.value_thunk(read);
        let normal = core.value_thunk(normal);
        assert_eq!(
            gandr_core_term::CertificateEquality::Equal,
            gandr_core_term::equal_certificate_syntax(&core, read, normal),
            "at a constructor the accumulator is returned; at a neutral the fixpoint \
                 stands with its leading argument, and reads back as itself applied to it"
        );
    }
}

#[test]
fn an_observed_loop_runs_out_of_fuel()
{
    let mut core = CoreArena::new();
    let recursive = core.value_variable(Zone::Intuitionistic, innermost());
    let forced = core.computation_force(recursive);
    let looping = core.computation_fixpoint(forced, gandr_kernel_term::FixpointEvidence::Partial);
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let observed = core.computation_bind(looping, returned);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let bare = eval_computation(&core, &mut domain, definitions, ample(), looping)
        .expect("a bare fixpoint is inert");
    assert!(
        matches!(domain.computation(bare), Some(&DomainComp::Fixpoint { .. })),
        "no gate observes it, so it is its own weak head"
    );
    assert_eq!(
        Err(EvalFault::OutOfFuel),
        eval_computation(&core, &mut domain, definitions, ample(), observed),
        "each observation unfolds it once, and the loop never returns"
    );
}

#[test]
fn a_manifest_definition_carries_its_body_unforced()
{
    let mut core = CoreArena::new();
    let constant = ConstantIndex::from(0_usize);
    let reference = core.value_constant(constant);

    let mut chain = DefinitionChain::new();
    let body = GlobalIndex::from(9_u32);
    let defined = chain.define(constant, body, Transparency::Manifest, &[]);
    assert!(defined.is_ok());
    let chain = lowered_to(chain, reference);
    let environment = DefinitionalEnvironment::new();
    let scope = environment.root();

    let mut domain = DomainArena::new();
    let evaluated = eval_value(
        &core,
        &mut domain,
        Definitions::new(&chain, &environment, scope),
        ample(),
        reference,
    )
    .expect("a constant evaluates to a neutral");

    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
    else {
        panic!("a constant is stuck");
    };
    let held = domain.neutral(neutral).expect("the neutral resolves");
    assert_eq!(
        Unfolding::Unforced(body),
        held.unfolding(),
        "a manifest definition carries its body's content id, unforced"
    );
    assert!(
        held.spine().is_empty(),
        "and stands in a value position, so it carries no spine"
    );
}

#[test]
fn a_rigid_run_unfolds_no_definition()
{
    let mut core = CoreArena::new();
    let constant = ConstantIndex::from(0_usize);
    let reference = core.value_constant(constant);
    let mut chain = DefinitionChain::new();
    let body = GlobalIndex::from(9_u32);
    let defined = chain.define(constant, body, Transparency::Manifest, &[]);
    assert!(defined.is_ok());
    let chain = lowered_to(chain, reference);
    let environment = DefinitionalEnvironment::new();
    let unfolding = Definitions::new(&chain, &environment, environment.root());
    assert_eq!(unfolding.unfolding(constant), Unfolding::Unforced(body));
    let rigid = unfolding.rigid();
    assert_eq!(
        rigid.unfolding(constant),
        Unfolding::Rigid,
        "the same manifest definition is compared by name"
    );
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, rigid, ample(), reference)
        .expect("a constant evaluates to a neutral");
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
    else {
        panic!("a constant is stuck");
    };
    assert_eq!(
        domain
            .neutral(neutral)
            .map(super::super::domain::Neutral::unfolding),
        Some(Unfolding::Rigid),
        "and the evaluator reads it there"
    );
}

#[test]
fn a_held_endpoint_stays_at_its_definition()
{
    // `ident(unit)` as a compound endpoint, `ident` the manifest identity.
    let mut core = CoreArena::new();
    let constant = ConstantIndex::from(0_usize);
    let reference = core.value_constant(constant);
    let variable = core.value_variable(Zone::Intuitionistic, innermost());
    let returned = core.computation_return(variable);
    let lambda = core.computation_lambda(returned);
    let identity = core.value_thunk(lambda);
    let unit = core.value_unit();
    let forced = core.computation_force(reference);
    let applied = core.computation_application(forced, unit);
    let endpoint = core.value_returned(applied);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(
        constant,
        GlobalIndex::from(9_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok());
    let chain = lowered_to(chain, identity);
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());

    let mut domain = DomainArena::new();
    let ran = eval_value(&core, &mut domain, definitions, ample(), endpoint)
        .expect("the running endpoint evaluates");
    assert_eq!(
        Some(TermFace::Source(unit)),
        domain.value(ran).map(DomainValue::face),
        "run, the endpoint unfolds `ident` and stands for the unit it returns"
    );

    let held = eval_value(
        &core,
        &mut domain,
        definitions.reading_endpoints(Endpoints::Hold),
        ample(),
        endpoint,
    )
    .expect("the held endpoint evaluates");
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(held)
    else {
        panic!("a held endpoint is a neutral");
    };
    let Some(NeutralHead::Returned(computation)) =
        domain.neutral(neutral).map(crate::domain::Neutral::head)
    else {
        panic!("headed by the computation it holds");
    };
    let Some(&DomainComp::Neutral { neutral: inner, .. }) = domain.computation(computation)
    else {
        panic!("which is stuck");
    };
    let inner = domain
        .neutral(inner)
        .expect("the computation's neutral resolves");
    assert_eq!(
        (
            NeutralHead::Constant(constant),
            Unfolding::Unforced(GlobalIndex::from(9_u32))
        ),
        (inner.head(), inner.unfolding()),
        "held, the endpoint waits on `ident`, its body unforced"
    );

    let manifest = eval_value(
        &core,
        &mut domain,
        definitions.reading_endpoints(Endpoints::Hold).manifest(),
        ample(),
        endpoint,
    )
    .expect("the manifest endpoint evaluates");
    assert_eq!(
        Some(TermFace::Source(unit)),
        domain.value(manifest).map(DomainValue::face),
        "the manifest reading of a held run runs the endpoint again"
    );
}

#[test]
fn a_run_goes_on_through_a_held_call_a_stuck_elimination_stands_on_3774()
{
    // `⟨force(⟨ident(t)⟩)⟩`, `ident` the manifest identity and `t` the thunk
    // of `return unit`. Held, `ident(t)` waits on `ident`, and the force sticks
    // on that held call.
    let mut core = CoreArena::new();
    let constant = ConstantIndex::from(0_usize);
    let reference = core.value_constant(constant);
    let variable = core.value_variable(Zone::Intuitionistic, innermost());
    let returned = core.computation_return(variable);
    let lambda = core.computation_lambda(returned);
    let identity = core.value_thunk(lambda);
    let unit = core.value_unit();
    let unit_returned = core.computation_return(unit);
    let suspended = core.value_thunk(unit_returned);
    let forced = core.computation_force(reference);
    let applied = core.computation_application(forced, suspended);
    let call = core.value_returned(applied);
    let stuck = core.computation_force(call);
    let endpoint = core.value_returned(stuck);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(
        constant,
        GlobalIndex::from(9_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok());
    let chain = lowered_to(chain, identity);
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());

    let mut domain = DomainArena::new();
    let held = eval_value(
        &core,
        &mut domain,
        definitions.reading_endpoints(Endpoints::Hold),
        ample(),
        endpoint,
    )
    .expect("the held endpoint evaluates");
    let (read, _left) =
        run_held(&core, &mut domain, definitions, ample(), held).expect("the held endpoint runs");
    assert_eq!(
        Some(TermFace::Source(unit)),
        read.and_then(|read| domain.value(read))
            .map(DomainValue::face),
        "the run goes on through the held `ident(t)` and returns what forcing `t` returns"
    );

    let empty = LoweredChain::new();
    let rigid = Definitions::new(&empty, &environment, environment.root());
    let held = eval_value(
        &core,
        &mut domain,
        rigid.reading_endpoints(Endpoints::Hold),
        ample(),
        endpoint,
    )
    .expect("the held endpoint evaluates");
    let (read, _left) =
        run_held(&core, &mut domain, rigid, ample(), held).expect("the held endpoint runs");
    assert_eq!(read, None, "with `ident` rigid the endpoint stays held");
}

#[test]
fn a_sealed_definition_is_rigid()
{
    let mut core = CoreArena::new();
    let constant = ConstantIndex::from(0_usize);
    let reference = core.value_constant(constant);

    let mut chain = DefinitionChain::new();
    let defined = chain.define(
        constant,
        GlobalIndex::from(9_u32),
        Transparency::Manifest,
        &[],
    );
    assert!(defined.is_ok());
    let chain = lowered_to(chain, reference);
    let mut environment = DefinitionalEnvironment::new();
    let outer = environment.root();
    let inner = environment.open_scope(outer).expect("the root resolves");
    let sealed = environment.state(outer, constant, Transparency::Opaque);
    assert_eq!(Ok(()), sealed);

    for (scope, expected) in [
        (inner, Unfolding::Rigid),
        (ScopeId::from(9_usize), Unfolding::Rigid),
    ] {
        let mut domain = DomainArena::new();
        let evaluated = eval_value(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            ample(),
            reference,
        )
        .expect("a constant evaluates to a neutral");
        let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
        else {
            panic!("a constant is stuck");
        };
        let held = domain.neutral(neutral).expect("the neutral resolves");
        assert_eq!(
            expected,
            held.unfolding(),
            "a seal in an enclosing scope, and a scope that was never opened, both \
                 degrade to rigidity rather than unfolding"
        );
    }
}

#[test]
fn an_ill_shaped_elimination_is_refused()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returner = core.computation_return(unit);
    let inner = core.computation_return(unit);
    let lambda = core.computation_lambda(inner);

    let forced_unit = core.computation_force(unit);
    let applied_returner = core.computation_application(returner, unit);
    let bound_lambda = core.computation_bind(lambda, returner);
    let cased_unit = core.computation_case(unit, &[returner, returner]);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);

    for (term, expected) in [
        (forced_unit, EvalFault::ForcedNonThunk),
        (applied_returner, EvalFault::AppliedNonFunction),
        (bound_lambda, EvalFault::BoundNonReturner),
        (cased_unit, EvalFault::CasedNonInjection),
    ] {
        let mut domain = DomainArena::new();
        assert_eq!(
            Err(expected),
            eval_computation(&core, &mut domain, definitions, ample(), term),
            "an eliminator meeting the wrong polarity of weak head is refused by name"
        );
    }

    let applied_unit = core.value_static_application(unit, unit);
    let mut domain = DomainArena::new();
    assert_eq!(
        Err(EvalFault::AppliedNonOperator),
        eval_value(&core, &mut domain, definitions, ample(), applied_unit),
        "a static application of a value that is no operator is refused by name"
    );
}

/// #2255: a lambda nested where a value is read stands for the thunk it is
/// suspended to, so a dependent position that forces and applies it reduces,
/// as `selfEquiv`'s bare components in `corpus/model/data/sigma-pair.gandr`
/// need.
#[test]
fn a_nested_lambda_forced_and_applied_reduces_2255()
{
    let mut core = CoreArena::new();
    // ⟨force ⟨λ. return v0⟩ ()⟩ ⇝ ().
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let returned = core.computation_return(bound);
    let lambda = core.computation_lambda(returned);
    let nested = core.value_nested(lambda);
    let forced = core.computation_force(nested);
    let unit = core.value_unit();
    let applied = core.computation_application(forced, unit);
    let read = core.value_returned(applied);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), read)
        .expect("a forced nested lambda evaluates");
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the reduct reads back");
    assert!(
        matches!(core.value(normal), Some(Value::Tuple(components)) if components.is_empty()),
        "the application reduced to the argument the lambda returns"
    );
}

#[test]
fn normalizes_beta_redex()
{
    let mut core = CoreArena::new();
    // (λX. ⌜El X × El X⌝) ⌜Integer⌝ ⇝ ⌜Integer × Integer⌝.
    let integer = core.value_type_base(BaseType::Integer);
    let argument = core.value_quote(integer);
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let decoded = core.value_type_element(bound, Level::zero());
    let doubled = core.value_type_product(&[decoded, decoded]);
    let body = core.value_quote(doubled);
    let operator = core.value_static_lambda(body);
    let redex = core.value_static_application(operator, argument);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), redex)
        .expect("a static redex evaluates");
    assert!(
        matches!(domain.value(evaluated), Some(&DomainValue::Code { .. })),
        "static beta fired: the weak head is the body's code, not a stuck application"
    );
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the reduct reads back");
    let Some(&Value::Quote(quoted)) = core.value(normal)
    else {
        panic!("the normal form is a quote");
    };
    let Some(held) = core.value_type(quoted)
    else {
        panic!("the quoted type is the body's product");
    };
    let ValueType::Product(ref components) = *held
    else {
        panic!("the quoted type is the body's product");
    };
    let [first, second] = **components
    else {
        panic!("the body's product is binary");
    };
    for component in [first, second] {
        assert_eq!(
            Some(&ValueType::Base(BaseType::Integer)),
            core.value_type(component),
            "each decode of the bound code reads as the argument's quoted type"
        );
    }
}

#[test]
fn normalization_preserves_a_stuck_application()
{
    let mut core = CoreArena::new();
    // F ((λX. X) ⌜Integer⌝) with F a constant that cannot unfold ⇝
    // F ⌜Integer⌝: the application stays, and its argument normalizes.
    let family = ConstantIndex::from(0_usize);
    let head = core.value_constant(family);
    let integer = core.value_type_base(BaseType::Integer);
    let quote = core.value_quote(integer);
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let identity = core.value_static_lambda(bound);
    let redex = core.value_static_application(identity, quote);
    let stuck = core.value_static_application(head, redex);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, ample(), stuck)
        .expect("a stuck application evaluates");
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(evaluated)
    else {
        panic!("an application of a rigid head is a neutral value");
    };
    let held = domain.neutral(neutral).expect("the neutral resolves");
    assert_eq!(
        NeutralHead::Constant(family),
        held.head(),
        "the neutral stands on the family's head"
    );
    assert!(
        matches!(held.spine(), [Elimination::StaticApply(_)]),
        "and carries the one static application"
    );
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("the stuck application reads back");
    let Some(&Value::StaticApplication(read_head, read_argument)) = core.value(normal)
    else {
        panic!("the normal form is still a static application");
    };
    assert_eq!(
        Some(&Value::Constant(family)),
        core.value(read_head),
        "its head is the family"
    );
    let Some(&Value::Quote(quoted)) = core.value(read_argument)
    else {
        panic!("its argument normalized past the inner redex to the quote");
    };
    assert_eq!(
        Some(&ValueType::Base(BaseType::Integer)),
        core.value_type(quoted),
        "and the quote carries the argument's type"
    );
}

#[test]
fn an_evaluation_in_a_supplied_environment_reports_its_remainder()
{
    let mut core = CoreArena::new();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let returner = core.computation_return(occurrence);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let definitions = Definitions::new(&chain, &environment, scope);
    let mut domain = DomainArena::new();
    let bound = domain.value_unit(TermFace::Reduced);
    let mut supplied = Environment::new();
    supplied.extend(Zone::Intuitionistic, bound);

    let budget = Fuel::from(10_u32);
    let (produced, remaining) =
        eval_comp_within(&core, &mut domain, definitions, budget, returner, supplied)
            .expect("the supplied environment answers the occurrence");
    let Some(&DomainComp::Return { value, .. }) = domain.computation(produced)
    else {
        panic!("the weak head is a returner");
    };
    assert_eq!(
        bound, value,
        "the run started from the environment it was handed rather than from the empty one"
    );
    assert_eq!(
        Fuel::from(7_u32),
        remaining,
        "three tasks ran — the returner, its value, and the returner's assembly frame — \
             and each spent exactly one unit of the budget"
    );

    assert_eq!(
        Err(EvalFault::UnboundVariable {
            zone: Zone::Intuitionistic,
            index: innermost(),
        }),
        eval_comp_within(
            &core,
            &mut domain,
            definitions,
            budget,
            returner,
            Environment::new(),
        ),
        "and the same body over the empty environment is refused, so the binding is what \
             answered it"
    );
}

#[test]
fn runtime_control_is_refused_by_former()
{
    use gandr_core_term::control::ControlFormer;
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let unit_type = core.value_type_unit();
    let returned = core.computation_return(unit);
    let stack = core.value_reify(alloc::sync::Arc::from([]));
    let signature = EffectSig::new(EffectName::from("State"), [EffectOp {
        name: OperationName::from("get"),
        payload: unit_type,
        reply: unit_type,
    }])
    .unwrap();
    let performed = core.computation_perform(signature.clone(), OperationName::from("get"), unit);
    let handled =
        core.computation_handle(signature, performed, returned, alloc::sync::Arc::from([]));
    let cases = [
        (performed, ControlFormer::Perform),
        (handled, ControlFormer::Handle),
        (
            core.computation_resume(stack, returned),
            ControlFormer::Resume,
        ),
        (core.computation_abandon(stack), ControlFormer::Abandon),
        (core.computation_reset(returned), ControlFormer::Reset),
        (core.computation_shift(returned), ControlFormer::Shift),
        (
            core.computation_with(&[returned, returned]),
            ControlFormer::With,
        ),
        (
            core.computation_project(gandr_kernel_term::Component::from(0_usize), returned),
            ControlFormer::Project,
        ),
    ];
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    for (term, former) in cases {
        assert_eq!(
            eval_computation(&core, &mut domain, definitions, ample(), term),
            Err(EvalFault::RuntimeControl(former))
        );
    }
    assert_eq!(
        eval_value(&core, &mut domain, definitions, ample(), stack),
        Err(EvalFault::RuntimeControl(ControlFormer::Reify))
    );
}

#[test]
fn a_loop_declines_on_fuel_rather_than_diverging()
{
    let mut core = CoreArena::new();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let inner_force = core.computation_force(occurrence);
    let self_application = core.computation_application(inner_force, occurrence);
    let lambda = core.computation_lambda(self_application);
    let looper = core.value_thunk(lambda);
    let outer_force = core.computation_force(looper);
    let omega = core.computation_application(outer_force, looper);

    let (chain, environment) = nothing_unfolds();
    let scope = environment.root();
    let mut domain = DomainArena::new();
    assert_eq!(
        Err(EvalFault::OutOfFuel),
        eval_computation(
            &core,
            &mut domain,
            Definitions::new(&chain, &environment, scope),
            Fuel::from(500_u32),
            omega,
        ),
        "beta and force alone loop, so the machine declines within its budget"
    );
}

#[test]
fn a_chain_lowers_each_body_once_in_admission_order()
{
    let mut core = CoreArena::new();
    let mut chain = DefinitionChain::new();
    let shared = GlobalIndex::from(5_u32);
    let own = GlobalIndex::from(6_u32);
    for (position, body) in [(0_usize, shared), (1_usize, own), (2_usize, shared)] {
        let defined = chain.define(
            ConstantIndex::from(position),
            body,
            Transparency::Manifest,
            &[],
        );
        assert!(defined.is_ok());
    }

    let mut asked = Vec::new();
    let Ok(lowered) = LoweredChain::lower(chain, |entry| {
        let lowered = core.value_unit();
        asked.push((entry.constant(), lowered));
        Ok::<_, Infallible>(lowered)
    });
    let &[(first, first_lowering), (second, second_lowering)] = asked.as_slice()
    else {
        panic!(
            "the pass asks once per distinct body index, so the third definition reuses \
                 the first one's lowering"
        );
    };
    assert_eq!(
        (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)),
        (first, second),
        "and it asks in admission order"
    );
    assert_eq!(
        (Some(&first_lowering), Some(&second_lowering)),
        (lowered.bodies().get(&shared), lowered.bodies().get(&own)),
        "each index reads as the lowering it was asked for"
    );
}

#[test]
fn a_refused_lowering_returns_no_chain()
{
    let mut chain = DefinitionChain::new();
    for (position, body) in [(0_usize, 0_u32), (1_usize, 1_u32)] {
        let defined = chain.define(
            ConstantIndex::from(position),
            GlobalIndex::from(body),
            Transparency::Manifest,
            &[],
        );
        assert!(defined.is_ok());
    }

    let mut core = CoreArena::new();
    let refused = LoweredChain::lower(chain, |entry| {
        if entry.constant() == ConstantIndex::from(1_usize) {
            Err(entry.constant())
        }
        else {
            Ok(core.value_unit())
        }
    });
    assert_eq!(
        Err(ConstantIndex::from(1_usize)),
        refused,
        "the first refusal is the answer, unchanged, and no partly lowered chain \
             escapes"
    );
}

#[test]
fn an_in_place_definition_equals_lowering_the_extended_chain()
{
    let mut core = CoreArena::new();
    let shared = GlobalIndex::from(5_u32);
    let own = GlobalIndex::from(6_u32);
    let first = core.value_unit();
    let second = core.value_unit();
    let third = core.value_unit();
    let rows = [
        (ConstantIndex::from(0_usize), shared, first),
        (ConstantIndex::from(1_usize), own, second),
        (ConstantIndex::from(3_usize), shared, third),
    ];
    let mut grown = LoweredChain::new();
    let mut chain = DefinitionChain::new();
    for (constant, body, lowered) in rows {
        assert_eq!(
            chain.define(constant, body, Transparency::Manifest, &[]),
            grown.define(constant, body, Transparency::Manifest, &[], lowered),
            "the in-place append answers the chain's own height"
        );
    }
    let Ok(whole) = LoweredChain::lower(chain, |entry| {
        Ok::<_, Infallible>(
            rows.iter()
                .find(|row| row.0 == entry.constant())
                .map_or(first, |row| row.2),
        )
    });
    assert_eq!(
        whole, grown,
        "three appends equal the extended chain lowered whole, the shared index keeping \
             its first lowering"
    );
    assert_eq!(
        Err(DefinitionError::AlreadyDefined {
            constant: ConstantIndex::from(1_usize)
        }),
        grown.define(
            ConstantIndex::from(1_usize),
            GlobalIndex::from(9_u32),
            Transparency::Manifest,
            &[],
            third,
        ),
        "a repeated position is refused"
    );
    assert_eq!(
        whole, grown,
        "and the refusal records neither an entry nor a body"
    );
}

#[test]
fn a_sliced_evaluation_agrees_with_an_unsliced_one()
{
    let mut core = CoreArena::new();
    let argument = core.value_unit();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let doubled = core.value_tuple(&[occurrence, occurrence]);
    let returned = core.computation_return(doubled);
    let lambda = core.computation_lambda(returned);
    let redex = core.computation_application(lambda, argument);
    let delayed = core.value_thunk(redex);

    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unsliced = eval_computation(&core, &mut domain, definitions, ample(), redex)
        .expect("a closed redex evaluates");
    let suspended = eval_value(&core, &mut domain, definitions, ample(), delayed)
        .expect("a thunk evaluates to its closure");
    let Some(&DomainValue::Thunk { body, .. }) = domain.value(suspended)
    else {
        panic!("a thunk evaluates to a thunk");
    };

    let mut sliced = Evaluation::enter(definitions, &domain, body, Bound::Nothing)
        .expect("the closure resolves");
    let answer = loop {
        let (progress, spent) = sliced
            .resume(&core, &mut domain, Fuel::from(1_u32))
            .expect("no slice of a closed redex is refused");
        assert!(
            u32::from(spent) <= 1_u32,
            "a slice never outspends its budget"
        );
        if let Progress::Finished(answer) = progress {
            break answer;
        }
    };

    let Glued::Computation(sliced) = answer
    else {
        panic!("an entered closure answers a computation");
    };
    assert_eq!(
        Ok(Settlement::StructurallyEqual),
        convert_computations(&core, &domain, unsliced, sliced),
        "and the paused run reached the weak head the uninterrupted one did"
    );
}

#[test]
fn a_reapplied_spine_fires_once_the_head_unfolds()
{
    let mut core = CoreArena::new();
    let function = ConstantIndex::from(0_usize);
    let injected = ConstantIndex::from(1_usize);
    let unit = core.value_unit();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let identity = core.computation_return(occurrence);
    let lambda = core.computation_lambda(identity);
    let function_body = core.value_thunk(lambda);
    let injected_body = core.value_injection(Side::Left.into(), unit);

    let function_reference = core.value_constant(function);
    let forced = core.computation_force(function_reference);
    let applied = core.computation_application(forced, unit);
    let passed_on = core.computation_return(occurrence);
    let bound = core.computation_bind(applied, passed_on);
    let injected_reference = core.value_constant(injected);
    let on_left = core.computation_return(occurrence);
    let on_right = core.computation_return(unit);
    let cased = core.computation_case(injected_reference, &[on_left, on_right]);

    let mut chain = DefinitionChain::new();
    for (constant, body) in [(function, 0_u32), (injected, 1_u32)] {
        let defined = chain.define(
            constant,
            GlobalIndex::from(body),
            Transparency::Manifest,
            &[],
        );
        assert!(defined.is_ok());
    }
    let Ok(chain) = LoweredChain::lower(chain, |entry| {
        Ok::<_, Infallible>(if entry.constant() == function {
            function_body
        }
        else {
            injected_body
        })
    });
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();

    for (stuck, head_body) in [(bound, function_body), (cased, injected_body)] {
        let evaluated = eval_computation(&core, &mut domain, definitions, ample(), stuck)
            .expect("an eliminator over an unforced constant gets stuck");
        let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
        else {
            panic!("the constant is not unfolded by evaluation, so the computation is stuck");
        };
        let spine = Vec::from(
            domain
                .neutral(neutral)
                .expect("the neutral resolves")
                .spine(),
        );
        let head = eval_value(&core, &mut domain, definitions, ample(), head_body)
            .expect("a definition body evaluates");

        let mut reapplied = Evaluation::eliminate(definitions, head, &spine);
        let (progress, _spent) = reapplied
            .resume(&core, &mut domain, ample())
            .expect("every elimination fits the unfolded head");
        let Progress::Finished(Glued::Computation(answer)) = progress
        else {
            panic!("an ample slice reaches the weak head, a computation");
        };
        let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
        else {
            panic!("every spine here ends in a returner once its head unfolds");
        };
        assert!(
            domain
                .value(value)
                .and_then(|held| domain.components(held))
                .is_some_and(<[_]>::is_empty),
            "the force, the application, the bind and the case each fired on the \
                 unfolded head in order"
        );
    }
}

#[test]
fn a_zero_slice_preserves_work_and_exact_completion_is_not_a_pause()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mut evaluation = Evaluation::body(definitions, unit);
    assert_eq!(
        Ok((Progress::Paused, Fuel::from(0_u32))),
        evaluation.resume(&core, &mut domain, Fuel::from(0_u32))
    );
    let (progress, spent) = evaluation
        .resume(&core, &mut domain, Fuel::from(1_u32))
        .expect("the unspent task is still available");
    assert_eq!(Fuel::from(1_u32), spent);
    let Progress::Finished(Glued::Value(value)) = progress
    else {
        panic!("draining on the last available step finishes rather than pauses");
    };
    assert_eq!(
        Some([].as_slice()),
        domain.value(value).and_then(|held| domain.components(held))
    );
    assert_eq!(Some(TermFace::Source(unit)), face_of(&domain, value));
}

#[test]
fn reapplied_eliminations_preserve_captures_and_argument_order()
{
    let mut core = CoreArena::new();
    let argument = core.value_variable(Zone::Intuitionistic, innermost());
    let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let pair = core.value_tuple(&[captured, argument]);
    let body = core.computation_return(pair);
    let pass = core.computation_return(argument);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let first = domain.value_unit(TermFace::Reduced);
    let second = domain.value_injection(Side::Left.into(), first, TermFace::Reduced);
    let supplied = domain.value_injection(Side::Right.into(), first, TermFace::Reduced);
    let mut left_capture = Environment::new();
    left_capture.extend(Zone::Intuitionistic, first);
    let mut right_capture = Environment::new();
    right_capture.extend(Zone::Intuitionistic, second);
    let on_left = domain.comp_closure_node(body, left_capture);
    let on_right = domain.comp_closure_node(body, right_capture);
    let left = domain.value_injection(Side::Left.into(), supplied, TermFace::Reduced);
    let right = domain.value_injection(Side::Right.into(), supplied, TermFace::Reduced);
    let mut returned_capture = Environment::new();
    returned_capture.extend(Zone::Intuitionistic, supplied);
    let returning = domain.comp_closure_node(pass, returned_capture);
    let thunk = domain.value_thunk(returning, TermFace::Reduced);
    let case = [Elimination::Case(domain.hold_branches([on_left, on_right]))];
    let bind = [Elimination::Force, Elimination::Bind(on_right)];
    for (head, spine, expected_capture) in [
        (left, case.as_slice(), first),
        (right, case.as_slice(), second),
        (thunk, bind.as_slice(), second),
    ] {
        let mut evaluation = Evaluation::eliminate(definitions, head, spine);
        let (progress, _spent) = evaluation
            .resume(&core, &mut domain, ample())
            .expect("the captured elimination has its operands");
        let Progress::Finished(Glued::Computation(answer)) = progress
        else {
            panic!("each elimination finishes at a returner");
        };
        let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
        else {
            panic!("the selected continuation returns its pair");
        };
        assert_eq!(
            Some([expected_capture, supplied].as_slice()),
            domain.value(value).and_then(|held| domain.components(held)),
            "the old capture stays outside the new argument, in the selected environment"
        );
        assert_eq!(Some(TermFace::Reduced), face_of(&domain, value));
    }
}

#[test]
fn reapplied_cases_refuse_only_when_the_selected_closure_is_missing()
{
    let mut core = CoreArena::new();
    let occurrence = core.value_variable(Zone::Intuitionistic, innermost());
    let body = core.computation_return(occurrence);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let value = domain.value_unit(TermFace::Reduced);
    let mut captured = Environment::new();
    captured.extend(Zone::Intuitionistic, value);
    let live = domain.comp_closure_node(body, captured);
    let left = domain.value_injection(Side::Left.into(), value, TermFace::Reduced);
    let right = domain.value_injection(Side::Right.into(), value, TermFace::Reduced);
    let boundary = domain.watermark();
    let missing = domain.comp_closure_node(body, Environment::new());
    domain.truncate_to(boundary);
    let spine = [Elimination::Case(domain.hold_branches([missing, live]))];
    let mut selected_live = Evaluation::eliminate(definitions, right, &spine);
    let (progress, _spent) = selected_live
        .resume(&core, &mut domain, ample())
        .expect("the unselected closure is not read");
    let Progress::Finished(Glued::Computation(answer)) = progress
    else {
        panic!("the live branch finishes");
    };
    assert_eq!(
        Some(&DomainComp::Return {
            value,
            face: CompTermFace::Reduced
        }),
        domain.computation(answer)
    );
    let mut selected_missing = Evaluation::eliminate(definitions, left, &spine);
    assert_eq!(
        Err(EvalFault::Domain(super::DomainFault::Dangling)),
        selected_missing.resume(&core, &mut domain, ample())
    );
}

#[test]
fn shared_configurations_distinguish_zones_but_ignore_unused_bindings()
{
    let mut core = CoreArena::new();
    let intuitionistic = core.value_variable(Zone::Intuitionistic, innermost());
    let linear = core.value_variable(Zone::Linear, innermost());
    let pair = core.value_tuple(&[intuitionistic, linear]);
    let term = super::CoreTerm::Value(pair);
    let mut indices = crate::free::FreeIndices::default();
    let free = indices
        .of(&core, term)
        .expect("both free indices resolve in the core")
        .clone();
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut machine = super::Machine::new(definitions, ample());
    machine.sharing.legs.insert(term, free);
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(TermFace::Reduced);
    let injection = domain.value_injection(Side::Left.into(), unit, TermFace::Reduced);
    for (first, second, unused, steps) in [
        (unit, injection, unit, 5_u32),
        (unit, injection, injection, 1_u32),
        (injection, unit, unit, 5_u32),
    ] {
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, unused);
        environment.extend(Zone::Intuitionistic, first);
        environment.extend(Zone::Linear, second);
        let env = machine.hold_env(environment);
        machine.tasks.push(super::Task::Value { term: pair, env });
        machine.fuel = ample();
        super::run(&core, &mut domain, &mut machine).expect("both free bindings are supplied");
        let result = machine.pop_value().expect("the leg produced its pair");
        assert_eq!(Some(TermFace::Reduced), face_of(&domain, result));
        assert_eq!(
            Some([first, second].as_slice()),
            domain
                .value(result)
                .and_then(|held| domain.components(held))
        );
        assert_eq!(
            steps,
            u32::from(ample()).saturating_sub(u32::from(machine.fuel))
        );
    }
}

#[test]
fn a_refused_evaluation_leaves_existing_values_usable()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let loose = core.value_variable(Zone::Linear, innermost());
    let pair = core.value_tuple(&[unit, loose]);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let existing = domain.value_unit(TermFace::Reduced);
    assert_eq!(
        Err(EvalFault::UnboundVariable {
            zone: Zone::Linear,
            index: innermost()
        }),
        eval_value(&core, &mut domain, definitions, ample(), pair)
    );
    assert_eq!(Some(TermFace::Reduced), face_of(&domain, existing));
    let retried = eval_value(&core, &mut domain, definitions, ample(), unit)
        .expect("a refused run does not poison later evaluation");
    assert_eq!(Some(TermFace::Source(unit)), face_of(&domain, retried));
    assert_eq!(
        Some([].as_slice()),
        domain
            .value(retried)
            .and_then(|held| domain.components(held))
    );
}

#[test]
fn ill_shaped_reapplied_spines_return_machine_faults()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let argument = domain.value_unit(TermFace::Reduced);
    let continuation = domain.comp_closure_node(body, Environment::new());
    let neutral = domain
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a rigid constant carries no body");
    let head = domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("the initial spine is a value spine");
    for spine in [
        [Elimination::Force, Elimination::Transport(argument)],
        [Elimination::Force, Elimination::ProductTransport(argument)],
        [Elimination::Force, Elimination::Force],
        [Elimination::Force, Elimination::StaticApply(argument)],
        [
            Elimination::StaticApply(argument),
            Elimination::Apply(argument),
        ],
        [
            Elimination::StaticApply(argument),
            Elimination::Bind(continuation),
        ],
        [
            Elimination::Force,
            Elimination::Case(domain.hold_branches([continuation, continuation])),
        ],
    ] {
        let mut evaluation = Evaluation::eliminate(definitions, head, &spine);
        assert_eq!(
            Err(EvalFault::MachineInvariant),
            evaluation.resume(&core, &mut domain, ample()),
            "an ill-shaped later elimination is a named refusal, not a contract panic"
        );
    }
}

#[test]
fn reapplied_closures_keep_stuck_spines_and_refuse_wrong_formers()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let pair = core.value_tuple(&[unit, unit]);
    let paired = core.computation_return(pair);
    let lambda = core.computation_lambda(returned);
    let suspended_lambda = core.value_thunk(lambda);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let argument = domain.value_unit(TermFace::Reduced);
    let on_left = domain.comp_closure_node(returned, Environment::new());
    let on_right = domain.comp_closure_node(paired, Environment::new());
    let neutral = domain
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::from([Elimination::StaticApply(argument)]),
            Unfolding::Rigid,
        )
        .expect("a rigid head can carry an existing static frame");
    let head = domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("the prefix still denotes a value");
    let bind = [Elimination::Force, Elimination::Bind(on_left)];
    let branches = domain.hold_branches([on_left, on_right]);
    let case = [Elimination::Case(branches)];
    let bound = [
        Elimination::StaticApply(argument),
        Elimination::Force,
        Elimination::Bind(on_left),
    ];
    let cased = [
        Elimination::StaticApply(argument),
        Elimination::Case(branches),
    ];
    for (spine, expected) in [
        (bind.as_slice(), bound.as_slice()),
        (case.as_slice(), cased.as_slice()),
    ] {
        let mut evaluation = Evaluation::eliminate(definitions, head, spine);
        let (progress, _spent) = evaluation
            .resume(&core, &mut domain, ample())
            .expect("a rigid head leaves its eliminations stuck");
        let Progress::Finished(Glued::Computation(answer)) = progress
        else {
            panic!("the eliminations produce a computation");
        };
        let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(answer)
        else {
            panic!("the result stays neutral");
        };
        assert_eq!(
            expected,
            domain
                .neutral(neutral)
                .expect("the grown spine resolves")
                .spine()
        );
    }
    let mut wrong_case = Evaluation::eliminate(definitions, argument, &case);
    assert_eq!(
        Err(EvalFault::CasedNonInjection),
        wrong_case.resume(&core, &mut domain, ample())
    );
    let thunk = eval_value(&core, &mut domain, definitions, ample(), suspended_lambda)
        .expect("the thunk captures the lambda");
    let mut wrong_bind = Evaluation::eliminate(definitions, thunk, &bind);
    assert_eq!(
        Err(EvalFault::BoundNonReturner),
        wrong_bind.resume(&core, &mut domain, ample())
    );
}

#[test]
fn native_records_and_cases_compute()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_core_term::ConstructorTag;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let left = core.value_injection(Side::Left.into(), unit);
    let right = core.value_injection(Side::Right.into(), unit);
    let pair = core.value_tuple(&[unit, unit]);
    let empty = core.value_record(BTreeMap::new());
    let labels = ["a", "b", "c", "d", "e"].map(|label| FieldLabel::from(String::from(label)));
    let source = core.value_record(
        labels
            .iter()
            .cloned()
            .zip([unit, left, right, pair, empty])
            .collect(),
    );
    let variables = [4_u32, 3, 2, 1, 0]
        .map(|index| core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
    let record = core.value_record(labels.iter().cloned().zip(variables).collect());
    let untaken = core.value_record(
        labels
            .iter()
            .cloned()
            .zip([unit, right, left, pair, empty])
            .collect(),
    );
    let mut selected = core.computation_return(record);
    let mut alternate = core.computation_return(untaken);
    for _ in 0 .. 5_u8 {
        selected = core.computation_lambda(selected);
        alternate = core.computation_lambda(alternate);
    }
    let unit_type = core.value_type_unit();
    let sum = core.value_type_sum(&[unit_type, unit_type]);
    let product = core.value_type_product(&[unit_type, unit_type]);
    let empty_type = core.value_type_record(BTreeMap::new());
    let record_type = core.value_type_record(
        labels
            .iter()
            .cloned()
            .zip([unit_type, sum, sum, product, empty_type])
            .collect(),
    );
    let motive = core.comp_type_returner(record_type);
    let datatype = core.value_type_data(ConstantIndex::from(2_usize), Vec::new());
    let fields = [unit, left, right, pair, empty];
    let constructor =
        core.value_constructor(datatype, ConstructorTag::from(1_usize), Vec::from(fields));
    let cased = core.computation_data_case(
        constructor,
        motive,
        Vec::from([alternate, selected]),
        [5_usize, 5]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("case returns its selected record");
    };
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        value,
    )
    .unwrap();
    let Some(matched_native_node) = core.value(normal)
    else {
        panic!("record readback");
    };
    let Value::Record(ref record) = *matched_native_node
    else {
        panic!("record readback");
    };
    assert!(record.keys().eq(labels.iter()));
    let mut actual = record.values().copied();
    assert!(
        core.value(actual.next().unwrap())
            .and_then(Value::components)
            .is_some_and(<[_]>::is_empty)
    );
    assert!(matches!(
        core.value(actual.next().unwrap()),
        Some(&Value::Injection(summand, _)) if summand == Side::Left.into()
    ));
    assert!(matches!(
        core.value(actual.next().unwrap()),
        Some(&Value::Injection(summand, _)) if summand == Side::Right.into()
    ));
    assert!(matches!(
        core.value(actual.next().unwrap())
            .and_then(Value::components),
        Some(&[_, _])
    ));
    assert!(
        matches!(core.value(actual.next().unwrap()),Some(Value::Record(fields)) if fields.is_empty())
    );
    let projection = core.computation_record_projection(source, labels[2].clone());
    let projected = eval_computation(&core, &mut domain, definitions, ample(), projection).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(projected)
    else {
        panic!("projection returns a field");
    };
    assert!(matches!(
        domain.value(value),
        Some(&DomainValue::Injection { summand, .. }) if summand == Side::Right.into()
    ));
    let absent =
        core.computation_record_projection(source, FieldLabel::from(String::from("absent")));
    let wrong_record = core.computation_record_projection(unit, labels[0].clone());
    let wrong_data = core.computation_data_case(
        unit,
        motive,
        Vec::from([alternate, selected]),
        [5_usize, 5]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let unknown =
        core.value_constructor(datatype, ConstructorTag::from(2_usize), Vec::from(fields));
    let unknown = core.computation_data_case(
        unknown,
        motive,
        Vec::from([alternate, selected]),
        [5_usize, 5]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    for (term, fault) in [
        (absent, EvalFault::AbsentRecordField),
        (wrong_record, EvalFault::ProjectedNonRecord),
        (wrong_data, EvalFault::CasedNonConstructor),
        (unknown, EvalFault::UnknownConstructor {
            tag: ConstructorTag::from(2_usize),
        }),
    ] {
        assert_eq!(
            eval_computation(&core, &mut domain, definitions, ample(), term),
            Err(fault)
        );
    }
    // Unselected suspended fields must stay unopened.
    let poison = core.value_thunk(wrong_record);
    let quiet = core.value_record(BTreeMap::from([
        (labels[0].clone(), poison),
        (labels[1].clone(), right),
    ]));
    let quiet = core.computation_record_projection(quiet, labels[1].clone());
    let projected = eval_computation(&core, &mut domain, definitions, ample(), quiet).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(projected)
    else {
        panic!("only the selected field returns");
    };
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        value,
    )
    .unwrap();
    assert!(matches!(
        core.value(normal),
        Some(&Value::Injection(summand, _)) if summand == Side::Right.into()
    ));
    let argument = core.value_variable(Zone::Intuitionistic, innermost());
    let identity = core.computation_return(argument);
    let identity = core.computation_lambda(identity);
    let identity = core.value_thunk(identity);
    let module = core.value_record(BTreeMap::from([
        (labels[0].clone(), poison),
        (labels[1].clone(), identity),
    ]));
    let selected = core.computation_record_projection(module, labels[1].clone());
    let forced = core.computation_force(argument);
    let applied = core.computation_application(forced, right);
    let applied = core.computation_bind(selected, applied);
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the projected function applies");
    };
    assert!(matches!(
        domain.value(value),
        Some(&DomainValue::Injection { summand, .. }) if summand == Side::Right.into()
    ));
    let poisoned = core.computation_record_projection(module, labels[0].clone());
    let poisoned = core.computation_bind(poisoned, forced);
    assert_eq!(
        eval_computation(&core, &mut domain, definitions, ample(), poisoned),
        Err(EvalFault::ProjectedNonRecord)
    );

    // A constructor's classifier closes over the argument, not merely its
    // value fields. Readback must substitute that captured value index.
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let indexed = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([bound]));
    let constructor =
        core.value_constructor(indexed, ConstructorTag::from(0_usize), Vec::from([source]));
    let returned = core.computation_return(constructor);
    let lambda = core.computation_lambda(returned);
    let applied = core.computation_application(lambda, unit);
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("constructor introduction");
    };
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        value,
    )
    .unwrap();
    let Some(matched_native_node) = core.value(normal)
    else {
        panic!("native constructor survives normalization");
    };
    let Value::Constructor {
        ref datatype,
        ref fields,
        ..
    } = *matched_native_node
    else {
        panic!("native constructor survives normalization");
    };
    let Some(matched_native_node) = core.value_type(*datatype)
    else {
        panic!("native classifier survives normalization");
    };
    let ValueType::Data {
        ref declaration,
        ref arguments,
    } = *matched_native_node
    else {
        panic!("native classifier survives normalization");
    };
    assert_eq!(*declaration, ConstantIndex::from(3_usize));
    assert!(
        matches!(arguments.as_slice(),[argument] if core.value(*argument) == Some(&Value::unit()))
    );
    assert!(
        matches!(fields.as_slice(),[field] if matches!(core.value(*field),Some(Value::Record(record)) if record.keys().eq(labels.iter())))
    );
}

/// A case over an indexed family hands its selected branch the constructor's
/// fields, then reflexivity at each index the constructor's classifier
/// states: `case C(left) : D(()) { λx. λe. return e }` returns `here(())`, the
/// equation at the constructor's own index rather than its field.
#[test]
fn an_indexed_case_supplies_its_equations()
{
    use gandr_core_term::ConstructorTag;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let left = core.value_injection(Side::Left.into(), unit);
    let equation = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(equation);
    let over_equation = core.computation_lambda(returned);
    let branch = core.computation_lambda(over_equation);
    let unit_type = core.value_type_unit();
    let motive = core.comp_type_returner(unit_type);
    let datatype = core.value_type_data(ConstantIndex::from(2_usize), Vec::from([unit]));
    let constructor =
        core.value_constructor(datatype, ConstructorTag::from(0_usize), Vec::from([left]));
    let cased = core.computation_data_case_with_equations(
        constructor,
        motive,
        (
            Vec::from([branch]),
            Vec::from([gandr_kernel_term::FieldCount::from(1_usize)]),
        ),
        gandr_kernel_term::EquationCount::from(1_usize),
    );
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), cased).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the branch returns its equation");
    };
    let normal = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        value,
    )
    .unwrap();
    let Some(&Value::Here(point)) = core.value(normal)
    else {
        panic!("the equation is reflexivity: {:?}", core.value(normal));
    };
    assert!(
        core.value(point)
            .and_then(Value::components)
            .is_some_and(<[_]>::is_empty),
        "reflexivity stands at the constructor's index, not at its field"
    );
}

/// Each component of a three-component tuple projects to itself; a
/// component past the last, a tuple projection of a record and a record
/// projection of a tuple each refuse by name.
#[test]
fn a_tuple_projection_reads_each_component()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_core_term::Component;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let left = core.value_injection(Side::Left.into(), unit);
    let pair = core.value_tuple(&[unit, unit]);
    let tuple = core.value_tuple(&[unit, left, pair]);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mut read = Vec::new();
    for position in 0 .. 3_usize {
        let projection = core.computation_tuple_projection(tuple, Component::from(position));
        let evaluated =
            eval_computation(&core, &mut domain, definitions, ample(), projection).unwrap();
        let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
        else {
            panic!("a projection returns its component");
        };
        read.push(
            readback_value(
                &mut core,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                ample(),
                value,
            )
            .unwrap(),
        );
    }
    let &[first, second, third] = read.as_slice()
    else {
        panic!("three components read back");
    };
    assert!(
        core.value(first)
            .and_then(Value::components)
            .is_some_and(<[_]>::is_empty)
    );
    assert!(matches!(
        core.value(second),
        Some(&Value::Injection(summand, _)) if summand == Side::Left.into()
    ));
    assert!(matches!(
        core.value(third).and_then(Value::components),
        Some(&[_, _])
    ));
    let past = core.computation_tuple_projection(tuple, Component::from(3_usize));
    let label = FieldLabel::from(String::from("a"));
    let record = core.value_record(BTreeMap::from([(label.clone(), unit)]));
    let of_record = core.computation_tuple_projection(record, Component::from(0_usize));
    let of_tuple = core.computation_record_projection(tuple, label);
    for (term, fault) in [
        (past, EvalFault::AbsentTupleComponent),
        (of_record, EvalFault::ProjectedNonTuple),
        (of_tuple, EvalFault::ProjectedNonRecord),
    ] {
        assert_eq!(
            eval_computation(&core, &mut domain, definitions, ample(), term),
            Err(fault)
        );
    }
}

/// A three-component split binds component zero outermost and the last
/// innermost, a split of the unit enters its body, and a split of
/// another arity or of a non-tuple refuses by name.
#[test]
fn a_split_binds_each_component_in_order()
{
    use gandr_core_term::ComponentCount;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let left = core.value_injection(Side::Left.into(), unit);
    let pair = core.value_tuple(&[unit, unit]);
    let tuple = core.value_tuple(&[unit, left, pair]);
    let last = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let middle = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let first = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let reordered = core.value_tuple(&[last, first, middle]);
    let body = core.computation_return(reordered);
    let split = core.computation_split(tuple, ComponentCount::from(3_usize), body);
    let (chain, environment) = nothing_unfolds();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), split).unwrap();
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the body returns");
    };
    let read = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        value,
    )
    .unwrap();
    let Some(&[was_last, was_first, was_middle]) = core.value(read).and_then(Value::components)
    else {
        panic!("the body's triple reads back");
    };
    assert!(matches!(
        core.value(was_last).and_then(Value::components),
        Some(&[_, _])
    ));
    assert!(
        core.value(was_first)
            .and_then(Value::components)
            .is_some_and(<[_]>::is_empty)
    );
    assert!(matches!(
        core.value(was_middle),
        Some(&Value::Injection(summand, _)) if summand == Side::Left.into()
    ));
    let entered = core.computation_return(left);
    let empty = core.computation_split(unit, ComponentCount::from(0_usize), entered);
    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), empty).unwrap();
    assert!(matches!(
        domain.computation(evaluated),
        Some(&DomainComp::Return { value, .. })
            if matches!(domain.value(value), Some(&DomainValue::Injection { .. }))
    ));
    let short = core.computation_split(tuple, ComponentCount::from(2_usize), entered);
    let of_injection = core.computation_split(left, ComponentCount::from(1_usize), entered);
    for (term, fault) in [
        (short, EvalFault::SplitArity),
        (of_injection, EvalFault::SplitNonTuple),
    ] {
        assert_eq!(
            eval_computation(&core, &mut domain, definitions, ample(), term),
            Err(fault)
        );
    }
}

#[test]
fn native_cases_reapply_when_head_unfolds()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_core_term::ConstructorTag;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let captured = core.value_injection(Side::Left.into(), unit);
    let field = core.value_injection(Side::Right.into(), unit);
    let label = FieldLabel::from(String::from("field"));
    let data = core.value_type_data(ConstantIndex::from(2_usize), Vec::new());
    let constructor =
        core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([field]));
    let record = core.value_record(BTreeMap::from([(label.clone(), field)]));
    let bound = core.value_variable(Zone::Intuitionistic, innermost());
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let motive_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([bound]));
    let motive = core.comp_type_returner(motive_type);
    let index = core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([bound]));
    let result_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([index]));
    let pair = core.value_tuple(&[outer, bound]);
    let result = core.value_constructor(
        result_type,
        ConstructorTag::from(0_usize),
        Vec::from([pair]),
    );
    let returned = core.computation_return(result);
    let branch = core.computation_lambda(returned);
    let data_reference = core.value_constant(ConstantIndex::from(0_usize));
    let record_reference = core.value_constant(ConstantIndex::from(1_usize));
    let cased = core.computation_data_case(
        data_reference,
        motive,
        Vec::from([branch]),
        [1_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
    let projected = core.computation_record_projection(record_reference, label);
    let mut chain = DefinitionChain::new();
    for (constant, entry) in [(0_usize, 0_u32), (1, 1)] {
        chain
            .define(
                ConstantIndex::from(constant),
                GlobalIndex::from(entry),
                Transparency::Manifest,
                &[],
            )
            .unwrap();
    }
    let Ok(chain) = LoweredChain::lower(chain, |entry| {
        Ok::<_, Infallible>(if entry.constant() == ConstantIndex::from(0_usize) {
            constructor
        }
        else {
            record
        })
    });
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let held = eval_value(&core, &mut domain, definitions, ample(), captured).unwrap();
    let mut supplied = Environment::new();
    supplied.extend(Zone::Intuitionistic, held);
    let (stuck, _) =
        eval_comp_within(&core, &mut domain, definitions, ample(), cased, supplied).unwrap();
    let normal = crate::readback::readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::ZeroUnfold,
        ample(),
        stuck,
    )
    .unwrap();
    let Some(matched_native_node) = core.computation(normal)
    else {
        panic!("stuck native case keeps its eliminator");
    };
    let gandr_core_term::Computation::DataCase { ref motive, .. } = *matched_native_node
    else {
        panic!("stuck native case keeps its eliminator");
    };
    let Some(matched_native_node) = core.comp_type(*motive)
    else {
        panic!("motive returns a value");
    };
    let gandr_core_term::CompType::Returner {
        result: ref motive, ..
    } = *matched_native_node
    else {
        panic!("motive returns a value");
    };
    let Some(matched_native_node) = core.value_type(*motive)
    else {
        panic!("dependent motive");
    };
    let ValueType::Data { ref arguments, .. } = *matched_native_node
    else {
        panic!("dependent motive");
    };
    assert!(
        matches!(arguments.as_slice(),[argument] if matches!(core.value(*argument),Some(Value::Variable {zone:Zone::Intuitionistic,index}) if *index == innermost())),
        "the motive's scrutinee binder must not become the captured value"
    );
    let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(stuck)
    else {
        panic!("constant head is initially stuck");
    };
    let spine = Vec::from(domain.neutral(neutral).unwrap().spine());
    let head = eval_value(&core, &mut domain, definitions, ample(), constructor).unwrap();
    let (progress, _) = Evaluation::eliminate(definitions, head, &spine)
        .resume(&core, &mut domain, ample())
        .unwrap();
    let Progress::Finished(Glued::Computation(answer)) = progress
    else {
        panic!("case reapplication finishes");
    };
    let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
    else {
        panic!("case returns its branch result");
    };
    let Some(&DomainValue::Constructor { fields, .. }) = domain.value(value)
    else {
        panic!("native result");
    };
    let [ref pair] = *(domain.fields(fields).unwrap())
    else {
        panic!("one result field");
    };
    let Some(&[first, second]) = domain.value(*pair).and_then(|held| domain.components(held))
    else {
        panic!("capture and payload pair");
    };
    assert!(matches!(
        domain.value(first),
        Some(&DomainValue::Injection { summand, .. }) if summand == Side::Left.into()
    ));
    assert!(matches!(
        domain.value(second),
        Some(&DomainValue::Injection { summand, .. }) if summand == Side::Right.into()
    ));
    let projected = eval_computation(&core, &mut domain, definitions, ample(), projected).unwrap();
    let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(projected)
    else {
        panic!("record constant is initially stuck");
    };
    let spine = Vec::from(domain.neutral(neutral).unwrap().spine());
    let head = eval_value(&core, &mut domain, definitions, ample(), record).unwrap();
    let (progress, _) = Evaluation::eliminate(definitions, head, &spine)
        .resume(&core, &mut domain, ample())
        .unwrap();
    let Progress::Finished(Glued::Computation(answer)) = progress
    else {
        panic!("projection reapplication finishes");
    };
    let Some(&DomainComp::Return { value, .. }) = domain.computation(answer)
    else {
        panic!("projection returns its field");
    };
    assert!(matches!(
        domain.value(value),
        Some(&DomainValue::Injection { summand, .. }) if summand == Side::Right.into()
    ));
}
