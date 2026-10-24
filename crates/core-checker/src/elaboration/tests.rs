//! Executable route laws, separately from the kernel's typing oracle.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_term::Binders;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Outcome;
use super::Output;
use super::ResumeError;
use super::Session;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::Declaration;
use crate::DeclarationContent;
use crate::Mismatch;
use crate::OriginToken;
use crate::TypeNode;
use crate::Verdict;
use crate::body;
use crate::bridge;
use crate::check_module;
use crate::fixture::Mode;
use crate::fixture::integer_literal;
use crate::fixture::term_recipe;
use crate::fixture::typed_recipe;
use crate::refusal::Unsolved;
use crate::signature;

/// A fixture admission position, distinct from counts.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct At(usize);

/// Mint a signed fixture declaration at its origin.
///
/// # Specification
/// trivial.
fn declaration(
    at: At,
    declared: ValueTypeId,
    body: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(at.0),
        Maybe::Present(declared),
        body,
        OriginToken::from(at.0),
    )
}

/// The type a signed fixture declaration states.
///
/// # Specification
/// trivial.
fn signed(declaration: &Declaration) -> ValueTypeId
{
    match *declaration.content() {
        DeclarationContent::Value {
            signature: Maybe::Present(declared),
            ..
        } => declared,
        ref other @ (DeclarationContent::Value { .. }
        | DeclarationContent::Data(_)
        | DeclarationContent::Codata(_)
        | DeclarationContent::Abstract(_)
        | DeclarationContent::World) => {
            panic!("a signed value declaration, got {other:?}")
        },
    }
}

/// Extract checked output, refusing any weakening to a non-error assertion.
///
/// # Specification
/// trivial.
fn checked(entry: &super::Entry) -> Output
{
    match *entry.outcome() {
        Outcome::Checked(output) => output,
        ref other @ (Outcome::Formed
        | Outcome::Owed(_)
        | Outcome::Suspended(_)
        | Outcome::Refused(_)) => panic!("expected Checked, got {other:?}"),
    }
}

/// The route's hole, two independent suspensions, and a stable dependent.
struct Route
{
    /// Declarations ordered by admission position.
    declarations: Vec<Declaration>,
    /// The legitimate code filling the first declaration.
    filling: ValueId,
    /// The rigid integer type.
    integer: ValueTypeId,
    /// The hole's decoded type.
    decoded: ValueTypeId,
    /// The literal both suspensions eventually emit.
    literal: ValueId,
}

/// Build the substitution law's finite model.
///
/// # Specification
/// trivial.
fn route(arena: &mut CoreArena) -> Route
{
    let universe = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let filling = arena.value_quote(integer);
    let hole = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.value_type_element(hole, Level::zero());
    let literal = arena.value_literal(integer_literal());
    let result = arena.comp_type_returner(decoded);
    let arrow = arena.comp_type_arrow(decoded, result);
    let identity_type = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let declarations = Vec::from([
        declaration(At(0), universe, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), decoded, Maybe::Present(literal)),
        declaration(At(2), decoded, Maybe::Present(literal)),
        declaration(At(3), identity_type, Maybe::Present(identity)),
    ]);
    Route {
        declarations,
        filling,
        integer,
        decoded,
        literal,
    }
}

/// Check every published answer with the independent kernel: one readmission
/// per entry, each the kernel's answer for its outcome — a static definition
/// staying on the checker's side.
///
/// # Specification
/// trivial.
fn assert_readmitted(session: &mut Session<'_>)
{
    let readmission = session.readmit();
    assert_eq!(
        readmission.readmitted().len(),
        session.entries().len(),
        "one readmission per entry"
    );
    for (entry, replay) in session.entries().iter().zip(readmission.readmitted()) {
        assert_eq!(replay.constant(), entry.constant());
        match (entry.outcome(), replay.outcome()) {
            (
                &Outcome::Checked(_),
                &(bridge::Outcome::Defined { .. } | bridge::Outcome::Static),
            )
            | (&Outcome::Formed, &bridge::Outcome::Data { .. })
            | (&Outcome::Owed(_), &bridge::Outcome::Assumed { .. })
            | (&Outcome::Suspended(_), &bridge::Outcome::Suspended) => {},
            (&Outcome::Refused(expected), &bridge::Outcome::Marked(actual)) => {
                assert_eq!(expected, actual);
            },
            (outcome, replay) => panic!("{outcome:?} readmitted as {replay:?}"),
        }
    }
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config {
        cases: 256,
        rng_seed: proptest::test_runner::RngSeed::Fixed(0x656c_6162),
        ..proptest::test_runner::Config::default()
    })]

    #[test]
    fn every_fixture_the_checker_accepts_is_readmitted(typed in typed_recipe(), free in term_recipe()) {
        // Construction 4.3 and the typed combinators: output inhabits its type.
        // Extends the existing checker corpus to the actual emitted terms.
        let mut arena = CoreArena::new();
        let terms = typed.build(&mut arena);
        let mut declarations = Vec::new();
        for declared in terms.constants {
            declarations.push(declaration(At(declarations.len()), declared, Maybe::Absent(body::Absent::Hole)));
        }
        for (body, declared, mode) in terms.values {
            declarations.push(declaration(At(declarations.len()), declared, Maybe::Present(body)));
            if mode == Mode::Synthesising {
                declarations.push(Declaration::new(ConstantIndex::from(declarations.len()), Maybe::Absent(signature::Absent::Unsigned), Maybe::Present(body), OriginToken::from(declarations.len())));
            }
        }
        for (body, declared, _) in terms.comps {
            let body = arena.value_thunk(body);
            let declared = arena.value_type_thunk(declared);
            declarations.push(declaration(At(declarations.len()), declared, Maybe::Present(body)));
        }
        let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
        assert!(session.entries().iter().all(|entry| matches!(entry.outcome(), Outcome::Checked(_) | Outcome::Owed(_))));
        assert_readmitted(&mut session);

        let mut arena = CoreArena::new();
        let terms = free.build(&mut arena);
        let declarations: Vec<_> = terms.values.iter().enumerate().map(|(position, &body)| Declaration::new(ConstantIndex::from(position), Maybe::Absent(signature::Absent::Unsigned), Maybe::Present(body), OriginToken::from(position))).collect();
        let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
        assert_readmitted(&mut session);
    }
}

#[test]
fn judgemental_equality_leaves_output_unchanged()
{
    // Construction 4.3 conv, §4.5 judgmental invariance: same body, equal type.
    let mut arena = CoreArena::new();
    let mut fixture = route(&mut arena);
    fixture.declarations[0] = declaration(
        At(0),
        signed(&fixture.declarations[0]),
        Maybe::Present(fixture.filling),
    );
    fixture.declarations[2] = declaration(At(2), fixture.integer, Maybe::Present(fixture.literal));
    let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
    assert_eq!(checked(&session.entries()[1]).body(), fixture.literal);
    assert_eq!(
        checked(&session.entries()[1]).body(),
        checked(&session.entries()[2]).body()
    );
    assert_readmitted(&mut session);
}

#[test]
fn owed_conversion_suspends()
{
    // Exegesis 6.6: absence of an identity solution is suspension, not failure,
    // in the checker's own report as in the term-producing run.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &fixture.declarations)
    };
    let Verdict::Suspended(declared) = report.judged()[1].verdict()
    else {
        panic!(
            "the checker suspends an owed decode: {:?}",
            report.judged()[1].verdict()
        );
    };
    assert_eq!(declared.id(), fixture.decoded);
    assert_eq!(report.ledger().entries().len(), 1, "only the hole is owed");
    let readmission = bridge::readmit(&mut arena, &report);
    assert_eq!(
        readmission.readmitted()[1].outcome(),
        &bridge::Outcome::Suspended,
        "the kernel is offered nothing for a waiting declaration"
    );
    let checker = report.suspensions()[&ConstantIndex::from(1_usize)].clone();
    let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
    let Outcome::Suspended(ref suspension) = *session.entries()[1].outcome()
    else {
        panic!("owed decode must suspend");
    };
    // One rule machine: the checker and the term-producing run record the same
    // suspension, the rigid side minted afresh by each judgement.
    for waiting in [&checker, suspension] {
        assert_eq!(waiting.declared().id(), fixture.decoded);
        assert_eq!(
            waiting.blockers(),
            &BTreeSet::from([ConstantIndex::from(0_usize)])
        );
        assert!(waiting.dependencies().is_empty());
        let &[equation] = waiting.equations()
        else {
            panic!("exactly one residual");
        };
        assert_eq!(equation.hole(), ConstantIndex::from(0_usize));
        assert_eq!(equation.flex(), TypeNode::Value(fixture.decoded));
        assert_eq!(
            session.arena().value_type(match equation.rigid() {
                TypeNode::Value(id) => id,
                TypeNode::Computation(_) => panic!("value comparison"),
            }),
            Some(&ValueType::Base(BaseType::Integer))
        );
    }
    assert_readmitted(&mut session);
}

#[test]
fn incremental_equals_from_scratch()
{
    // Theorem 5.1 multilinearity / presheaf naturality: substitution commutes
    // with elaboration. Compare exact emitted body, then the typed artifact.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let incremental = {
        let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
        session
            .fill(ConstantIndex::from(0_usize), fixture.filling)
            .expect("valid fill");
        session
            .resume(ConstantIndex::from(1_usize))
            .expect("resume first");
        session
            .resume(ConstantIndex::from(2_usize))
            .expect("resume second");
        assert_eq!(checked(&session.entries()[1]).body(), fixture.literal);
        assert_readmitted(&mut session);
        session
            .readmit()
            .export(alloc::collections::BTreeMap::new())
    };
    let mut declarations = fixture.declarations;
    declarations[0] = declaration(
        At(0),
        signed(&declarations[0]),
        Maybe::Present(fixture.filling),
    );
    let mut batch = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert_eq!(checked(&batch.entries()[1]).body(), fixture.literal);
    assert_readmitted(&mut batch);
    assert_eq!(
        incremental,
        batch.readmit().export(alloc::collections::BTreeMap::new())
    );
}

#[test]
fn resumptions_commute()
{
    // Lemma 3.19 / §1.2.5: commuting partiality actions, not just well-typedness.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let mut artifacts = Vec::new();
    for order in [[1_usize, 2_usize], [2_usize, 1_usize]] {
        let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
        session
            .fill(ConstantIndex::from(0_usize), fixture.filling)
            .expect("valid fill");
        for position in order {
            session
                .resume(ConstantIndex::from(position))
                .expect("resume");
        }
        assert_eq!(checked(&session.entries()[1]).body(), fixture.literal);
        assert_eq!(checked(&session.entries()[2]).body(), fixture.literal);
        artifacts.push(
            session
                .readmit()
                .export(alloc::collections::BTreeMap::new()),
        );
    }
    assert_eq!(artifacts[0], artifacts[1]);
}

#[test]
fn checked_success_is_stable_without_rejudgement()
{
    // Exegesis 6.6's successful sieve contains identity and all substitutions.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
    let before = session.entries()[3].clone();
    let _ = checked(&before);
    assert_eq!(usize::from(before.judgements()), 1);
    session
        .fill(ConstantIndex::from(0_usize), fixture.filling)
        .expect("valid fill");
    for position in [3_usize, 2_usize, 1_usize, 3_usize] {
        session
            .resume(ConstantIndex::from(position))
            .expect("resume");
    }
    assert_eq!(
        session.entries()[3],
        before,
        "type-dependent identity is adopted, not rejudged"
    );
    assert_readmitted(&mut session);
}

#[test]
fn refused_subterms_refuse_the_declaration()
{
    // Corollary 5.2 multistrictness: a refused argument poisons its application,
    // then its enclosing returner thunk; the good neighboring term still checks.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let result = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, result);
    let function = arena.value_type_thunk(arrow);
    let thunk_type = arena.value_type_thunk(result);
    let head = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.computation_force(head);
    let wrong = arena.value_unit();
    let body = arena.computation_application(head, wrong);
    let body = arena.value_thunk(body);
    let literal = arena.value_literal(integer_literal());
    let declarations = [
        declaration(At(0), function, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), thunk_type, Maybe::Present(body)),
        declaration(At(2), integer, Maybe::Present(literal)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    let Outcome::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, expected, .. })) =
        *session.entries()[1].outcome()
    else {
        panic!("argument mismatch must propagate");
    };
    assert_eq!(at, wrong);
    assert_eq!(expected, integer);
    assert_eq!(checked(&session.entries()[2]).body(), literal);
    assert_readmitted(&mut session);
}

#[test]
fn only_bare_flex_rigid_equations_suspend()
{
    // Exegesis 6.6, bounded route: no flex-flex solving and no invented clash.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let universe = signed(&fixture.declarations[0]);
    let other_hole = arena.value_constant(ConstantIndex::from(1_usize));
    let other_decoded = arena.value_type_element(other_hole, Level::zero());
    let value_hole = arena.value_constant(ConstantIndex::from(2_usize));
    let declarations = [
        fixture.declarations[0].clone(),
        declaration(At(1), universe, Maybe::Absent(body::Absent::Hole)),
        declaration(At(2), fixture.decoded, Maybe::Absent(body::Absent::Hole)),
        declaration(At(3), fixture.integer, Maybe::Present(value_hole)),
        declaration(At(4), other_decoded, Maybe::Present(value_hole)),
    ];
    let session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert!(
        matches!(session.entries()[3].outcome(), Outcome::Suspended(_)),
        "reverse orientation"
    );
    assert!(
        matches!(
            session.entries()[4].outcome(),
            Outcome::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "flex-flex is outside the suspension fragment"
    );
}

#[test]
fn residual_conjunction_does_not_hide_refusal()
{
    // Theorem 5.1 and Corollary 5.2: conjunction retains both residuals, but
    // a later false premise is not erased by an earlier suspended premise.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let pair_type = arena.value_type_product(&[fixture.decoded, fixture.integer]);
    let wrong = arena.value_unit();
    let pair = arena.value_tuple(&[fixture.literal, wrong]);
    let pair_both_type = arena.value_type_product(&[fixture.decoded, fixture.decoded]);
    let good_pair = arena.value_tuple(&[fixture.literal, fixture.literal]);
    let declarations = [
        fixture.declarations[0].clone(),
        declaration(At(1), pair_type, Maybe::Present(pair)),
        declaration(At(2), pair_both_type, Maybe::Present(good_pair)),
    ];
    let session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert!(
        matches!(*session.entries()[1].outcome(), Outcome::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == wrong)
    );
    let Outcome::Suspended(ref suspension) = *session.entries()[2].outcome()
    else {
        panic!("two equal residual obligations remain conditional");
    };
    assert_eq!(
        suspension.blockers(),
        &BTreeSet::from([ConstantIndex::from(0_usize)])
    );
}

#[test]
fn invalid_fills_leave_entries_unchanged()
{
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
    let before = session.entries().to_vec();
    assert_eq!(
        session.fill(ConstantIndex::from(90_usize), fixture.filling),
        Err(ResumeError::Unknown(ConstantIndex::from(90_usize)))
    );
    assert_eq!(
        session.fill(ConstantIndex::from(3_usize), fixture.filling),
        Err(ResumeError::NotOwed(ConstantIndex::from(3_usize)))
    );
    assert!(matches!(
        session.fill(ConstantIndex::from(0_usize), fixture.literal),
        Err(ResumeError::Refused(CheckRefusal::TypeMismatch(_)))
    ));
    assert_eq!(session.entries(), before);
}

#[test]
fn outputs_materialize_nested_lifts()
{
    // Construction 4.3 conv preserves the runtime term, while universe
    // cumulativity's explicit code transport belongs to the output syntax.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let large = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::constant(gandr_kernel_strata::LevelConstant::from(1_u64)),
    );
    let result = arena.comp_type_returner(unit);
    let arrow = arena.comp_type_arrow(large, result);
    let function = arena.value_type_thunk(arrow);
    let suspended = arena.value_type_thunk(result);
    let function_body = arena.value_unit();
    let function_body = arena.computation_return(function_body);
    let function_body = arena.computation_lambda(function_body);
    let function_body = arena.value_thunk(function_body);
    let head = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.computation_force(head);
    let argument = arena.value_quote(unit);
    let application = arena.computation_application(head, argument);
    let body = arena.value_thunk(application);
    let declarations = [
        declaration(At(0), function, Maybe::Present(function_body)),
        declaration(At(1), suspended, Maybe::Present(body)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    let output = checked(&session.entries()[1]).body();
    assert_ne!(
        output, body,
        "lifted argument must be emitted, not kept in a side table"
    );
    let Some(&Value::Thunk(application)) = session.arena().value(output)
    else {
        panic!("thunk output");
    };
    let Some(&Computation::Application(_, argument)) = session.arena().computation(application)
    else {
        panic!("application output");
    };
    let Some(&Value::Quote(lifted)) = session.arena().value(argument)
    else {
        panic!("explicit code lift");
    };
    assert_eq!(
        session.arena().value_type(lifted),
        Some(&ValueType::Lift {
            inner: unit,
            target: Level::constant(gandr_kernel_strata::LevelConstant::from(1_u64))
        })
    );
    assert_readmitted(&mut session);
}

#[test]
fn dependent_resumption_closes_its_prerequisites()
{
    // Theorem 5.1: composition's support is the conjunction of premise supports.
    let mut arena = CoreArena::new();
    let mut fixture = route(&mut arena);
    let reference = arena.value_constant(ConstantIndex::from(1_usize));
    fixture.declarations.push(declaration(
        At(4),
        fixture.decoded,
        Maybe::Present(reference),
    ));
    let mut artifacts = Vec::new();
    for order in [[4_usize, 1_usize, 2_usize], [1_usize, 2_usize, 4_usize]] {
        let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
        let Outcome::Suspended(ref suspended) = *session.entries()[4].outcome()
        else {
            panic!("conditional reference");
        };
        assert_eq!(
            suspended.dependencies(),
            &BTreeSet::from([ConstantIndex::from(1_usize)])
        );
        session
            .fill(ConstantIndex::from(0_usize), fixture.filling)
            .expect("fill");
        for position in order {
            session
                .resume(ConstantIndex::from(position))
                .expect("resume dependency closure");
        }
        assert_eq!(checked(&session.entries()[4]).body(), reference);
        assert_eq!(usize::from(session.entries()[1].judgements()), 2);
        assert_readmitted(&mut session);
        artifacts.push(
            session
                .readmit()
                .export(alloc::collections::BTreeMap::new()),
        );
    }
    assert_eq!(artifacts[0], artifacts[1]);
}

#[test]
fn computation_bridge_and_bind_resume_under_binders()
{
    // Construction 4.3 conv and Theorem 5.1's binding combinators: transport
    // through a computation bridge and under a non-dependent bind agrees.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let rigid = arena.comp_type_returner(fixture.integer);
    let flexible = arena.comp_type_returner(fixture.decoded);
    let rigid = arena.value_type_thunk(rigid);
    let flexible = arena.value_type_thunk(flexible);
    let reference = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(reference);
    let bridged = arena.value_thunk(forced);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(variable);
    let bound = arena.computation_bind(forced, returned);
    let bound = arena.value_thunk(bound);
    let declarations = [
        fixture.declarations[0].clone(),
        declaration(At(1), rigid, Maybe::Absent(body::Absent::Hole)),
        declaration(At(2), flexible, Maybe::Present(bridged)),
        declaration(At(3), flexible, Maybe::Present(bound)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    for position in [2_usize, 3_usize] {
        let Outcome::Suspended(ref suspension) = *session.entries()[position].outcome()
        else {
            panic!("bridge and bind must suspend");
        };
        assert_eq!(
            suspension.blockers(),
            &BTreeSet::from([ConstantIndex::from(0_usize)])
        );
    }
    session
        .fill(ConstantIndex::from(0_usize), fixture.filling)
        .expect("fill");
    for position in [3_usize, 2_usize] {
        session
            .resume(ConstantIndex::from(position))
            .expect("resume");
    }
    assert_eq!(checked(&session.entries()[2]).body(), bridged);
    assert_eq!(checked(&session.entries()[3]).body(), bound);
    assert_readmitted(&mut session);
}

#[test]
fn spined_holes_do_not_enter_the_residual_fragment()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let operator = arena.value_type_static_pi(universe, universe);
    let integer = arena.value_type_base(BaseType::Integer);
    let argument = arena.value_quote(integer);
    let hole = arena.value_constant(ConstantIndex::from(0_usize));
    let application = arena.value_static_application(hole, argument);
    let decoded = arena.value_type_element(application, Level::zero());
    let literal = arena.value_literal(integer_literal());
    let declarations = [
        declaration(At(0), operator, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), decoded, Maybe::Present(literal)),
    ];
    let session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert!(
        matches!(session.entries()[1].outcome(), &Outcome::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == literal)
    );
}

#[test]
fn shared_code_occurrences_keep_distinct_transports()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let small = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let large = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::constant(gandr_kernel_strata::LevelConstant::from(1_u64)),
    );
    let result = arena.comp_type_returner(unit);
    let second = arena.comp_type_arrow(small, result);
    let first = arena.comp_type_arrow(large, second);
    let function = arena.value_type_thunk(first);
    let suspended = arena.value_type_thunk(result);
    let head = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.computation_force(head);
    let argument = arena.value_quote(unit);
    let first = arena.computation_application(head, argument);
    let second = arena.computation_application(first, argument);
    let body = arena.value_thunk(second);
    let declarations = [
        declaration(At(0), function, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), suspended, Maybe::Present(body)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert_readmitted(&mut session);
}

#[test]
fn filling_through_a_suspended_dependency_reports_only_still_owed_blockers()
{
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let reference = arena.value_constant(ConstantIndex::from(1_usize));
    let declarations = [
        fixture.declarations[0].clone(),
        fixture.declarations[1].clone(),
        declaration(At(2), fixture.integer, Maybe::Absent(body::Absent::Hole)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    let Err(ResumeError::Suspended(before)) = session.fill(ConstantIndex::from(2_usize), reference)
    else {
        panic!("the filling depends on a suspended declaration");
    };
    assert_eq!(
        before.blockers(),
        &BTreeSet::from([ConstantIndex::from(0_usize)])
    );
    session
        .fill(ConstantIndex::from(0_usize), fixture.filling)
        .expect("fill the code hole");
    let entries = session.entries().to_vec();
    let Err(ResumeError::Suspended(after)) = session.fill(ConstantIndex::from(2_usize), reference)
    else {
        panic!("the prerequisite still needs resumption");
    };
    assert_eq!(after.blockers(), &BTreeSet::new());
    assert_eq!(
        after.dependencies(),
        &BTreeSet::from([ConstantIndex::from(1_usize)])
    );
    assert_eq!(session.entries(), entries);
    session
        .resume(ConstantIndex::from(1_usize))
        .expect("resume prerequisite");
    session
        .fill(ConstantIndex::from(2_usize), reference)
        .expect("fill dependent hole");
    assert_eq!(checked(&session.entries()[2]).body(), reference);
    assert_readmitted(&mut session);
}

#[test]
fn every_fragment_former_carries_a_nested_lift()
{
    // Construction 4.3 conv: a code checked above its own universe is
    // transported where it stands, under whichever former of the fragment
    // holds it, and the kernel readmits the output.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let unit_value = arena.value_unit();
    let large = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::constant(gandr_kernel_strata::LevelConstant::from(1_u64)),
    );
    let choice = arena.value_type_sum(&[unit, unit]);
    let operator = arena.value_type_static_pi(large, large);
    let returns_large = arena.comp_type_returner(large);
    let suspended = arena.value_type_thunk(returns_large);
    let from_unit = arena.comp_type_arrow(unit, returns_large);
    let function = arena.value_type_thunk(from_unit);
    let pair = arena.value_type_product(&[large, unit]);
    let tagged = arena.value_type_sum(&[large, unit]);
    let code = arena.value_quote(unit);
    let returned = arena.computation_return(code);
    let tuple = arena.value_tuple(&[code, unit_value]);
    let injection = arena.value_injection(gandr_core_term::Summand::from(0_usize), code);
    let thunk = arena.value_thunk(returned);
    let lambda = arena.computation_lambda(returned);
    let lambda = arena.value_thunk(lambda);
    let returns_unit = arena.comp_type_returner(unit);
    let held_unit = arena.value_type_thunk(returns_unit);
    let first = arena.value_constant(ConstantIndex::from(2_usize));
    let first = arena.computation_force(first);
    let bind = arena.computation_bind(first, returned);
    let bind = arena.value_thunk(bind);
    let scrutinee = arena.value_constant(ConstantIndex::from(0_usize));
    let case = arena.computation_case(scrutinee, &[returned, returned]);
    let case = arena.value_thunk(case);
    let ascribed = arena.computation_ascribe(returned, returns_large);
    let ascribed = arena.value_thunk(ascribed);
    let head = arena.value_constant(ConstantIndex::from(1_usize));
    let applied = arena.value_static_application(head, code);
    let abstraction = arena.value_static_lambda(code);
    let cases = [
        ("a tuple", pair, tuple),
        ("an injection", tagged, injection),
        ("a return", suspended, thunk),
        ("a lambda", function, lambda),
        ("a bind", suspended, bind),
        ("a case", suspended, case),
        ("an ascription", suspended, ascribed),
        ("a static application", large, applied),
        ("a static lambda", operator, abstraction),
    ];
    let mut declarations = Vec::from([
        declaration(At(0), choice, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), operator, Maybe::Absent(body::Absent::Hole)),
        declaration(At(2), held_unit, Maybe::Absent(body::Absent::Hole)),
    ]);
    for &(_, declared, body) in &cases {
        declarations.push(declaration(
            At(declarations.len()),
            declared,
            Maybe::Present(body),
        ));
    }
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    for (entry, &(former, _, body)) in session.entries().iter().skip(3).zip(&cases) {
        let Outcome::Checked(output) = *entry.outcome()
        else {
            panic!(
                "{former} holding a small code checks: {:?}",
                entry.outcome()
            );
        };
        assert_ne!(
            output.body(),
            body,
            "{former} carries the code's lift into its output"
        );
    }
    assert_readmitted(&mut session);
}

#[test]
fn a_refused_declaration_leaves_no_transport_behind()
{
    // The transports a judgement records are its own: a declaration refused
    // after lifting a shared code leaves the next one's use of it unchanged.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let large = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::constant(gandr_kernel_strata::LevelConstant::from(1_u64)),
    );
    let pair = arena.value_type_product(&[large, integer]);
    let code = arena.value_quote(unit);
    let wrong = arena.value_unit();
    let refused = arena.value_tuple(&[code, wrong]);
    let declarations = [
        declaration(At(0), pair, Maybe::Present(refused)),
        declaration(At(1), small, Maybe::Present(code)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert!(
        matches!(*session.entries()[0].outcome(), Outcome::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == wrong),
        "the pair is refused at its second component, after its code was lifted"
    );
    assert_eq!(
        checked(&session.entries()[1]).body(),
        code,
        "the code at its own universe is emitted as written"
    );
    assert_readmitted(&mut session);
}

#[test]
fn an_off_collector_never_defers()
{
    // A judgement that does not collect decides every comparison rigidly,
    // whatever holes are owed: deferring there would accept a mismatch.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    let mut deferrals = super::Deferrals::default();
    deferrals.owed.insert(ConstantIndex::from(0_usize));
    let (flex, rigid) = (
        TypeNode::Value(fixture.decoded),
        TypeNode::Value(fixture.integer),
    );
    deferrals.open(super::Collecting::Off);
    assert_eq!(deferrals.defer(&arena, flex, rigid), super::Deferred::No);
    assert!(deferrals.take().equations.is_empty());
    deferrals.open(super::Collecting::On);
    assert_eq!(deferrals.defer(&arena, flex, rigid), super::Deferred::Yes);
}

#[test]
fn computation_code_decodes_suspend_as_value_ones_do()
{
    // Exegesis 6.6 in the computation family: a returner against the decode of
    // an owed computation code waits on it; two such decodes are flex-flex
    // and refused.
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Computation),
        Level::zero(),
    );
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let held_integer = arena.value_type_thunk(returns_integer);
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.comp_type_element(code, Level::zero());
    let held_decoded = arena.value_type_thunk(decoded);
    let other = arena.value_constant(ConstantIndex::from(2_usize));
    let other_decoded = arena.comp_type_element(other, Level::zero());
    let held_other = arena.value_type_thunk(other_decoded);
    let integer_hole = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(integer_hole);
    let waiting = arena.value_thunk(forced);
    let decoded_hole = arena.value_constant(ConstantIndex::from(3_usize));
    let forced = arena.computation_force(decoded_hole);
    let across = arena.value_thunk(forced);
    let declarations = [
        declaration(At(0), universe, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), held_integer, Maybe::Absent(body::Absent::Hole)),
        declaration(At(2), universe, Maybe::Absent(body::Absent::Hole)),
        declaration(At(3), held_decoded, Maybe::Absent(body::Absent::Hole)),
        declaration(At(4), held_decoded, Maybe::Present(waiting)),
        declaration(At(5), held_other, Maybe::Present(across)),
    ];
    let session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    let Outcome::Suspended(ref suspension) = *session.entries()[4].outcome()
    else {
        panic!(
            "a returner against an owed computation decode waits: {:?}",
            session.entries()[4].outcome()
        );
    };
    assert_eq!(
        suspension.blockers(),
        &BTreeSet::from([ConstantIndex::from(0_usize)])
    );
    assert!(
        matches!(
            session.entries()[5].outcome(),
            Outcome::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "flex-flex between computation decodes is outside the fragment: {:?}",
        session.entries()[5].outcome()
    );
}

#[test]
fn unchanged_paths_keep_their_ids_beside_a_lift()
{
    // Output identity: one lifted code makes the walk visit its whole
    // declaration, and every path that holds no lift is emitted as the same
    // node, never a fresh copy of it.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let unit_value = arena.value_unit();
    let small = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let large = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::constant(gandr_kernel_strata::LevelConstant::from(1_u64)),
    );
    let choice = arena.value_type_sum(&[unit, unit]);
    let operator = arena.value_type_static_pi(large, large);
    let returns_unit = arena.comp_type_returner(unit);
    let held_unit = arena.value_type_thunk(returns_unit);
    let code = arena.value_quote(unit);
    let returned = arena.computation_return(unit_value);
    let held = arena.value_constant(ConstantIndex::from(2_usize));
    let forced = arena.computation_force(held);
    let bind = arena.computation_bind(forced, returned);
    let bind = arena.value_thunk(bind);
    let scrutinee = arena.value_constant(ConstantIndex::from(0_usize));
    let case = arena.computation_case(scrutinee, &[returned, returned]);
    let case = arena.value_thunk(case);
    let head = arena.value_constant(ConstantIndex::from(1_usize));
    let large_code = arena.value_quote(small);
    let applied = arena.value_static_application(head, large_code);
    let components = [code, bind, case, applied];
    let declared = arena.value_type_product(&[large, held_unit, held_unit, large]);
    let tuple = arena.value_tuple(&components);
    let declarations = [
        declaration(At(0), choice, Maybe::Absent(body::Absent::Hole)),
        declaration(At(1), operator, Maybe::Absent(body::Absent::Hole)),
        declaration(At(2), held_unit, Maybe::Absent(body::Absent::Hole)),
        declaration(At(3), declared, Maybe::Present(tuple)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    let output = checked(&session.entries()[3]).body();
    let Some(&Value::Tuple(ref emitted)) = session.arena().value(output)
    else {
        panic!("tuple output");
    };
    assert_ne!(emitted[0], code, "the small code is lifted");
    assert_eq!(
        emitted[1 ..],
        components[1 ..],
        "a bind over a force, a case and a static application with no lift \
         beneath them keep their ids"
    );
    assert_readmitted(&mut session);
}

/// A fill whose body rides along a flow above level zero forms its motive at
/// the carrier's level where the batch run never judged it, and the session
/// readmits the fill at that motive: the family reaches the report the bridge
/// reads only through the fill's judgement, #1837.
#[test]
fn a_filled_ride_above_level_zero_readmits_at_its_recorded_motive_1837()
{
    // def kept : Flow(Type[+, 1], Type, Type) = stay(Type) ;
    // def rode : () => Type = ? ; filled as thunk { ride(\X. X, kept, Integer) }
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        Level::zero(),
    );
    let one = Level::zero().succ().expect("one is below the top");
    let large = arena.value_type_universe(
        Sort::Ground(gandr_kernel_term::GroundSort::Value),
        one.clone(),
    );
    let code = arena.value_quote(small);
    let stay = arena.value_stay(code);
    let flow = arena.value_type_flow(large, code, code);
    let binder = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(binder, Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    let quoted = arena.value_quote(integer);
    let kept = arena.value_constant(ConstantIndex::from(0_usize));
    let ride = arena.computation_ride(motive, kept, quoted);
    let rode = arena.value_thunk(ride);
    let returns_type = arena.comp_type_returner(small);
    let suspended_type = arena.value_type_thunk(returns_type);
    let declarations = [
        declaration(At(0), flow, Maybe::Present(stay)),
        declaration(At(1), suspended_type, Maybe::Absent(body::Absent::Hole)),
    ];
    let mut session = Session::new(&mut arena, &declarations, CheckBudget::DEFAULT);
    assert!(
        session.report().motives().is_empty(),
        "the batch run forms no motive: the ride is only written by the fill"
    );
    session
        .fill(ConstantIndex::from(1_usize), rode)
        .expect("the ride along the level-one flow checks");
    let family = session.report().motives().get(&ride).copied();
    assert!(
        family.is_some_and(|family| matches!(
            session.arena().value_type(family),
            Some(&ValueType::Element { code: read, ref target }) if read == binder && *target == one
        )),
        "the fill's judgement reports the motive at the carrier's level: {family:?}"
    );
    assert_readmitted(&mut session);
}

/// A collector open for a value declaration, with the first nominated hole
/// declared at no binder: the hole, its node and its decode.
///
/// # Specification
/// trivial.
fn nominated(
    arena: &mut CoreArena,
    deferrals: &mut super::Deferrals,
) -> (gandr_core_term::hole::HoleId, ValueId, ValueTypeId)
{
    let hole = gandr_core_term::hole::HoleId::nominated(
        gandr_core_term::hole::NominationIndex::from(0_u32),
    )
    .expect("the first nominated name");
    let at = arena.value_hole(hole);
    deferrals.open(super::Collecting::On);
    deferrals.nominate(at, hole, Binders::NONE);
    (hole, at, arena.value_type_element(at, Level::zero()))
}

#[test]
fn an_omitted_implicit_is_solved_from_the_argument_1216()
{
    // `same(3)`: the decode of `a` against the type the argument synthesises
    // binds `a` to that type's code. A pair neither side of which is a
    // metavariable's decode is conversion's, and nothing is bound by it.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (hole, _, decoded) = nominated(&mut arena, &mut deferrals);
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let rigid = (TypeNode::Value(integer), TypeNode::Value(unit));
    assert_eq!(
        deferrals.unify(&mut arena, Binders::NONE, rigid.0, rigid.1),
        super::Unified::Rigid
    );
    assert_eq!(
        deferrals.unify(
            &mut arena,
            Binders::NONE,
            TypeNode::Value(decoded),
            TypeNode::Value(integer)
        ),
        super::Unified::Agreed
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved.len() == 1
            && solved.get(&hole).is_some_and(|&(code, scope)| {
                scope == Binders::NONE
                    && matches!(arena.value(code), Some(&Value::Quote(quoted)) if quoted == integer)
            })),
        "`a` is solved as the integers' code, at the binders it was declared under: {solutions:?}"
    );
}

#[test]
fn two_arguments_disagreeing_on_an_implicit_are_apart_1216()
{
    // `both(3, unit)`: the first argument binds `a` to the integers, and the
    // second's type is refuted against the same decode.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (_, _, decoded) = nominated(&mut arena, &mut deferrals);
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let [first, second] = [integer, unit].map(|argument| {
        deferrals.unify(
            &mut arena,
            Binders::NONE,
            TypeNode::Value(decoded),
            TypeNode::Value(argument),
        )
    });
    assert_eq!(first, super::Unified::Agreed);
    assert_eq!(second, super::Unified::Refuted);
}

#[test]
fn an_open_end_is_solved_from_its_point_1979()
{
    // `(here(0) : Path(Integer, 0, _))`: two rigid values are conversion's;
    // the open end against the point that reaches it is bound to the point;
    // a second, different point is then refuted against the same end.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (hole, open, _) = nominated(&mut arena, &mut deferrals);
    let zero = arena.value_literal(integer_literal());
    let one = gandr_kernel_term::Magnitude::from_decimal_text("1".into())
        .expect("the digits are decimal");
    let one = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(gandr_kernel_term::Sign::NonNegative, one),
    ));
    let outcomes = [(zero, one), (zero, open), (one, open)]
        .map(|(point, end)| deferrals.unify_values(&mut arena, Binders::NONE, point, end));
    assert_eq!(
        outcomes,
        [
            super::Unified::Rigid,
            super::Unified::Agreed,
            super::Unified::Refuted
        ],
        "rigid values are left to conversion, the open end is solved, and a second point is apart"
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved.len() == 1
            && solved.get(&hole).is_some_and(|&(end, scope)| {
                scope == Binders::NONE
                    && gandr_core_term::equal_certificate_syntax(&arena, end, zero)
                        == gandr_core_term::CertificateEquality::Equal
            })),
        "the end is solved as the point, at the binders it was declared under: {solutions:?}"
    );
}

#[test]
fn an_implicit_no_argument_forces_is_unsolved_1216()
{
    // `twice(3)`'s combination: met and declared, compared with nothing.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (_, at, _) = nominated(&mut arena, &mut deferrals);
    assert_eq!(deferrals.solutions(&arena), Err((at, Unsolved::Unforced)));
}

#[test]
fn an_implicit_solved_past_its_scope_escapes_1216()
{
    // `konst(fn (t) { fn (y) { return y } })`: under the lambda's binder the
    // decode of `b`, declared outside it, meets the decode of `t`. The only
    // solution names `t`, so the equation waits on its escape, and the
    // refusal says so.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (_, at, decoded) = nominated(&mut arena, &mut deferrals);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded_bound = arena.value_type_element(bound, Level::zero());
    assert_eq!(
        deferrals.unify(
            &mut arena,
            Binders::ONE,
            TypeNode::Value(decoded),
            TypeNode::Value(decoded_bound)
        ),
        super::Unified::Agreed
    );
    assert_eq!(deferrals.solutions(&arena), Err((at, Unsolved::Escape)));
}

#[test]
fn a_row_open_through_an_implicit_is_solved_by_the_row_equation_2270()
{
    // `log("a")` where `[Console, Div]` is asked: `log`'s row `[Console | r]`,
    // `r` omitted, against the closed row binds `r` to `[Div]`. Two closed
    // rows are conversion's; against `[Div]`, which lacks `Console`, the open
    // row is apart.
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;

    let row = |names: &[&str]| {
        names.iter().fold(EffectRow::EMPTY, |row, &name| {
            let signature = EffectSig::new(EffectName::from(name), Vec::<EffectOp>::new())
                .expect("an interface without operations has no duplicate");
            row.union(&EffectRow::singleton(signature), &CoreArena::new())
                .expect("each interface once")
        })
    };
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (hole, at, _) = nominated(&mut arena, &mut deferrals);
    let tail = arena.value_type_row_tail(at);
    let open = row(&["Console"]).with_tail(Some(tail));
    let (asked, lacking) = (row(&["Console", "Div"]), row(&["Div"]));
    assert_eq!(
        deferrals.unify_rows(&mut arena, Binders::NONE, (&asked, &lacking)),
        super::Unified::Rigid,
        "two closed rows are conversion's"
    );
    assert_eq!(
        deferrals.unify_rows(&mut arena, Binders::NONE, (&open, &asked)),
        super::Unified::Agreed,
        "the open row meets the asked one"
    );
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions
            .as_ref()
            .is_ok_and(|solved| solved.get(&hole).is_some_and(|&(code, _)| {
                matches!(arena.value(code), Some(Value::Row(solved))
                if solved.tail().is_none()
                    && solved.signatures().map(|signature| signature.name().as_ref()).eq(["Div"]))
            })),
        "`r` is solved as `[Div]`, closed: {solutions:?}"
    );
    assert_eq!(
        deferrals.unify_rows(&mut arena, Binders::NONE, (&open, &lacking)),
        super::Unified::Refuted,
        "a row lacking `Console` is apart from `log`'s"
    );
}

/// A collector open for a value declaration over a counter's model slot: its
/// sort's hole and its step's, both declared at no binder, the sort's forced
/// to the integers as `stepped(4)`'s argument forces it. The holes, the sort
/// hole's node, and the codes of the integers and of the unit type.
///
/// # Specification
/// trivial.
fn forced_slot(
    arena: &mut CoreArena,
    deferrals: &mut super::Deferrals,
) -> ([gandr_core_term::hole::HoleId; 2], ValueId, [ValueId; 2])
{
    let [sort, step] = [0_u32, 1].map(|index| {
        gandr_core_term::hole::HoleId::nominated(gandr_core_term::hole::NominationIndex::from(
            index,
        ))
        .expect("a nominated name")
    });
    let [sort_at, step_at] = [sort, step].map(|hole| arena.value_hole(hole));
    deferrals.open(super::Collecting::On);
    deferrals.nominate(sort_at, sort, Binders::NONE);
    deferrals.nominate(step_at, step, Binders::NONE);
    let decoded = arena.value_type_element(sort_at, Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    assert_eq!(
        deferrals.unify(
            arena,
            Binders::NONE,
            TypeNode::Value(decoded),
            TypeNode::Value(integer)
        ),
        super::Unified::Agreed,
        "the argument forces the sort"
    );
    let unit = arena.value_type_unit();
    let codes = [integer, unit].map(|ty| arena.value_quote(ty));
    ([sort, step], sort_at, codes)
}

/// The candidate passing the sort `code` and the step named by the constant
/// at `step`.
///
/// # Specification
/// trivial.
fn candidate(
    arena: &mut CoreArena,
    code: ValueId,
    step: ConstantIndex,
) -> gandr_core_term::model::Candidate
{
    gandr_core_term::model::Candidate {
        components: Vec::from([code, arena.value_constant(step)]),
        fixed: Vec::new(),
    }
}

#[test]
fn a_model_slot_resolves_to_the_candidate_its_sort_admits_739()
{
    // `stepped(4)` with `Up` over the integers and `Flag` over the unit type
    // in scope: the argument forces the sort, so only `Up` is left, and the
    // step is solved as `Up`'s.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, _, [integer, unit]) = forced_slot(&mut arena, &mut deferrals);
    let up = candidate(&mut arena, integer, ConstantIndex::from(1_usize));
    let flag = candidate(&mut arena, unit, ConstantIndex::from(2_usize));
    let up_step = up.components[1];
    let slot = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates: Vec::from([flag, up]),
    };
    assert_eq!(deferrals.resolve(&mut arena, &[slot]), Ok(()));
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved
            .get(&holes[1])
            .is_some_and(|&(step, _)| step == up_step)),
        "the step is `Up`'s: {solutions:?}"
    );
}

#[test]
fn a_model_slot_two_candidates_answer_is_ambiguous_739()
{
    // `Up` and `Tens`, both over the integers: the argument's sort leaves
    // both, and the refusal names both by their places.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, at, [integer, unit]) = forced_slot(&mut arena, &mut deferrals);
    let candidates = Vec::from([
        candidate(&mut arena, integer, ConstantIndex::from(1_usize)),
        candidate(&mut arena, unit, ConstantIndex::from(2_usize)),
        candidate(&mut arena, integer, ConstantIndex::from(3_usize)),
    ]);
    let slot = gandr_core_term::model::ModelSlot {
        holes: Vec::from(holes),
        fixed: Vec::new(),
        candidates,
    };
    let survivors = [0_usize, 2]
        .into_iter()
        .map(gandr_core_term::model::CandidatePlace::from)
        .fold(
            gandr_core_term::model::Survivors::default(),
            gandr_core_term::model::Survivors::with,
        );
    assert_eq!(
        deferrals.resolve(&mut arena, &[slot]),
        Err((at, CheckRefusal::ModelAmbiguous { at, survivors }))
    );
}

#[test]
fn a_model_slot_no_candidate_answers_is_refused_739()
{
    // Only `Flag`, over the unit type, where the argument forces the
    // integers; and a scope holding no model at all.
    let mut arena = CoreArena::new();
    let mut deferrals = super::Deferrals::default();
    let (holes, at, [_, unit]) = forced_slot(&mut arena, &mut deferrals);
    let flag = candidate(&mut arena, unit, ConstantIndex::from(2_usize));
    let [refuted, empty] = [Vec::from([flag]), Vec::new()].map(|candidates| {
        deferrals.resolve(&mut arena, &[gandr_core_term::model::ModelSlot {
            holes: Vec::from(holes),
            fixed: Vec::new(),
            candidates,
        }])
    });
    assert_eq!(refuted, Err((at, CheckRefusal::ModelUnanswered { at })));
    assert_eq!(empty, Err((at, CheckRefusal::ModelUnanswered { at })));
}

#[test]
fn a_manifest_model_slot_resolves_to_the_candidate_of_its_fixed_sort_2317()
{
    // `fromZero()` over `@[s : Model(Tally) with sort C = Integer]`: the slot
    // binds the step alone, nothing forces it, and the sort is fixed, so only
    // the fixed sort tells `Up`, over the integers, from `Flips`, over the
    // unit type. A fixed type reading a binder of the callee tests nothing.
    let mut arena = CoreArena::new();
    let step = gandr_core_term::hole::HoleId::nominated(
        gandr_core_term::hole::NominationIndex::from(0_u32),
    )
    .expect("a nominated name");
    let at = arena.value_hole(step);
    let collecting = || {
        let mut deferrals = super::Deferrals::default();
        deferrals.open(super::Collecting::On);
        deferrals.nominate(at, step, Binders::NONE);
        deferrals
    };
    let mut deferrals = collecting();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let [integer, unit] = [integer, unit].map(|ty| arena.value_quote(ty));
    let [up_step, flips_step] =
        [1_usize, 2].map(|constant| arena.value_constant(ConstantIndex::from(constant)));
    let candidates = Vec::from([
        gandr_core_term::model::Candidate {
            components: Vec::from([flips_step]),
            fixed: Vec::from([unit]),
        },
        gandr_core_term::model::Candidate {
            components: Vec::from([up_step]),
            fixed: Vec::from([integer]),
        },
    ]);
    let slot = |fixed| gandr_core_term::model::ModelSlot {
        holes: Vec::from([step]),
        fixed: Vec::from([fixed]),
        candidates: candidates.clone(),
    };
    let mut open = collecting();
    assert_eq!(deferrals.resolve(&mut arena, &[slot(integer)]), Ok(()));
    let solutions = deferrals.solutions(&arena);
    assert!(
        solutions.as_ref().is_ok_and(|solved| solved
            .get(&step)
            .is_some_and(|&(solved, _)| solved == up_step)),
        "the step is `Up`'s: {solutions:?}"
    );
    let bound = arena.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
    let survivors = [0_usize, 1]
        .into_iter()
        .map(gandr_core_term::model::CandidatePlace::from)
        .fold(
            gandr_core_term::model::Survivors::default(),
            gandr_core_term::model::Survivors::with,
        );
    assert_eq!(
        open.resolve(&mut arena, &[slot(bound)]),
        Err((at, CheckRefusal::ModelAmbiguous { at, survivors })),
        "a fixed type reading the callee's binder refutes neither"
    );
}
