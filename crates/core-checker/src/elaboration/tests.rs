//! Executable route laws, separately from the kernel's typing oracle.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

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

/// Extract checked output, refusing any weakening to a non-error assertion.
///
/// # Specification
/// trivial.
fn checked(entry: &super::Entry) -> Output
{
    match *entry.outcome() {
        | Outcome::Checked(output) => output,
        | ref other => panic!("expected Checked, got {other:?}"),
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

/// Check every published answer with the independent kernel.
///
/// # Specification
/// trivial.
fn assert_readmitted(session: &mut Session<'_>)
{
    let readmission = session.readmit();
    let mut readmitted = readmission.readmitted().iter();
    for entry in session.entries() {
        if matches!(entry.outcome(), Outcome::Suspended(_)) {
            continue;
        }
        let replay = readmitted
            .next()
            .expect("one readmission per settled entry");
        assert_eq!(replay.constant(), entry.constant());
        match (entry.outcome(), replay.outcome()) {
            | (&Outcome::Checked(_), &bridge::Outcome::Defined { .. })
            | (&Outcome::Owed(_), &bridge::Outcome::Assumed { .. }) => {},
            | (&Outcome::Refused(expected), &bridge::Outcome::Marked(actual)) => {
                assert_eq!(expected, actual);
            },
            | (outcome, replay) => panic!("{outcome:?} readmitted as {replay:?}"),
        }
    }
    assert_eq!(readmitted.next(), None);
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
        match fixture.declarations[0].signature() {
            | Maybe::Present(id) => id,
            | Maybe::Absent(_) => panic!("universe"),
        },
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
    // Exegesis 6.6: absence of an identity solution is suspension, not failure.
    let mut arena = CoreArena::new();
    let fixture = route(&mut arena);
    {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let report = check_module(&mut context, &fixture.declarations);
        assert!(matches!(
            report.judged()[1].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ));
    }
    let mut session = Session::new(&mut arena, &fixture.declarations, CheckBudget::DEFAULT);
    let Outcome::Suspended(ref suspension) = *session.entries()[1].outcome()
    else {
        panic!("owed decode must suspend");
    };
    assert_eq!(suspension.source(), fixture.declarations[1]);
    assert_eq!(
        suspension.blockers(),
        &BTreeSet::from([ConstantIndex::from(0_usize)])
    );
    let &[equation] = suspension.equations()
    else {
        panic!("exactly one residual");
    };
    assert_eq!(equation.hole(), ConstantIndex::from(0_usize));
    assert_eq!(equation.flex(), TypeNode::Value(fixture.decoded));
    assert_eq!(
        session.arena().value_type(match equation.rigid() {
            | TypeNode::Value(id) => id,
            | TypeNode::Computation(_) => panic!("value comparison"),
        }),
        Some(&ValueType::Base(BaseType::Integer))
    );
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
    declarations[0] = Declaration::new(
        declarations[0].constant(),
        declarations[0].signature(),
        Maybe::Present(fixture.filling),
        declarations[0].origin(),
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
    let universe = match fixture.declarations[0].signature() {
        | Maybe::Present(id) => id,
        | Maybe::Absent(_) => panic!("universe"),
    };
    let other_hole = arena.value_constant(ConstantIndex::from(1_usize));
    let other_decoded = arena.value_type_element(other_hole, Level::zero());
    let value_hole = arena.value_constant(ConstantIndex::from(2_usize));
    let declarations = [
        fixture.declarations[0],
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
    let pair_type = arena.value_type_product(fixture.decoded, fixture.integer);
    let wrong = arena.value_unit();
    let pair = arena.value_pair(fixture.literal, wrong);
    let pair_both_type = arena.value_type_product(fixture.decoded, fixture.decoded);
    let good_pair = arena.value_pair(fixture.literal, fixture.literal);
    let declarations = [
        fixture.declarations[0],
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
        fixture.declarations[0],
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
        fixture.declarations[0],
        fixture.declarations[1],
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
