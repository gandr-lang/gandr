//! Live answers and coverage over retained semantic scrutinees.

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Exhaustiveness;
use gandr_core_checker::Redundancy;
use gandr_core_checker::form_value_type;
use gandr_core_nbe::ArmIndex;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::Selection;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::BranchStatus;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_term::Side;
use gandr_surface_session::MatchCheckpoint;

/// Evaluate a closed fixture without global definitions.
///
/// # Specification
/// - requires: `value` is closed in `core`.
/// - ensures: the retained checkpoint holds its semantic result.
/// - panics: if the fixture cannot evaluate.
///
/// # Adequacy
/// - hypothesis: the callers distinguish constructor heads from holed payloads.
/// - witness: `tests::live_match::a_constructor_scrutinee_refutes_the_head_and_suspends_the_payload`
pub fn checkpoint(
    core: &CoreArena,
    value: ValueId,
) -> MatchCheckpoint
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    MatchCheckpoint::evaluate(core, definitions, Fuel::from(10_000_u32), value)
        .expect("a closed fixture evaluates")
        .0
}

#[test]
fn a_hole_scrutinee_leaves_every_branch_possible()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = core.value_hole(HoleId::from(0_u32));
    let checkpoint = checkpoint(&core, hole);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).expect("sum forms");
    let analysis = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, right])
        .unwrap();
    assert_eq!(analysis.branches(), &[
        BranchStatus::Possibly,
        BranchStatus::Possibly
    ]);
    assert_eq!(analysis.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(0_usize)
    });
    assert_eq!(
        analysis.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Exhaustive
    );
}

#[test]
fn a_constructor_scrutinee_refutes_the_head_and_suspends_the_payload()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = core.value_hole(HoleId::from(0_u32));
    let value = core.value_injection(Side::Left, hole);
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let unit_pattern = patterns.mint(Pattern::Unit);
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    let left_unit = patterns.mint(Pattern::Injection(Side::Left, unit_pattern));
    let left_any = patterns.mint(Pattern::Injection(Side::Left, any));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, sum, &patterns, &[right, left_unit, left_any])
        .unwrap();
    assert_eq!(analysis.branches(), &[
        BranchStatus::Refuted,
        BranchStatus::Possibly,
        BranchStatus::Satisfied
    ]);
    assert_eq!(analysis.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(1_usize)
    });
}

#[test]
fn a_pattern_hole_downgrades_the_residue()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let value = core.value_unit();
    let value = core.value_injection(Side::Left, value);
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let hole = patterns.mint(Pattern::Hole(HoleId::from(1_u32)));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let before = checkpoint
        .analyze(&mut context, sum, &patterns, &[left])
        .unwrap();
    let after = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, hole])
        .unwrap();
    assert_eq!(
        before.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Inexhaustive
    );
    assert_eq!(
        after.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Possibly
    );
    assert_eq!(after.branches(), &[
        BranchStatus::Satisfied,
        BranchStatus::Possibly
    ]);
}

#[test]
fn completing_the_match_clears_the_obligation()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let value = core.value_hole(HoleId::from(0_u32));
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let before = checkpoint
        .analyze(&mut context, sum, &patterns, &[left])
        .unwrap();
    let after = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, right])
        .unwrap();
    assert_eq!(
        before.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Inexhaustive
    );
    assert_eq!(
        after.coverage().as_ref().unwrap().exhaustiveness(),
        Exhaustiveness::Exhaustive
    );
}

#[test]
fn a_hole_in_the_prefix_leaves_redundancy_unproved()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let value = core.value_unit();
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let hole = patterns.mint(Pattern::Hole(HoleId::from(0_u32)));
    let any = patterns.mint(Pattern::Wildcard);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let unit = form_value_type(&mut context, unit).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, unit, &patterns, &[hole, any])
        .unwrap();
    assert_eq!(analysis.coverage().as_ref().unwrap().arms(), &[
        Redundancy::Possibly,
        Redundancy::Possibly
    ]);
    assert_eq!(analysis.branches(), &[
        BranchStatus::Possibly,
        BranchStatus::Satisfied
    ]);
    assert_eq!(analysis.selection(), &Selection::Indeterminate {
        arm: ArmIndex::from(0_usize)
    });
}

#[test]
fn a_live_branch_raises_no_redundancy_obligation()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let value = core.value_unit();
    let checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let unit = form_value_type(&mut context, unit).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, unit, &patterns, &[any])
        .unwrap();
    assert_eq!(analysis.coverage().as_ref().unwrap().arms(), &[
        Redundancy::Irredundant
    ]);
    assert_eq!(analysis.selection(), &Selection::Taken {
        arm: ArmIndex::from(0_usize),
        bindings: Vec::new()
    });
}

#[test]
fn filling_a_hole_refines_a_possible_verdict()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = HoleId::from(0_u32);
    let value = core.value_hole(hole);
    let mut checkpoint = checkpoint(&core, value);
    let mut patterns = Patterns::new();
    let any = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, any));
    let right = patterns.mint(Pattern::Injection(Side::Right, any));
    {
        let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
        let sum = form_value_type(&mut context, sum).unwrap();
        assert_eq!(
            checkpoint
                .analyze(&mut context, sum, &patterns, &[left, right])
                .unwrap()
                .branches(),
            &[BranchStatus::Possibly, BranchStatus::Possibly]
        );
    }
    let body = core.value_unit();
    let filled = core.value_injection(Side::Right, body);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    checkpoint
        .fill(
            &mut core,
            definitions,
            Fuel::from(10_000_u32),
            hole,
            TermId::Value(filled),
        )
        .unwrap();
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let sum = form_value_type(&mut context, sum).unwrap();
    let after = checkpoint
        .analyze(&mut context, sum, &patterns, &[left, right])
        .unwrap();
    assert_eq!(after.branches(), &[
        BranchStatus::Refuted,
        BranchStatus::Satisfied
    ]);
    assert_eq!(after.selection(), &Selection::Taken {
        arm: ArmIndex::from(1_usize),
        bindings: Vec::new()
    });
}

#[test]
fn filling_preserves_the_captured_scrutinee_environment()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let hole = HoleId::from(7_u32);
    let body = core.value_hole(hole);
    let lambda = core.value_static_lambda(body);
    let argument = core.value_unit();
    let applied = core.value_static_application(lambda, argument);
    let mut checkpoint = checkpoint(&core, applied);
    let mut patterns = Patterns::new();
    let expected = patterns.mint(Pattern::Unit);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let formed = form_value_type(&mut context, unit).unwrap();
    assert_eq!(
        checkpoint
            .analyze(&mut context, formed, &patterns, &[expected])
            .unwrap()
            .branches(),
        &[BranchStatus::Possibly]
    );
    let filling = core.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    checkpoint
        .fill(
            &mut core,
            definitions,
            Fuel::from(1000_u32),
            hole,
            TermId::Value(filling),
        )
        .unwrap();
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    assert_eq!(
        checkpoint
            .analyze(&mut context, formed, &patterns, &[expected])
            .unwrap()
            .branches(),
        &[BranchStatus::Satisfied]
    );
}

#[test]
fn the_eliminator_still_fires_on_a_hole_payload()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let sum = core.value_type_sum(unit, unit);
    let hole = core.value_hole(HoleId::from(0_u32));
    let left = core.value_injection(Side::Left, hole);
    let mut checkpoint = checkpoint(&core, left);
    let mut patterns = Patterns::new();
    let binder = patterns.mint(Pattern::Binder);
    let left = patterns.mint(Pattern::Injection(Side::Left, binder));
    let right = patterns.mint(Pattern::Injection(Side::Right, binder));
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let formed = form_value_type(&mut context, sum).unwrap();
    let analysis = checkpoint
        .analyze(&mut context, formed, &patterns, &[left, right])
        .unwrap();
    let bound = core.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let returned = core.computation_return(bound);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let (outcome, _) = checkpoint
        .run(&core, definitions, Fuel::from(1000_u32), &analysis, &[
            returned, returned,
        ])
        .unwrap();
    let gandr_surface_session::MatchRun::Evaluated { arm, result } = outcome
    else {
        panic!("the constructor head selects")
    };
    assert_eq!(arm, ArmIndex::from(0_usize));
    let Some(&gandr_core_nbe::DomainComp::Return { value, .. }) =
        checkpoint.domain().computation(result)
    else {
        panic!("returning the hole is not a stuck eliminator")
    };
    assert!(matches!(
        checkpoint.domain().value(value),
        Some(&gandr_core_nbe::DomainValue::Neutral { .. })
    ));
}
