//! The accumulate stencil on each tier: a free variable's accumulator grows
//! with each force and application, holding an owner of what it grew from,
//! and sticks on any other observation.

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_value;
use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_term::Component;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_open_on;

use crate::support::BUDGET;

/// How many producer binders out a variable reaches: zero names the
/// innermost.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Outward(u32);

/// The intuitionistic producer variable `outward` binders out.
///
/// # Specification
/// trivial.
fn variable(
    core: &mut CoreArena,
    outward: Outward,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, outward.0.into())
}

/// One tier's open run: the tier, the store its outcome moved into, and the
/// outcome.
type Run = (Tier, Store, Result<Outcome, Declined>);

/// `program`, focused into an arena of its own, run open on each tier this
/// host runs, each run's store beside its outcome.
///
/// # Specification
/// trivial.
fn runs(
    core: &CoreArena,
    program: ComputationId,
) -> (CommandArena, Vec<Run>)
{
    let mut arena = CommandArena::new();
    let root: CommandId = focus_computation(
        core,
        program,
        &mut arena,
        &mut Provenance::new(),
        &gandr_core_sequent::Writers::NONE,
    )
    .expect("the program focuses");
    let tiers: &[Tier] = if PATCHER {
        &[Tier::Native, Tier::Executor]
    }
    else {
        &[Tier::Executor]
    };
    let definitions = Definitions::new();
    let outcomes = tiers
        .iter()
        .map(|&tier| {
            let mut store = Store::new();
            let outcome = evaluate_open_on(
                tier,
                (&arena, &definitions),
                root,
                (Fuel::from(BUDGET), RunInputs::new(&mut store)),
            );
            (tier, store, outcome)
        })
        .collect();
    (arena, outcomes)
}

/// An accumulator two holders share keeps both: over `f` and `z`,
/// `x ← (force f) z; y ← (force f) x; return (x, y)` answers
/// `(return ((force f) z), return ((force f) (return ((force f) z))))` on
/// each tier. `y`'s accumulator holds `x` beside the pair, so an owner it
/// did not count frees `x` while the pair still reads it.
#[test]
fn an_accumulator_holds_what_it_grew_from_3557()
{
    let mut core = CoreArena::new();
    let f = variable(&mut core, Outward(1));
    let z = variable(&mut core, Outward(0));
    let forced = core.computation_force(f);
    let first = core.computation_application(forced, z);
    let f_under_x = variable(&mut core, Outward(2));
    let x = variable(&mut core, Outward(0));
    let forced_under_x = core.computation_force(f_under_x);
    let second = core.computation_application(forced_under_x, x);
    let x_under_y = variable(&mut core, Outward(1));
    let y = variable(&mut core, Outward(0));
    let pair = core.value_tuple(&[x_under_y, y]);
    let answered = core.computation_return(pair);
    let rest = core.computation_bind(second, answered);
    let program = core.computation_bind(first, rest);
    let once = core.value_returned(first);
    let twice = core.computation_application(forced, once);
    let twice = core.value_returned(twice);
    let expected = core.value_tuple(&[once, twice]);
    let (arena, outcomes) = runs(&core, program);
    for (tier, store, outcome) in outcomes {
        let Ok(Outcome::Halted(value)) = outcome
        else {
            panic!("the run halts on {tier:?}: {outcome:?}");
        };
        let actual =
            read_back_value(&arena, &store, value, &mut core).expect("the answer reads back");
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&core, actual, expected),
            "on {tier:?}"
        );
    }
}

/// A projection of a free variable sticks naming the projection, the
/// accumulator in hand: `project 0 (force f)`.
#[test]
fn a_projection_of_a_free_variable_sticks_3557()
{
    let mut core = CoreArena::new();
    let f = variable(&mut core, Outward(0));
    let forced = core.computation_force(f);
    let program = core.computation_project(Component::from(0_usize), forced);
    let (_arena, outcomes) = runs(&core, program);
    for (tier, _store, outcome) in outcomes {
        assert!(
            matches!(
                outcome,
                Ok(Outcome::Stuck(Stuck::Unobservable { head, .. }))
                    if head == DestructorTag::Project(Component::from(0_usize))
            ),
            "on {tier:?}: {outcome:?}"
        );
    }
}
