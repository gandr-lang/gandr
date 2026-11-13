//! The routes of [`dispatch`] whose walk or script the run stage's engine
//! drives: a check, a test and a run each reach the path given (#7048).

use core::ops::ControlFlow;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_diagnostics::Lint;
use gandr_surface_dispatcher::Captured;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::ScriptRun;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::dispatch;
use gandr_surface_evaluate::Evaluator;

/// The first fault a walk over `paths` reports, which names the first path
/// it visited when no path exists.
///
/// # Specification
/// - requires: a run outcome whose first step is a fault.
/// - ensures: the path carried by that first fault.
/// - fails: never on the admitted domain.
/// - panics: a non-run outcome or non-fault first step violates the
///   precondition.
///
/// # Adequacy
/// - hypothesis: L3 — missing paths distinguish the first routed path under
///   both check policies and test. Other outcomes and successful first steps
///   are outside this helper's admitted domain.
/// - witness: `tests::dispatch::check_routes_to_a_walk_under_the_check_verb`
/// - witness: `tests::dispatch::the_test_verb_routes_to_a_walk`
#[spec(requires: matches!(outcome, Outcome::Run { .. }))]
fn first_fault_path(outcome: Outcome) -> PathBuf
{
    let Outcome::Run { walk, .. } = outcome
    else {
        panic!("a verb routes to a walk");
    };
    let ControlFlow::Break(path) =
        walk.visit::<Evaluator, _, _>(&Pool::new(Width::SERIAL), |step| match step {
            Step::Fault { path, .. } => ControlFlow::Break(path.to_path_buf()),
            Step::Source { .. } => panic!("an absent path faults"),
        })
    else {
        panic!("an absent path faults");
    };
    path
}

/// `check` keeps its goals and lints settings, its width and its paths'
/// order.
#[test]
fn check_routes_to_a_walk_under_the_check_verb()
{
    let three = Width::Threads(Threads::from(
        core::num::NonZeroUsize::MIN.saturating_add(2),
    ));
    for (goals, lints, width) in [
        (Goals::Gated, Lints::default(), Width::SERIAL),
        (
            Goals::Reported,
            Lints::enabling([Lint::ExplicitExits]),
            three,
        ),
    ] {
        let paths = vec![
            PathBuf::from("no/such/first.gandr"),
            PathBuf::from("no/such/second.gandr"),
        ];
        let outcome = dispatch(Invocation::Check {
            goals,
            lints,
            grant: HostGrant::UNBOUNDED,
            paths,
            width,
        });
        assert!(
            matches!(outcome, Outcome::Run { verb: Verb::Check(routed), lints: routed_lints, width: routed_width, .. }
                if routed == goals && routed_lints == lints && routed_width == width),
            "check routes under its own goals and lints settings and width"
        );
        assert_eq!(
            first_fault_path(outcome),
            PathBuf::from("no/such/first.gandr"),
            "the walk starts at the first path given"
        );
    }
}

/// `test` routes to a walk under the test verb, at its width.
#[test]
fn the_test_verb_routes_to_a_walk()
{
    let outcome = dispatch(Invocation::Test {
        paths: vec![PathBuf::from("no/such/only.gandr")],
        width: Width::PerformanceCores,
    });
    assert!(
        matches!(outcome, Outcome::Run {
            verb: Verb::Test,
            width: Width::PerformanceCores,
            ..
        }),
        "test routes under the test verb at its width"
    );
    assert_eq!(
        first_fault_path(outcome),
        PathBuf::from("no/such/only.gandr"),
        "the walk visits the path given"
    );
}

/// `run` routes to a script of its one path.
#[test]
fn the_run_verb_routes_to_a_script()
{
    let outcome = dispatch(Invocation::Run {
        path: PathBuf::from("no/such/script.gandr"),
        arguments: Vec::new(),
    });
    let Outcome::Script(mut script) = outcome
    else {
        panic!("run routes to a script");
    };
    let ScriptRun::Fault { path, .. } = script.run::<Evaluator>(&mut Captured::default())
    else {
        panic!("an absent script faults");
    };
    assert_eq!(
        path,
        PathBuf::from("no/such/script.gandr"),
        "the script reads the path given"
    );
}
