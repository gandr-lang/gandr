//! The emitter across the tiers: each named program lowered, emitted or
//! built for the executor, run, and its answer moved into a store — native
//! code's compared with the executor's value by value, through the policy's
//! own entry too, and each with the answer the program states.

use std::io::Write as _;
use std::process::Command;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_definition;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::POLICY_VARIABLE;
use gandr_runtime_emitter::Policy;
use gandr_runtime_emitter::RunInputs;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate;
use gandr_runtime_emitter::evaluate_on;
use gandr_runtime_emitter::evaluate_unfused_on;
use gandr_runtime_emitter::lower;
use gandr_runtime_emitter::lower_unfused;
use gandr_runtime_emitter::replay;

use crate::support::BUDGET;
use crate::support::COMPARED;
use crate::support::Integer;
use crate::support::Label;
use crate::support::Program;
use crate::support::Verdict;
use crate::support::agree;
use crate::support::agree_with;
use crate::support::focus;
use crate::support::integer;
use crate::support::named;

/// The named programs — a return, a bind, a case, a constructor, their
/// composition, and answers that suspend a function or a thunk, whose sites,
/// captures and environments the transfer rebuilds — halt alike on both tiers
/// and under the policy, with the answer each states.
#[test]
fn the_named_programs_agree_on_both_executors()
{
    for named in named() {
        let name = named.program.name;
        let shows = Verdict::Halted(Some(String::from(named.shows)));
        let (commands, root) = focus(&named.program);
        let definitions = Definitions::new();
        assert_eq!(
            shows,
            agree(Label(name), &commands, &definitions, root),
            "{name} across the tiers"
        );
        let policy = agree_with(Label(name), &commands, &definitions, root, |store| {
            evaluate(
                &commands,
                &definitions,
                root,
                Fuel::from(BUDGET),
                RunInputs::new(store),
            )
        });
        assert_eq!(shows, policy, "{name} under the policy");
    }
}

/// The line the cached policy's child ends with once every named program
/// agreed under it.
const SERVED: &str = "the cached policy served every named program";

/// The named programs halt under the cached policy with the answer each
/// states, in a child process whose `GANDR_NATIVE` reads `cached`: each
/// misses the cache and runs on the executor, then, once a native run has
/// emitted it, runs the code the cache serves.
#[test]
fn the_named_programs_agree_under_the_cached_policy()
{
    let ran = Command::new(std::env::current_exe().expect("the test binary is named"))
        .args([
            "--exact",
            "agreement::the_cached_policy_child",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(POLICY_VARIABLE, "cached")
        .output()
        .expect("the child runs");
    let transcript = String::from_utf8_lossy(&ran.stdout);
    assert!(
        ran.status.success(),
        "{transcript}\n{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    assert!(
        transcript.contains(SERVED),
        "the child ran under the cached policy: {transcript}"
    );
}

/// The cached policy's process: run only when the parent test starts this
/// binary for it with `GANDR_NATIVE=cached`, ending with [`SERVED`].
#[test]
#[ignore = "run by `the_named_programs_agree_under_the_cached_policy` as a child process"]
fn the_cached_policy_child()
{
    if Policy::from_environment() != Policy::Cached {
        return;
    }
    for named in named() {
        let name = named.program.name;
        let shows = Verdict::Halted(Some(String::from(named.shows)));
        let (commands, root) = focus(&named.program);
        let definitions = Definitions::new();
        let policy = |store: &mut Store| {
            evaluate(
                &commands,
                &definitions,
                root,
                Fuel::from(BUDGET),
                RunInputs::new(store),
            )
        };
        assert_eq!(
            shows,
            agree_with(Label(name), &commands, &definitions, root, policy),
            "{name} missing the cache"
        );
        assert_eq!(
            shows,
            agree(Label(name), &commands, &definitions, root),
            "{name} across the tiers"
        );
        assert_eq!(
            shows,
            agree_with(Label(name), &commands, &definitions, root, policy),
            "{name} served from the cache"
        );
    }
    writeln!(std::io::stdout().lock(), "{SERVED}").expect("the line is written");
}

/// The named programs answer fused what their unfused lowering answers on
/// the executor, with the answer each states, and each fused function is the
/// replay of its trace over the unfused one.
#[test]
fn a_fused_program_answers_what_its_unfused_lowering_answers()
{
    for named in named() {
        let name = named.program.name;
        let shows = Verdict::Halted(Some(String::from(named.shows)));
        let (commands, root) = focus(&named.program);
        let definitions = Definitions::new();
        let (Ok(fused), Ok(unfused)) = (
            lower(&commands, &definitions, root),
            lower_unfused(&commands, &definitions, root),
        )
        else {
            panic!("{name} lowers");
        };
        assert_eq!(
            replay(&unfused.function, &fused.fused).as_ref(),
            Ok(&fused.function),
            "{name}: the trace replays to the fused function"
        );
        let unfused = agree_with(Label(name), &commands, &definitions, root, |store| {
            evaluate_unfused_on(
                Tier::Executor,
                &commands,
                &definitions,
                root,
                Fuel::from(BUDGET),
                RunInputs::new(store),
            )
        });
        assert_eq!(shows, unfused, "{name} unfused");
    }
}

/// Forcing an owed constant and casing on one stop stuck alike on each tier,
/// and under the policy, holding the constant: forced, it is unobservable;
/// cased, unmatched. The dispatcher blames the constant from the value held.
#[test]
fn an_observed_opaque_constant_is_named_on_both_executors()
{
    let mut definitions = Definitions::new();
    let owed = definitions.push(Definition::Opaque);
    let mut forced = CoreArena::new();
    let constant = forced.value_constant(owed);
    let force = forced.computation_force(constant);
    let mut cased = CoreArena::new();
    let constant = cased.value_constant(owed);
    let variable = cased.value_variable(Zone::Intuitionistic, 0_u32.into());
    let arm = cased.computation_return(variable);
    let case = cased.computation_case(constant, &[arm, arm]);
    let programs = [
        Program {
            name: "force owed",
            core: forced,
            root: force,
        },
        Program {
            name: "case owed",
            core: cased,
            root: case,
        },
    ];
    for program in programs {
        let name = program.name;
        let (commands, root) = focus(&program);
        let verdict = agree(Label(name), &commands, &definitions, root);
        let policy = agree_with(Label(name), &commands, &definitions, root, |store| {
            evaluate(
                &commands,
                &definitions,
                root,
                Fuel::from(BUDGET),
                RunInputs::new(store),
            )
        });
        assert_eq!(verdict, policy, "{name} under the policy");
        let mut store = Store::new();
        let outcome = evaluate_on(
            Tier::Executor,
            &commands,
            &definitions,
            root,
            Fuel::from(BUDGET),
            RunInputs::new(&mut store),
        );
        let held = match outcome {
            Ok(Outcome::Stuck(
                Stuck::Unobservable {
                    value,
                    head: DestructorTag::Force,
                }
                | Stuck::Unmatched { value, .. },
            )) => store.value(value),
            other => panic!("{name}: stuck at the constant, not {other:?}"),
        };
        assert_eq!(
            Some(&HeapValue::Opaque(owed)),
            held,
            "{name} holds the constant"
        );
    }
}

/// A computed constant, `⟨x ← return 5; return (x, x)⟩`, runs its
/// computation the first time a run reads it, and every later read is that
/// one answer; one whose computation reads its own value sticks as a cycle.
#[test]
fn a_computed_constant_unfolds_once_to_its_answer()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Integer(5));
    let given = core.computation_return(five);
    let bound = core.value_variable(
        Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(0_u32),
    );
    let doubled = core.value_tuple(&[bound, bound]);
    let answer = core.computation_return(doubled);
    let computation = core.computation_bind(given, answer);
    let computed = core.value_returned(computation);
    let first = core.value_constant(ConstantIndex::from(0_usize));
    let cyclic = core.value_constant(ConstantIndex::from(1_usize));
    let reads_itself = core.computation_return(cyclic);
    let cycle = core.value_returned(reads_itself);
    let mut commands = CommandArena::new();
    let mut provenance = Provenance::new();
    let mut definitions = Definitions::new();
    for value in [computed, cycle] {
        let producer = focus_definition(&core, value, &mut commands, &mut provenance)
            .expect("a computed value focuses");
        definitions.push(Definition::Transparent(producer));
    }
    let both = core.value_tuple(&[first, first]);
    let mut root = |value| {
        let returned = core.computation_return(value);
        focus_computation(&core, returned, &mut commands, &mut provenance).expect("closed")
    };
    let twice = root(both);
    let looping = root(cyclic);

    for tier in [COMPARED, Tier::Executor] {
        let mut store = Store::new();
        let outcome = evaluate_on(
            tier,
            &commands,
            &definitions,
            twice,
            Fuel::from(BUDGET),
            RunInputs::new(&mut store),
        );
        let Ok(Outcome::Halted(pair)) = outcome
        else {
            panic!("{tier:?}: the pair halts: {outcome:?}");
        };
        let Some(&HeapValue::Constructed { ref fields, .. }) = store.value(pair)
        else {
            panic!("{tier:?}: a pair");
        };
        let &[left, right] = &**fields
        else {
            panic!("{tier:?}: two fields");
        };
        assert_eq!(left, right, "{tier:?}: both reads are the one run");
    }
    assert_eq!(
        Verdict::Halted(Some(String::from("⟨pair(pair(5, 5), pair(5, 5)) |+ ★⟩"))),
        agree(Label("(c0, c0)"), &commands, &definitions, twice),
        "the computed constant answers what its computation returns"
    );
    assert_eq!(
        Verdict::Stuck(Stuck::CyclicConstant(ConstantIndex::from(1_usize))),
        agree(Label("c1"), &commands, &definitions, looping),
        "a computation reading its own constant is a cycle"
    );
}
