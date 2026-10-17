//! The emitter across the tiers: each named program lowered, emitted or
//! built for the executor, run, and its answer moved into a store — native
//! code's compared with the executor's value by value, through the policy's
//! own entry too, and each with the answer the program states.

use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate;
use gandr_runtime_emitter::evaluate_on;

use crate::support::BUDGET;
use crate::support::Label;
use crate::support::Program;
use crate::support::Verdict;
use crate::support::agree;
use crate::support::agree_with;
use crate::support::focus;
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
            evaluate(&commands, &definitions, root, Fuel::from(BUDGET), store)
        });
        assert_eq!(shows, policy, "{name} under the policy");
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
            evaluate(&commands, &definitions, root, Fuel::from(BUDGET), store)
        });
        assert_eq!(verdict, policy, "{name} under the policy");
        let mut store = Store::new();
        let outcome = evaluate_on(
            Tier::Executor,
            &commands,
            &definitions,
            root,
            Fuel::from(BUDGET),
            &mut store,
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
