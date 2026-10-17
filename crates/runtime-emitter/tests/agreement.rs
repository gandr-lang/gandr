//! The emitter against the L machine: each named program lowered, emitted
//! or built for the executor, run, and its answer moved into a store and
//! compared with the machine's, value by value — on both tiers and through
//! the policy's own entry.

use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate;

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
/// captures and environments the transfer rebuilds — halt on both tiers and
/// under the policy with the machine's answer.
#[test]
fn the_named_programs_agree_on_both_executors()
{
    let tiers: &[Tier] = if PATCHER {
        &[Tier::Native, Tier::Executor]
    }
    else {
        &[Tier::Executor]
    };
    for program in named() {
        let (commands, root) = focus(&program);
        let definitions = Definitions::new();
        for &tier in tiers {
            assert_eq!(
                Verdict::Agreed,
                agree(Label(program.name), &commands, &definitions, root, tier),
                "{} on {tier:?}",
                program.name
            );
        }
        let policy = agree_with(
            Label(program.name),
            &commands,
            &definitions,
            root,
            |store| evaluate(&commands, &definitions, root, Fuel::from(BUDGET), store),
        );
        assert_eq!(Verdict::Agreed, policy, "{} under the policy", program.name);
    }
}

/// Forcing an owed constant and casing on one stick on each tier, and under
/// the policy, at the constant: the run names it as the machine's stuck
/// answer observes it, so the dispatcher blames it without the machine.
#[test]
fn an_observed_opaque_constant_is_named_on_both_executors()
{
    let tiers: &[Tier] = if PATCHER {
        &[Tier::Native, Tier::Executor]
    }
    else {
        &[Tier::Executor]
    };
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
        let (commands, root) = focus(&program);
        for &tier in tiers {
            assert_eq!(
                Verdict::BothOpaque,
                agree(Label(program.name), &commands, &definitions, root, tier),
                "{} on {tier:?}",
                program.name
            );
        }
        let policy = agree_with(
            Label(program.name),
            &commands,
            &definitions,
            root,
            |store| evaluate(&commands, &definitions, root, Fuel::from(BUDGET), store),
        );
        assert_eq!(
            Verdict::BothOpaque,
            policy,
            "{} under the policy",
            program.name
        );
    }
}
