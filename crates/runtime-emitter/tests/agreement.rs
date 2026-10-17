//! The emitter against the L machine: each named program lowered, emitted
//! or built for the executor, run, and its answer moved into a store and
//! compared with the machine's, value by value — on both tiers and through
//! the policy's own entry.

use gandr_core_sequent::Definitions;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate;

use crate::support::BUDGET;
use crate::support::Label;
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
