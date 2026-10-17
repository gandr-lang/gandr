//! The stencils against the L machine: every program run on both tiers —
//! emitted native code where this host has a patcher, and the portable
//! executor everywhere — and each answer compared with the machine's, value
//! by value.

use alloc::collections::BTreeMap;
use std::path::Path;

use gandr_core_sequent::Definitions;
use gandr_core_term::CoreArena;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Engine;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use quenchant_shape::shape::Maybe;

use crate::generate::Generator;
use crate::generate::Shape;
use crate::support::Label;
use crate::support::Program;
use crate::support::Verdict;
use crate::support::agree;
use crate::support::focus;
use crate::support::named;

/// The tiers this host runs: both where a patcher exists.
///
/// # Specification
/// trivial.
fn tiers() -> Vec<Tier>
{
    if PATCHER {
        vec![Tier::Native, Tier::Executor]
    }
    else {
        vec![Tier::Executor]
    }
}

/// macOS arm64 and Linux x86-64 have a patcher: the build script emitted
/// its table, and a named program runs native there rather than declining
/// for want of one. The suites below then compare native code on these
/// hosts, so this line in a lane's log is the witness that it ran native.
#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    all(target_os = "linux", target_arch = "x86_64")
))]
#[test]
fn a_patcher_host_runs_native()
{
    const { assert!(PATCHER, "the build script found this host's patcher") };
    let program = named().swap_remove(0);
    let (commands, root) = focus(&program);
    assert_eq!(
        Verdict::Agreed,
        agree(
            Label(program.name),
            &commands,
            &Definitions::new(),
            root,
            Tier::Native
        ),
        "{} runs native",
        program.name
    );
}

/// The named programs — a return, a bind, a case, a constructor, their
/// composition, and answers that suspend a function or a thunk — halt on
/// both tiers with the machine's answer.
#[test]
fn the_named_programs_agree_on_both_executors()
{
    for program in named() {
        let (commands, root) = focus(&program);
        let definitions = Definitions::new();
        for tier in tiers() {
            assert_eq!(
                Verdict::Agreed,
                agree(Label(program.name), &commands, &definitions, root, tier),
                "{} on {tier:?}",
                program.name
            );
        }
    }
}

/// Closed positive-core programs of every size, sixty-four seeds per
/// budget, halt on both tiers with the machine's answer, or stick at an
/// unmatched constructor exactly where the machine sticks.
#[test]
fn the_generated_programs_agree_on_both_executors()
{
    let mut halted = 0_usize;
    for budget in [1_usize, 2, 4, 8, 16, 64, 256, 1024] {
        for seed in 0 .. 64_u64 {
            let mut core = CoreArena::new();
            let shape = Shape {
                seed: seed
                    .wrapping_mul(7919)
                    .wrapping_add(u64::try_from(budget).expect("small")),
                budget,
            };
            let root = Generator::program(shape, &mut core);
            let program = Program {
                name: "generated",
                core,
                root,
            };
            let (commands, command) = focus(&program);
            let definitions = Definitions::new();
            for tier in tiers() {
                match agree(
                    Label(&format!("seed {seed} budget {budget}")),
                    &commands,
                    &definitions,
                    command,
                    tier,
                ) {
                    Verdict::Agreed => halted = halted.saturating_add(1),
                    Verdict::BothUnmatched => {},
                    Verdict::Declined(declined) => {
                        panic!("seed {seed} budget {budget} on {tier:?}: declined {declined:?}")
                    },
                }
            }
        }
    }
    assert!(halted > 0, "the generator writes programs that halt");
}

/// Every declaration of the model corpus that states a `runs` outcome,
/// outside the pathological twins, gives the machine's evaluation on each
/// tier, or is declined: by the form the lowering refuses, or as an
/// unmatched case exactly where the machine sticks. The declines are counted
/// by reason and printed.
#[test]
fn the_corpus_runs_items_agree_on_both_executors()
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
    let mut walk = Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]);
    let engines: &[Engine] = if PATCHER {
        &[Engine::Native, Engine::Executor]
    }
    else {
        &[Engine::Executor]
    };
    let mut stated = 0_usize;
    let mut answered = 0_usize;
    let mut declined: BTreeMap<String, usize> = BTreeMap::new();
    while let Maybe::Present(step) = walk.step() {
        let Step::Source {
            path,
            composed:
                Composed::Settled {
                    report,
                    mut program,
                    ..
                },
            ..
        } = step
        else {
            continue;
        };
        if path
            .components()
            .any(|component| component.as_os_str() == "pathological")
        {
            continue;
        }
        for declaration in report.declarations() {
            let Stated::Verdict(Outcome::Runs(_)) = *declaration.stated()
            else {
                continue;
            };
            stated = stated.saturating_add(1);
            let constant = declaration.constant();
            let item = format!("{} {}", path.display(), declaration.name());
            let expected = program
                .evaluate_on(constant, Engine::Machine)
                .expect("the machine never declines");
            for &engine in engines {
                match program.evaluate_on(constant, engine) {
                    Ok(evaluation) => {
                        assert_eq!(expected, evaluation, "{item} on {engine:?}");
                        if engine == engines[0] {
                            answered = answered.saturating_add(1);
                        }
                    },
                    Err(Declined::Unmatched) => {
                        assert!(
                            matches!(expected, Evaluation::Stuck(_)),
                            "{item} on {engine:?}: unmatched where the machine gave {expected}"
                        );
                    },
                    Err(Declined::Lowering(form)) => {
                        if engine == engines[0] {
                            *declined.entry(format!("{form:?}")).or_default() += 1;
                        }
                    },
                    Err(other) => panic!("{item} on {engine:?}: declined {other:?}"),
                }
            }
        }
    }
    println!(
        "runs items {stated}, answered on {:?} {answered}, declined {declined:?}",
        engines[0]
    );
    assert!(answered > 0, "the corpus states runs the tiers answer");
}
