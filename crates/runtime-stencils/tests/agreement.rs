//! The stencils across the tiers: every program run on emitted native code
//! where this host has a patcher and on the portable executor, and the two
//! answers compared value by value; each named program and each witness
//! below also states the answer it expects.

use alloc::collections::BTreeMap;
use core::convert::Infallible;
use core::fmt::Write as _;
use core::ops::ControlFlow;
use std::path::Path;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::ConsumerId;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::CopatternArm;
use gandr_core_sequent::CovariableIndex;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::PatternArm;
use gandr_core_sequent::ProducerArity;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::focus_value;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Side;
use gandr_runtime_emitter::Fuel;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::dispatches;
use gandr_runtime_emitter::evaluate_on;
use gandr_runtime_emitter::evaluate_unfused_on;
use gandr_runtime_emitter::lower;
use gandr_runtime_emitter::lower_unfused;
use gandr_runtime_emitter::replay;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Engine;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_theory_cell_complexes::Polarity;

use crate::generate::Generator;
use crate::generate::Shape;
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

/// arm64 on macOS and Linux, and Linux x86-64, have a patcher: the build
/// script emitted its table, and a named program runs native there rather
/// than declining for want of one. The suites below then compare native code
/// on these hosts, so this line in a lane's log is the witness that it ran
/// native.
#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    all(
        target_os = "linux",
        any(target_arch = "aarch64", target_arch = "x86_64")
    )
))]
#[test]
fn a_patcher_host_runs_native()
{
    const { assert!(PATCHER, "the build script found this host's patcher") };
    assert_eq!(
        Tier::Native,
        COMPARED,
        "native code is what a run is compared on"
    );
    let named = named().swap_remove(0);
    let (commands, root) = focus(&named.program);
    assert_eq!(
        Verdict::Halted(Some(String::from(named.shows))),
        agree(
            Label(named.program.name),
            &commands,
            &Definitions::new(),
            root
        ),
        "{} runs native",
        named.program.name
    );
}

/// The named programs — a return, a bind, a case, a constructor, their
/// composition, answers that suspend a function or a thunk, primitive calls,
/// a resumed reified stack and a projected lazy product — halt alike on both
/// tiers with the answer each states.
#[test]
fn the_named_programs_agree_on_both_executors()
{
    let mut differing = Vec::new();
    for named in named() {
        let (commands, root) = focus(&named.program);
        let verdict = agree(
            Label(named.program.name),
            &commands,
            &Definitions::new(),
            root,
        );
        if verdict != Verdict::Halted(Some(String::from(named.shows))) {
            differing.push(format!("{}: {verdict:?}", named.program.name));
        }
    }
    assert!(
        differing.is_empty(),
        "programs answering other than they state:\n{}",
        differing.join("\n")
    );
}

/// Closed positive-core programs of every size, sixty-four seeds per
/// budget, halt alike on both tiers, or stop stuck alike.
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
            match agree(
                Label(&format!("seed {seed} budget {budget}")),
                &commands,
                &Definitions::new(),
                command,
            ) {
                Verdict::Halted(_) => halted = halted.saturating_add(1),
                Verdict::Stuck(_) => {},
                Verdict::Declined(declined) => {
                    panic!("seed {seed} budget {budget}: declined {declined:?}")
                },
            }
        }
    }
    assert!(halted > 0, "the generator writes programs that halt");
}

/// Every named program and the generated programs of every size answer fused
/// what their unfused lowering answers on the executor. Each fused function
/// is the replay of its trace over the unfused one and costs one dispatch
/// fewer per fusion, and fusions occur.
#[test]
fn a_fused_program_answers_what_its_unfused_lowering_answers()
{
    let mut programs: Vec<Program> = named().into_iter().map(|named| named.program).collect();
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
            programs.push(Program {
                name: "generated",
                core,
                root,
            });
        }
    }
    let mut fusions = 0_usize;
    let mut name = String::new();
    for (index, program) in programs.iter().enumerate() {
        let (commands, root) = focus(program);
        let definitions = Definitions::new();
        name.clear();
        write!(name, "{} #{index}", program.name).expect("a name writes");
        let (Ok(fused), Ok(unfused)) = (
            lower(&commands, &definitions, root),
            lower_unfused(&commands, &definitions, root),
        )
        else {
            continue;
        };
        assert_eq!(
            replay(&unfused.function, &fused.fused).as_ref(),
            Ok(&fused.function),
            "{name}: the trace replays to the fused function"
        );
        assert_eq!(
            dispatches(&fused.function)
                .0
                .saturating_add(fused.fused.len()),
            dispatches(&unfused.function).0,
            "{name}: one dispatch fewer per fusion"
        );
        fusions = fusions.saturating_add(fused.fused.len());
        let _verdict = agree_with(Label(&name), &commands, &definitions, root, |store| {
            evaluate_unfused_on(
                Tier::Executor,
                &commands,
                &definitions,
                root,
                Fuel::from(BUDGET),
                store,
            )
        });
    }
    assert!(fusions > 0, "the programs fuse a constant bound");
}

/// Every declaration of the model corpus that states a `runs` outcome,
/// outside the pathological twins, evaluates on the executor to the run it
/// states and on native code as on the executor, or both decline alike. The
/// answers are counted, the declines by reason, and printed.
#[test]
fn the_corpus_runs_items_agree_on_both_executors()
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus");
    let walk = Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]);
    let mut stated = 0_usize;
    let mut answered = 0_usize;
    let mut declined: BTreeMap<String, usize> = BTreeMap::new();
    let mut item = String::new();
    let mut rendered = String::new();
    let ControlFlow::Continue(_report) =
        walk.visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
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
                return ControlFlow::Continue(());
            };
            if path
                .components()
                .any(|component| component.as_os_str() == "pathological")
            {
                return ControlFlow::Continue(());
            }
            for declaration in report.declarations() {
                let Stated::Verdict(gandr_surface_corpus::Outcome::Runs(ref spelled)) =
                    *declaration.stated()
                else {
                    continue;
                };
                stated = stated.saturating_add(1);
                let constant = declaration.constant();
                item.clear();
                write!(item, "{} {}", path.display(), declaration.name()).expect("an item writes");
                let expected = program.evaluate_on(constant, Engine::Executor);
                if PATCHER {
                    assert_eq!(
                        expected,
                        program.evaluate_on(constant, Engine::Native),
                        "{item}: native code against the executor"
                    );
                }
                match expected {
                    Ok(ref evaluation) => {
                        rendered.clear();
                        write!(rendered, "{evaluation}").expect("an evaluation writes");
                        assert_eq!(
                            spelled.as_ref(),
                            rendered,
                            "{item}: the executor against the run it states"
                        );
                        answered = answered.saturating_add(1);
                    },
                    Err(reason) => *declined.entry(format!("{reason:?}")).or_default() += 1,
                }
            }
            ControlFlow::Continue(())
        });
    println!("runs items {stated}, answered {answered}, declined {declined:?}");
    assert!(answered > 0, "the corpus states runs the tiers answer");
}

/// The literal `value` focused into `commands`.
///
/// # Specification
/// trivial.
fn literal(
    commands: &mut CommandArena,
    value: Integer,
) -> ProducerId
{
    let mut core = CoreArena::new();
    let literal = integer(&mut core, value);
    focus_value(&core, literal, commands, &mut Provenance::new()).expect("a literal focuses")
}

/// The cut of `producer` against `consumer` at `polarity`.
///
/// # Specification
/// trivial.
fn cut(
    commands: &mut CommandArena,
    polarity: Polarity,
    producer: ProducerId,
    consumer: ConsumerId,
) -> CommandId
{
    commands
        .mint_cut(polarity, producer, consumer)
        .expect("live children")
}

/// The covariable at index zero.
///
/// # Specification
/// trivial.
fn innermost_covariable(commands: &mut CommandArena) -> ConsumerId
{
    commands
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf")
}

/// `μ̃x. ⟨x |polarity consumer⟩`: bind the value met, then cut it against
/// `consumer`.
///
/// # Specification
/// trivial.
fn bound_then(
    commands: &mut CommandArena,
    polarity: Polarity,
    consumer: ConsumerId,
) -> ConsumerId
{
    let variable = commands
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("a leaf");
    let body = cut(commands, polarity, variable, consumer);
    commands
        .mint_consumer(ConsumerNode::MuTilde { body })
        .expect("a live body")
}

/// A lazy product bound to a variable answers each projection with its own
/// arm, and a head it has no arm for — `force`, `apply` — sticks naming the
/// product: the object is entered with the observation, which picks the arm.
#[test]
fn an_object_answers_its_arms_and_sticks_on_the_rest()
{
    let mut commands = CommandArena::new();
    let top = commands.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let arms = [Integer(1), Integer(2), Integer(3)]
        .into_iter()
        .enumerate()
        .map(|(component, value)| {
            let answer = literal(&mut commands, value);
            let back = innermost_covariable(&mut commands);
            CopatternArm {
                destructor: DestructorTag::Project(Component::from(component)),
                body: cut(&mut commands, Polarity::Positive, answer, back),
            }
        })
        .collect::<Box<[_]>>();
    let pair = commands
        .mint_producer(ProducerNode::Cocase { arms })
        .expect("live arms");
    let unit = commands
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf");
    let observe = |commands: &mut CommandArena, tag, producers: &[ProducerId]| {
        commands
            .mint_consumer(ConsumerNode::Destructor {
                tag,
                producers: Box::from(producers),
                consumers: Box::from([top]),
            })
            .expect("live children")
    };
    let observations = [
        (DestructorTag::Project(Component::from(0_usize)), &[][..]),
        (DestructorTag::Project(Component::from(1_usize)), &[][..]),
        (DestructorTag::Project(Component::from(2_usize)), &[][..]),
        (DestructorTag::Force, &[][..]),
        (DestructorTag::Apply, &[unit][..]),
    ]
    .map(|(tag, producers)| {
        let observation = observe(&mut commands, tag, producers);
        let bound = bound_then(&mut commands, Polarity::Negative, observation);
        (tag, cut(&mut commands, Polarity::Negative, pair, bound))
    });
    let definitions = Definitions::new();
    for (tag, root) in observations {
        let verdict = agree(Label(&format!("{tag:?}")), &commands, &definitions, root);
        match tag {
            DestructorTag::Project(component) => assert_eq!(
                Verdict::Halted(Some(format!("⟨{} |+ ★⟩", usize::from(component) + 1))),
                verdict
            ),
            DestructorTag::Force | DestructorTag::Apply => assert!(
                matches!(verdict, Verdict::Stuck(Stuck::Unobservable { head, .. }) if head == tag),
                "{tag:?} sticks at the pair: {verdict:?}"
            ),
        }
    }
}

/// A capture bound by name stays suspended until a consumer meets it, then
/// runs its body against that consumer: cut against `★`, rebound and then
/// cut, or matched by a case, it answers what its body returns; ignored, it
/// never runs, though its body would stick.
#[test]
fn a_suspended_capture_runs_against_the_consumer_it_meets()
{
    let mut commands = CommandArena::new();
    let top = commands.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let one = literal(&mut commands, Integer(1));
    let zero = literal(&mut commands, Integer(0));
    let back = innermost_covariable(&mut commands);
    let returns_one = cut(&mut commands, Polarity::Positive, one, back);
    let capture = commands
        .mint_producer(ProducerNode::Mu { body: returns_one })
        .expect("a live body");
    let injected = commands
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Injection(Side::Right.into()),
            producers: Box::from([one]),
            consumers: Box::from([]),
        })
        .expect("a live field");
    let back = innermost_covariable(&mut commands);
    let returns_injected = cut(&mut commands, Polarity::Positive, injected, back);
    let injecting = commands
        .mint_producer(ProducerNode::Mu {
            body: returns_injected,
        })
        .expect("a live body");
    let forced_back = innermost_covariable(&mut commands);
    let force = commands
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([forced_back]),
        })
        .expect("live children");
    let unit = commands
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf");
    let sticks = cut(&mut commands, Polarity::Positive, unit, force);
    let sticking = commands
        .mint_producer(ProducerNode::Mu { body: sticks })
        .expect("a live body");

    let met = bound_then(&mut commands, Polarity::Positive, top);
    let rebound = bound_then(&mut commands, Polarity::Positive, met);
    let payload = commands
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("a leaf");
    let arms = [(Side::Left, zero), (Side::Right, payload)].map(|(side, answer)| PatternArm {
        constructor: ConstructorTag::Injection(side.into()),
        body: cut(&mut commands, Polarity::Positive, answer, top),
    });
    let case = commands
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from(arms),
        })
        .expect("live arms");
    let matched = bound_then(&mut commands, Polarity::Positive, case);
    let ignored_body = cut(&mut commands, Polarity::Positive, zero, top);
    let ignored = commands
        .mint_consumer(ConsumerNode::MuTilde { body: ignored_body })
        .expect("a live body");
    let programs = [
        ("met by ★", capture, met, "⟨1 |+ ★⟩"),
        ("rebound, then met by ★", capture, rebound, "⟨1 |+ ★⟩"),
        ("met by a case", injecting, matched, "⟨1 |+ ★⟩"),
        ("ignored", sticking, ignored, "⟨0 |+ ★⟩"),
    ];
    let definitions = Definitions::new();
    for (name, suspended, consumer, shows) in programs {
        let root = cut(&mut commands, Polarity::Negative, suspended, consumer);
        assert_eq!(
            Verdict::Halted(Some(String::from(shows))),
            agree(Label(name), &commands, &definitions, root),
            "a capture {name}"
        );
    }
}

/// A transparent constant unfolds the first time a run reads it and is the
/// same value at every later read; an opaque one stays itself; one whose
/// definition reads itself sticks as a cycle, and one never defined sticks
/// where it is read.
#[test]
fn constants_unfold_once_and_a_cycle_is_stuck()
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, Integer(5));
    let five_body = core.computation_return(five);
    let suspended = core.value_thunk(five_body);
    let first = core.value_constant(ConstantIndex::from(0_usize));
    let opaque = core.value_constant(ConstantIndex::from(1_usize));
    let cyclic = core.value_constant(ConstantIndex::from(2_usize));
    let undefined = core.value_constant(ConstantIndex::from(9_usize));
    let mut commands = CommandArena::new();
    let mut provenance = Provenance::new();
    let mut definitions = Definitions::new();
    let body = focus_value(&core, suspended, &mut commands, &mut provenance).expect("a thunk");
    definitions.push(Definition::Transparent(body));
    definitions.push(Definition::Opaque);
    let loops = focus_value(&core, cyclic, &mut commands, &mut provenance).expect("a constant");
    definitions.push(Definition::Transparent(loops));
    let both = core.value_tuple(&[first, first]);
    let opaque_first = core.value_tuple(&[opaque, first]);
    let mut root = |value| {
        let returned = core.computation_return(value);
        focus_computation(&core, returned, &mut commands, &mut provenance).expect("closed")
    };
    let twice = root(both);
    let kept = root(opaque_first);
    let looping = root(cyclic);
    let missing = root(undefined);

    for tier in [COMPARED, Tier::Executor] {
        let mut store = Store::new();
        let outcome = evaluate_on(
            tier,
            &commands,
            &definitions,
            twice,
            Fuel::from(BUDGET),
            &mut store,
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
        assert_eq!(left, right, "{tier:?}: both reads are the one unfolding");
    }
    assert_eq!(
        Verdict::Halted(Some(String::from(
            "⟨pair(c1, {force(α) ⇒ ⟨5 |+ α0⟩}) |+ ★⟩"
        ))),
        agree(Label("(c1, c0)"), &commands, &definitions, kept),
        "the opaque constant stays itself and the transparent one unfolds"
    );
    assert_eq!(
        Verdict::Stuck(Stuck::CyclicConstant(ConstantIndex::from(2_usize))),
        agree(Label("c2"), &commands, &definitions, looping),
        "a definition reading its own value is a cycle"
    );
    assert_eq!(
        Verdict::Stuck(Stuck::UndefinedConstant(ConstantIndex::from(9_usize))),
        agree(Label("c9"), &commands, &definitions, missing),
        "a constant never defined sticks where it is read"
    );
}
