//! The L machine against normalisation by evaluation.
//!
//! `gandr-core-nbe` evaluates the core itself, by closures over a glued
//! domain, and shares no step with the machine, which runs focused commands
//! over a store. The suites compare what the two compute: the machine's
//! halted value read back as a core term, against the normaliser's normal
//! form. A first-order answer agrees node for node; an answer that suspends a
//! computation agrees once the machine's reading, which keeps a closure's body
//! as written, is normalised too; an ill-typed redex stops both at the same
//! elimination.

use alloc::vec::Vec;

use gandr_core_nbe::DomainArena;
use gandr_core_nbe::EvalFault;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_computation;
use gandr_core_nbe::readback_computation;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::Machine;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::StepCount;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use proptest::prelude::*;

use crate::compare::Agreement;
use crate::compare::same_computation;
use crate::generate::GeneratedRoot;
use crate::generate::Integer;
use crate::generate::computations;
use crate::generate::integer;

/// Where an evaluation stopped short of a value, named alike for both
/// evaluators.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stop
{
    /// An application met a value that is not a function.
    AppliedNonFunction,
    /// A force met a value that is not a thunk.
    ForcedNonThunk,
    /// A case met a value that is not an injection.
    CasedNonInjection,
    /// A variable no binding answers.
    UnboundVariable,
}

/// What one evaluator made of a computation.
#[derive(Debug)]
enum Answer
{
    /// A term and the arena holding it: the normaliser's normal form, or the
    /// machine's terminal read back.
    Term
    {
        /// The arena.
        core: CoreArena,
        /// The term.
        term: ComputationId,
    },
    /// The evaluation stopped short of a value.
    Stopped(Stop),
}

/// A variable's de Bruijn index in a hand-built case.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Index(u32);

/// A hand-built case's name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Label(&'static str);

/// How a hand-built case's two answers relate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Expected
{
    /// The machine's reading is the normal form, node for node.
    Exactly,
    /// The machine's reading keeps a redex under a binder, and is the normal
    /// form once normalised.
    Normalised,
    /// Both evaluators stop, at the named elimination.
    Stops(Stop),
}

/// One hand-built case: its name, its term and how its answers relate.
struct Case
{
    /// The name an assertion reports.
    label: Label,
    /// The arena holding the term.
    core: CoreArena,
    /// The term.
    root: ComputationId,
    /// How the machine's answer relates to the normaliser's.
    expected: Expected,
}

/// The intuitionistic variable at `index` in `core`.
///
/// # Specification
/// trivial.
fn variable(
    core: &mut CoreArena,
    index: Index,
) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index.0))
}

/// A case built by `build` into a fresh arena.
///
/// # Specification
/// trivial.
fn case(
    label: Label,
    expected: Expected,
    build: impl FnOnce(&mut CoreArena) -> ComputationId,
) -> Case
{
    let mut core = CoreArena::new();
    let root = build(&mut core);
    Case {
        label,
        core,
        root,
        expected,
    }
}

/// Run `root` of `core` on the L machine and read its terminal back.
///
/// # Specification
/// trivial.
fn machine(
    core: &CoreArena,
    root: ComputationId,
) -> Answer
{
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let command = focus_computation(core, root, &mut arena, &mut provenance)
        .expect("focusing is total on the pure fragment");
    let definitions = Definitions::new();
    let mut machine = Machine::new(&arena, &definitions);
    match machine.run(command, StepCount::from(1_000_000_usize)) {
        | Ok(Outcome::Halted(value)) => {
            let mut read = CoreArena::new();
            let term = machine
                .read_back(value, &mut read)
                .expect("a halted value of the pure fragment reads back");
            Answer::Term { core: read, term }
        },
        | Ok(Outcome::Stuck(stuck)) => Answer::Stopped(machine_stop(&stuck)),
        | Err(fault) => panic!("the machine faulted: {fault}"),
    }
}

/// The stop a machine's stuck configuration names.
///
/// # Specification
/// trivial.
fn machine_stop(stuck: &Stuck) -> Stop
{
    match *stuck {
        | Stuck::Unobservable {
            head: DestructorTag::Apply,
            ..
        } => Stop::AppliedNonFunction,
        | Stuck::Unobservable {
            head: DestructorTag::Force,
            ..
        } => Stop::ForcedNonThunk,
        | Stuck::Unmatched { .. } => Stop::CasedNonInjection,
        | Stuck::UnboundVariable { .. } => Stop::UnboundVariable,
        | Stuck::UnboundCovariable(_)
        | Stuck::UndefinedConstant(_)
        | Stuck::CyclicConstant(_)
        | Stuck::IllFormedCommand(_)
        | Stuck::IllFormedProducer(_)
        | Stuck::IllFormedConsumer(_) => {
            panic!("no focused core term stops the machine as: {stuck}")
        },
    }
}

/// Normalise `root` of `core` by evaluation and readback, with no
/// definitions.
///
/// # Specification
/// trivial.
fn normalised(
    core: &CoreArena,
    root: ComputationId,
) -> Answer
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = gandr_core_nbe::Definitions::new(&chain, &environment, environment.root());
    let fuel = Fuel::from(1_000_000_u32);
    let mut normal = core.clone();
    let mut domain = DomainArena::new();
    match eval_computation(&normal, &mut domain, definitions, fuel, root) {
        | Ok(head) => {
            let term = readback_computation(
                &mut normal,
                &mut domain,
                definitions,
                ReadbackMode::Unfolding,
                fuel,
                head,
            )
            .expect("a weak head of the pure fragment reads back");
            Answer::Term { core: normal, term }
        },
        | Err(fault) => Answer::Stopped(normaliser_stop(fault)),
    }
}

/// The stop a normaliser's fault names.
///
/// # Specification
/// trivial.
fn normaliser_stop(fault: EvalFault) -> Stop
{
    match fault {
        | EvalFault::AppliedNonFunction => Stop::AppliedNonFunction,
        | EvalFault::ForcedNonThunk => Stop::ForcedNonThunk,
        | EvalFault::CasedNonInjection => Stop::CasedNonInjection,
        | EvalFault::UnboundVariable { .. } => Stop::UnboundVariable,
        | EvalFault::TransportedNonPath
        | EvalFault::OutOfFuel
        | EvalFault::DanglingTerm
        | EvalFault::Domain(_)
        | EvalFault::BoundNonReturner
        | EvalFault::AppliedNonOperator
        | EvalFault::MachineInvariant => {
            panic!("no pure core term faults the normaliser as: {fault:?}")
        },
    }
}

/// The machine's answer with its reading normalised: what a suspended body
/// comes to once the normaliser runs it.
///
/// # Specification
/// trivial.
fn settled(answer: &Answer) -> Answer
{
    match *answer {
        | Answer::Term { ref core, term } => normalised(core, term),
        | Answer::Stopped(stop) => Answer::Stopped(stop),
    }
}

/// Whether two answers agree: the same stop, or terms equal node for node.
///
/// # Specification
/// trivial.
fn agreement(
    left: &Answer,
    right: &Answer,
) -> Agreement
{
    match (left, right) {
        | (
            &Answer::Term {
                core: ref left_core,
                term: left_term,
            },
            &Answer::Term {
                core: ref right_core,
                term: right_term,
            },
        ) => same_computation(left_core, left_term, right_core, right_term),
        | (&Answer::Stopped(left_stop), &Answer::Stopped(right_stop)) if left_stop == right_stop => {
            Agreement::Same
        },
        | (&Answer::Stopped(_), &Answer::Stopped(_) | &Answer::Term { .. })
        | (&Answer::Term { .. }, &Answer::Stopped(_)) => Agreement::Differ,
    }
}

/// Every case's two answers relate as it expects.
///
/// # Specification
/// trivial.
fn assert_cases(cases: Vec<Case>)
{
    for case in cases {
        let Label(label) = case.label;
        let ran = machine(&case.core, case.root);
        let normal = normalised(&case.core, case.root);
        match case.expected {
            | Expected::Exactly => assert_eq!(
                Agreement::Same,
                agreement(&ran, &normal),
                "{label}: the machine's reading is the normal form"
            ),
            | Expected::Normalised => {
                assert_eq!(
                    Agreement::Differ,
                    agreement(&ran, &normal),
                    "{label}: the machine's reading keeps a redex under a binder"
                );
                assert_eq!(
                    Agreement::Same,
                    agreement(&settled(&ran), &normal),
                    "{label}: the reading, normalised, is the normal form"
                );
            },
            | Expected::Stops(stop) => {
                assert_eq!(
                    Agreement::Same,
                    agreement(&ran, &Answer::Stopped(stop)),
                    "{label}: the machine stops at {stop:?}, not {ran:?}"
                );
                assert_eq!(
                    Agreement::Same,
                    agreement(&normal, &Answer::Stopped(stop)),
                    "{label}: the normaliser stops at {stop:?}, not {normal:?}"
                );
            },
        }
    }
}

/// `return v` for the value `build` mints.
///
/// # Specification
/// trivial.
fn returning(
    core: &mut CoreArena,
    build: impl FnOnce(&mut CoreArena) -> ValueId,
) -> ComputationId
{
    let value = build(core);
    core.computation_return(value)
}

/// A first-order answer read back from the machine is the normal form node
/// for node, and a different first-order answer is not.
#[test]
fn first_order_returns_compare_exactly()
{
    let bound = case(Label("a bound pair returned"), Expected::Exactly, |core| {
        let head = returning(core, |core| {
            let one = integer(core, Integer(1_i32));
            let unit = core.value_unit();
            let left = core.value_injection(Side::Left, unit);
            core.value_pair(one, left)
        });
        let body = returning(core, |core| variable(core, Index(0)));
        core.computation_bind(head, body)
    });
    let other = case(
        Label("the other injection returned"),
        Expected::Exactly,
        |core| {
            returning(core, |core| {
                let one = integer(core, Integer(1_i32));
                let unit = core.value_unit();
                let right = core.value_injection(Side::Right, unit);
                core.value_pair(one, right)
            })
        },
    );
    let ran = machine(&bound.core, bound.root);
    assert_eq!(
        Agreement::Same,
        agreement(&ran, &normalised(&bound.core, bound.root)),
        "the reading is the normal form"
    );
    assert_eq!(
        Agreement::Differ,
        agreement(&ran, &normalised(&other.core, other.root)),
        "a different first-order answer is told apart"
    );
}

/// A suspended body that still holds a redex reads back with it, and agrees
/// with the normal form once normalised: a returned thunk, a function
/// terminal, and a thunk whose body forces a captured thunk.
#[test]
fn thunks_compare_structurally_through_readback()
{
    assert_cases(alloc::vec![
        case(
            Label("a returned thunk over a bind"),
            Expected::Normalised,
            |core| {
                let head = returning(core, |core| integer(core, Integer(3_i32)));
                let returned = returning(core, |core| {
                    let inner = returning(core, |core| variable(core, Index(0)));
                    let body = returning(core, |core| variable(core, Index(0)));
                    let suspended = core.computation_bind(inner, body);
                    core.value_thunk(suspended)
                });
                core.computation_bind(head, returned)
            },
        ),
        case(
            Label("a function over a bind"),
            Expected::Normalised,
            |core| {
                let inner = returning(core, |core| variable(core, Index(0)));
                let body = returning(core, |core| variable(core, Index(0)));
                let bound = core.computation_bind(inner, body);
                core.computation_lambda(bound)
            },
        ),
        case(
            Label("a thunk forcing a captured thunk"),
            Expected::Normalised,
            |core| {
                let head = returning(core, |core| {
                    let one = returning(core, |core| integer(core, Integer(1_i32)));
                    core.value_thunk(one)
                });
                let returned = returning(core, |core| {
                    let captured = variable(core, Index(0));
                    let forced = core.computation_force(captured);
                    core.value_thunk(forced)
                });
                core.computation_bind(head, returned)
            },
        ),
    ]);
}

/// The pure spine: returns of first-order data, bind, force, a thunk forced
/// twice, β and a curried application, case on both injections, and three
/// ill-typed redexes that stop both evaluators at the same elimination.
#[test]
fn hand_built_pure_spine_cases_agree()
{
    assert_cases(alloc::vec![
        case(Label("return an integer"), Expected::Exactly, |core| {
            returning(core, |core| integer(core, Integer(42_i32)))
        }),
        case(Label("return a pair"), Expected::Exactly, |core| {
            returning(core, |core| {
                let first = integer(core, Integer(1_i32));
                let second = integer(core, Integer(-2_i32));
                core.value_pair(first, second)
            })
        }),
        case(Label("return an injection"), Expected::Exactly, |core| {
            returning(core, |core| {
                let unit = core.value_unit();
                core.value_injection(Side::Left, unit)
            })
        }),
        case(Label("bind threads a value"), Expected::Exactly, |core| {
            let head = returning(core, |core| integer(core, Integer(3_i32)));
            let body = returning(core, |core| variable(core, Index(0)));
            core.computation_bind(head, body)
        }),
        case(Label("force a thunk"), Expected::Exactly, |core| {
            let body = returning(core, |core| integer(core, Integer(5_i32)));
            let thunk = core.value_thunk(body);
            core.computation_force(thunk)
        }),
        case(Label("a thunk forced twice"), Expected::Exactly, |core| {
            let head = returning(core, |core| {
                let nine = returning(core, |core| integer(core, Integer(9_i32)));
                core.value_thunk(nine)
            });
            let first = variable(core, Index(0));
            let force_first = core.computation_force(first);
            let again = variable(core, Index(1));
            let force_again = core.computation_force(again);
            let answer = returning(core, |core| {
                let earlier = variable(core, Index(1));
                let later = variable(core, Index(0));
                core.value_pair(earlier, later)
            });
            let inner = core.computation_bind(force_again, answer);
            let middle = core.computation_bind(force_first, inner);
            core.computation_bind(head, middle)
        },),
        case(Label("β"), Expected::Exactly, |core| {
            let body = returning(core, |core| variable(core, Index(0)));
            let function = core.computation_lambda(body);
            let argument = integer(core, Integer(11_i32));
            core.computation_application(function, argument)
        }),
        case(Label("a curried application"), Expected::Exactly, |core| {
            let body = returning(core, |core| variable(core, Index(1)));
            let inner = core.computation_lambda(body);
            let function = core.computation_lambda(inner);
            let first = integer(core, Integer(1_i32));
            let applied = core.computation_application(function, first);
            let second = integer(core, Integer(2_i32));
            core.computation_application(applied, second)
        },),
        case(Label("case on the left"), Expected::Exactly, |core| {
            let one = integer(core, Integer(1_i32));
            let scrutinee = core.value_injection(Side::Left, one);
            let on_left = returning(core, |core| variable(core, Index(0)));
            let on_right = returning(core, |core| integer(core, Integer(0_i32)));
            core.computation_case(scrutinee, on_left, on_right)
        }),
        case(Label("case on the right"), Expected::Exactly, |core| {
            let two = integer(core, Integer(2_i32));
            let scrutinee = core.value_injection(Side::Right, two);
            let on_left = returning(core, |core| integer(core, Integer(0_i32)));
            let on_right = returning(core, |core| variable(core, Index(0)));
            core.computation_case(scrutinee, on_left, on_right)
        }),
        case(
            Label("a returner applied"),
            Expected::Stops(Stop::AppliedNonFunction),
            |core| {
                let head = returning(core, |core| integer(core, Integer(1_i32)));
                let argument = integer(core, Integer(2_i32));
                core.computation_application(head, argument)
            },
        ),
        case(
            Label("an integer forced"),
            Expected::Stops(Stop::ForcedNonThunk),
            |core| {
                let one = integer(core, Integer(1_i32));
                core.computation_force(one)
            },
        ),
        case(
            Label("an integer cased"),
            Expected::Stops(Stop::CasedNonInjection),
            |core| {
                let one = integer(core, Integer(1_i32));
                let on_left = returning(core, CoreArena::value_unit);
                let on_right = returning(core, CoreArena::value_unit);
                core.computation_case(one, on_left, on_right)
            },
        ),
    ]);
}

/// Terminals that close over their environment read back as the normal form
/// node for node: a returned thunk and a function over a captured value, a
/// curried function, and a function returning a thunk.
#[test]
fn hand_built_exact_readback_cases_agree()
{
    assert_cases(alloc::vec![
        case(
            Label("a returned thunk over a captured value"),
            Expected::Exactly,
            |core| {
                let head = returning(core, |core| integer(core, Integer(5_i32)));
                let returned = returning(core, |core| {
                    let body = returning(core, |core| variable(core, Index(0)));
                    core.value_thunk(body)
                });
                core.computation_bind(head, returned)
            },
        ),
        case(
            Label("a function over a captured value"),
            Expected::Exactly,
            |core| {
                let head = returning(core, |core| integer(core, Integer(5_i32)));
                let body = returning(core, |core| variable(core, Index(1)));
                let function = core.computation_lambda(body);
                core.computation_bind(head, function)
            },
        ),
        case(Label("a curried function"), Expected::Exactly, |core| {
            let body = returning(core, |core| {
                let outer = variable(core, Index(1));
                let inner = variable(core, Index(0));
                core.value_pair(outer, inner)
            });
            let inner = core.computation_lambda(body);
            core.computation_lambda(inner)
        }),
        case(
            Label("a function returning a thunk"),
            Expected::Exactly,
            |core| {
                let body = returning(core, |core| {
                    let suspended = returning(core, |core| variable(core, Index(0)));
                    core.value_thunk(suspended)
                });
                core.computation_lambda(body)
            },
        ),
    ]);
}

/// A forced variable no binding answers stops both evaluators, the machine
/// with an unbound variable rather than a fault.
#[test]
fn an_unbound_forced_name_is_still_stuck()
{
    assert_cases(alloc::vec![case(
        Label("an unbound name forced and applied"),
        Expected::Stops(Stop::UnboundVariable),
        |core| {
            let name = variable(core, Index(0));
            let forced = core.computation_force(name);
            let five = integer(core, Integer(5_i32));
            core.computation_application(forced, five)
        },
    )]);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// Every generated closed, well-typed computation halts within the
    /// budget, and two runs of it read back as the same term.
    #[test]
    fn l_machine_is_total_and_deterministic(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let first = machine(&generated.core, root);
        let second = machine(&generated.core, root);
        prop_assert!(matches!(first, Answer::Term { .. }), "a closed, well-typed computation stopped: {:?}", first);
        prop_assert_eq!(Agreement::Same, agreement(&first, &second), "two runs read back apart");
    }

    /// The machine's reading of every generated closed, well-typed
    /// computation, normalised, is the normaliser's normal form of it.
    #[test]
    fn the_l_machine_agrees_with_normalisation_by_evaluation(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let ran = machine(&generated.core, root);
        let normal = normalised(&generated.core, root);
        prop_assert_eq!(
            Agreement::Same,
            agreement(&settled(&ran), &normal),
            "the machine read back {:?} against the normal form {:?}", ran, normal
        );
    }
}
