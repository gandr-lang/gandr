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
/// - requires: a well-formed pure computation without constants whose run fits
///   the fixture budget and whose terminal has a pure core reading.
/// - ensures: its terminal reading in the returned arena, or the common
///   semantic stop for a stuck elimination or an unbound variable.
/// - provides: the machine observation for differential comparison.
/// - panics: on a focus refusal, machine fault or unreadable terminal.
///
/// # Adequacy
/// - hypothesis: L2 — bounded closed generated computations halt and their
///   settled readings agree with the independent normalizer. L3 hand-built
///   bindings, applications, cases and malformed eliminations distinguish lost
///   environments, wrong branch selection and mismapped stops. Constant
///   unfolding and budget exhaustion are outside this helper.
/// - witness: `tests::differential::l_machine_is_total_and_deterministic`
/// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[anodized::spec(requires: core.computation(root).is_some(), ensures: |ref ret| match *ret {
    | Answer::Term { ref core, term } => core.computation(term).is_some(),
    | Answer::Stopped(_) => true,
})]
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
/// - requires: nothing.
/// - ensures: the common semantic stop for an unobservable apply or force, an
///   unmatched case, or an unbound value variable.
/// - provides: an evaluator-independent refusal vocabulary.
/// - panics: for any machine state outside those four classes.
///
/// # Adequacy
/// - hypothesis: L3 — hand-built applications, forces and cases with the wrong
///   head have their declared stops; an unbound forced variable remains
///   unbound. These distinguish exchanged stop classes; states impossible for
///   the supported focused fragment are not mapped.
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[anodized::spec(ensures: |ret| match *stuck {
    | Stuck::Unobservable { head: DestructorTag::Apply, .. } => ret == Stop::AppliedNonFunction,
    | Stuck::Unobservable { head: DestructorTag::Force, .. } => ret == Stop::ForcedNonThunk,
    | Stuck::Unmatched { .. } => ret == Stop::CasedNonInjection,
    | Stuck::UnboundVariable { .. } => ret == Stop::UnboundVariable,
    | _ => false,
})]
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
/// - requires: a well-formed pure computation without constants, within the
///   fixture's normalization budget.
/// - ensures: its normal form resolves in the returned arena, or evaluation
///   yields the common stop for a malformed elimination or unbound variable.
/// - provides: an independent normalizer observation for the machine.
/// - panics: on a readback refusal or an unsupported evaluation fault.
///
/// # Adequacy
/// - hypothesis: L2 — generated machine readings, normalized, agree with the
///   independent normalization-by-evaluation path. L3 exact first-order and
///   suspended-body fixtures distinguish unperformed reductions, wrong binding
///   and collapsed refusal classes. Evidence is bounded to the pure fixtures
///   and their budget, not arbitrary open code.
/// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
/// - witness: `tests::differential::first_order_returns_compare_exactly`
/// - witness: `tests::differential::thunks_compare_structurally_through_readback`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[anodized::spec(requires: core.computation(root).is_some(), ensures: |ref ret| match *ret {
    | Answer::Term { ref core, term } => core.computation(term).is_some(),
    | Answer::Stopped(_) => true,
})]
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
/// - requires: nothing.
/// - ensures: the common semantic stop for each wrong-head elimination and
///   unbound variable, without conflating the four classes.
/// - provides: the normalizer side of the shared refusal vocabulary.
/// - panics: for fuel, dangling-term, domain or machine-invariant faults, or a
///   non-returning bind outside the supported fixtures.
///
/// # Adequacy
/// - hypothesis: L3 — the malformed apply, force and case fixtures and the
///   unbound variable name their exact semantic stop in both evaluators. These
///   distinguish exchanged error classes; internal faults and resource failures
///   are deliberately outside this mapping.
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[anodized::spec(ensures: |ret| match fault {
    | EvalFault::AppliedNonFunction => ret == Stop::AppliedNonFunction,
    | EvalFault::ForcedNonThunk => ret == Stop::ForcedNonThunk,
    | EvalFault::CasedNonInjection => ret == Stop::CasedNonInjection,
    | EvalFault::UnboundVariable { .. } => ret == Stop::UnboundVariable,
    | _ => false,
})]
fn normaliser_stop(fault: EvalFault) -> Stop
{
    match fault {
        | EvalFault::AppliedNonFunction => Stop::AppliedNonFunction,
        | EvalFault::ForcedNonThunk => Stop::ForcedNonThunk,
        | EvalFault::CasedNonInjection => Stop::CasedNonInjection,
        | EvalFault::UnboundVariable { .. } => Stop::UnboundVariable,
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
/// - requires: a term answer is in the normalizer helper's supported domain.
/// - ensures: a stopped answer remains the same stop; a term answer has its
///   reading normalized, with any resulting term resolving in its arena.
/// - provides: the common observation for suspended machine readings.
/// - panics: on a normalization failure outside the helper's domain.
///
/// # Adequacy
/// - hypothesis: L2 — generated readings agree with independent normalization
///   after settling. L3 suspended-body examples distinguish a retained redex
///   from its normal form and preserve semantic stops. Only pure bounded
///   fixture readings are covered.
/// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
/// - witness: `tests::differential::thunks_compare_structurally_through_readback`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::refusal_classes_do_not_collapse_into_success`
#[anodized::spec(ensures: |ref ret| match *answer {
    | Answer::Stopped(stop) => matches!(*ret, Answer::Stopped(found) if found == stop),
    | Answer::Term { .. } => match *ret {
        | Answer::Term { ref core, term } => core.computation(term).is_some(),
        | Answer::Stopped(_) => true,
    },
})]
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
/// - requires: term answers hold acyclic graphs in the compared pure fragment.
/// - ensures: Same for structurally equal terms or identical semantic stops; a
///   term and a stop, unequal stops or unequal terms differ.
/// - provides: a common observation across the two evaluators.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unequal first-order answers differ while exact and
///   normalized fixtures agree in their declared relation; all refusal classes
///   remain distinct from successful answers. The comparison oracle separately
///   challenges address identity, node labels and each ordered child. This is
///   structural comparison, not equivalence modulo reduction.
/// - witness: `tests::differential::first_order_returns_compare_exactly`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::thunks_compare_structurally_through_readback`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
/// - witness: `tests::compare::structural_equality_ignores_addresses_but_not_labels`
/// - witness: `tests::compare::computation_comparison_preserves_every_child_role`
/// - witness: `tests::differential::refusal_classes_do_not_collapse_into_success`
#[anodized::spec(ensures: |ret| match (left, right) {
    | (&Answer::Stopped(first), &Answer::Stopped(second)) => (ret == Agreement::Same) == (first == second),
    | (&Answer::Term { core: ref first, term: first_root }, &Answer::Term { core: ref second, term: second_root }) =>
        ret != Agreement::Same || (first.computation(first_root).is_some() && second.computation(second_root).is_some()),
    | _ => ret == Agreement::Differ,
})]
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
/// - requires: each case is in both evaluator helpers' supported pure domain.
/// - ensures: each pair of observations has its case's declared relation: exact
///   agreement, agreement only after normalization, or the named stop.
/// - provides: the independent finite-case comparison oracle.
/// - panics: on a mismatched observation or an unsupported evaluator failure.
///
/// # Adequacy
/// - hypothesis: L3 — finite bindings, applications, both case branches,
///   suspended redexes and malformed eliminations have declared relations
///   between independent evaluator observations. They distinguish premature
///   normalization, lost bindings and wrong stops. The assertion loop covers
///   these pure fixtures, not arbitrary well-typed programs.
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[anodized::spec(requires: cases.iter().all(|case| case.core.computation(case.root).is_some()))]
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

/// Actual malformed eliminations remain distinct from one another and from a
/// value.
#[test]
fn refusal_classes_do_not_collapse_into_success()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let forced = core.computation_force(unit);
    let applied = core.computation_application(returned, unit);
    let value_answer = machine(&core, returned);
    let forced_answer = machine(&core, forced);
    let applied_answer = machine(&core, applied);
    assert!(matches!(
        forced_answer,
        Answer::Stopped(Stop::ForcedNonThunk)
    ));
    assert!(matches!(
        applied_answer,
        Answer::Stopped(Stop::AppliedNonFunction)
    ));
    assert_eq!(
        Agreement::Differ,
        agreement(&forced_answer, &applied_answer)
    );
    assert_eq!(Agreement::Differ, agreement(&value_answer, &forced_answer));
    assert_eq!(Agreement::Differ, agreement(&forced_answer, &value_answer));
    assert_eq!(
        Agreement::Same,
        agreement(&settled(&forced_answer), &forced_answer)
    );
}
