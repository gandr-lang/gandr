//! The runtime's tiers against normalisation by evaluation.
//!
//! `gandr-core-nbe` evaluates the core itself, by closures over a glued
//! domain, and shares no step with the tiers, which run focused commands as
//! native code or through the portable executor. The suites compare what the
//! two compute: a run's halted value read back as a core term, against the
//! normaliser's normal form. A first-order answer agrees node for node; an
//! answer that suspends a computation agrees once the run's reading, which
//! keeps a closure's body as written, is normalised too; an ill-typed redex
//! stops both at the same elimination. Recursive definitions meet two
//! strategies here: a run unfolds a fixpoint when it is forced, the
//! normaliser when it is applied to a canonical argument, and on a closed
//! first-order answer the two agree.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::EvalFault;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_computation;
use gandr_core_nbe::readback_computation;
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::read_back_terminal;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;
use gandr_runtime_emitter::Declined;
use gandr_runtime_emitter::Form;
use gandr_runtime_emitter::PATCHER;
use gandr_runtime_emitter::Tier;
use gandr_runtime_emitter::evaluate_on;
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
    /// A case met a value that is not an injection it has an arm for.
    CasedNonInjection,
    /// A nominal match met a value that is not a constructor it has a branch
    /// for.
    UnmatchedConstructor,
    /// A projection met a value that is not a tuple or a record holding the
    /// component or the label it names.
    UnprojectedField,
    /// A variable no binding answers.
    UnboundVariable,
}

/// What one evaluator made of a computation.
#[derive(Debug)]
enum Answer
{
    /// A term and the arena holding it: the normaliser's normal form, or a
    /// run's terminal read back.
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
    /// The run's reading is the normal form, node for node.
    Exactly,
    /// The run's reading keeps a redex under a binder, and is the normal
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
    /// How the run's answer relates to the normaliser's.
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

/// Run `root` of `core` on every tier this host has, check the tiers' readings
/// agree, and answer the executor's.
///
/// # Specification
/// - requires: a well-formed pure computation without constants whose run fits
///   the fixture budget and whose terminal has a pure core reading.
/// - ensures: its terminal reading in the returned arena, or the common
///   semantic stop for a stuck elimination or an unbound variable.
/// - provides: the tiers' observation for differential comparison.
/// - panics: on a focus refusal, a tier declining other than for an unbound
///   variable, an unreadable terminal, or two tiers reading apart.
///
/// # Adequacy
/// - hypothesis: L2 — bounded closed generated computations halt and their
///   settled readings agree with the independent normalizer. L3 hand-built
///   bindings, applications, cases and malformed eliminations distinguish lost
///   environments, wrong branch selection and mismapped stops. Constant
///   unfolding and budget exhaustion are outside this helper.
/// - witness: `tests::differential::the_tiers_are_total_and_deterministic`
/// - witness: `tests::differential::the_tiers_agree_with_normalisation_by_evaluation`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `tests::differential::hand_built_declared_data_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[spec(requires: core.computation(root).is_some(), ensures: |ref ret| match *ret {
    | Answer::Term { ref core, term } => core.computation(term).is_some(),
    | Answer::Stopped(_) => true,
})]
fn on_tiers(
    core: &CoreArena,
    root: ComputationId,
) -> Answer
{
    let mut arena = CommandArena::new();
    let mut provenance = Provenance::new();
    let command = focus_computation(core, root, &mut arena, &mut provenance)
        .expect("focusing is total on the pure fragment");
    let definitions = Definitions::new();
    let tiers: &[Tier] = if PATCHER {
        &[Tier::Native, Tier::Executor]
    }
    else {
        &[Tier::Executor]
    };
    let mut answers: Vec<Answer> = tiers
        .iter()
        .map(|&tier| {
            let mut store = Store::new();
            let fuel = gandr_runtime_emitter::Fuel::from(1_usize << 20_u32);
            match evaluate_on(tier, &arena, &definitions, command, fuel, &mut store) {
                Ok(Outcome::Halted(value)) => {
                    let mut read = CoreArena::new();
                    let term = read_back_terminal(&arena, &store, value, &mut read)
                        .expect("a halted value of the pure fragment reads back");
                    Answer::Term { core: read, term }
                },
                Ok(Outcome::Stuck(stuck)) => Answer::Stopped(tier_stop(&arena, &stuck)),
                Err(Declined::Lowering(Form::Unbound)) => Answer::Stopped(Stop::UnboundVariable),
                Err(declined) => panic!("{tier:?} declined: {declined}"),
            }
        })
        .collect();
    let executor = answers.pop().expect("the executor runs on every host");
    for native in &answers {
        assert_eq!(
            Agreement::Same,
            agreement(native, &executor),
            "native code read back {native:?} against the executor's {executor:?}"
        );
    }
    executor
}

/// The stop a tier's stuck run names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the common semantic stop for an unobservable apply or force, an
///   unmatched structural or nominal match, or an unmatched selection.
/// - provides: an evaluator-independent refusal vocabulary.
/// - panics: for any stop outside those five classes.
///
/// # Adequacy
/// - hypothesis: L3 — hand-built applications, forces, cases and nominal
///   matches with the wrong head have their declared stops. These distinguish
///   exchanged stop classes; stops impossible for the supported focused
///   fragment are not mapped.
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_declared_data_cases_agree`
/// - witness: `tests::differential::hand_built_projection_cases_agree`
#[spec(ensures: |ret| match *stuck {
    | Stuck::Unobservable { head: DestructorTag::Apply, .. } => ret == Stop::AppliedNonFunction,
    | Stuck::Unobservable { head: DestructorTag::Force, .. } => ret == Stop::ForcedNonThunk,
    | Stuck::Unmatched { arms, .. } => match arena.consumer(arms) {
        | Some(&ConsumerNode::DataCase { .. }) => ret == Stop::UnmatchedConstructor,
        | Some(&ConsumerNode::Select { .. }) => ret == Stop::UnprojectedField,
        | _ => ret == Stop::CasedNonInjection,
    },
    | _ => false,
})]
fn tier_stop(
    arena: &CommandArena,
    stuck: &Stuck,
) -> Stop
{
    match *stuck {
        Stuck::Unobservable {
            head: DestructorTag::Apply,
            ..
        } => Stop::AppliedNonFunction,
        Stuck::Unobservable {
            head: DestructorTag::Force,
            ..
        } => Stop::ForcedNonThunk,
        Stuck::Unmatched { arms, .. } => match arena.consumer(arms) {
            Some(&ConsumerNode::DataCase { .. }) => Stop::UnmatchedConstructor,
            Some(&ConsumerNode::Select { .. }) => Stop::UnprojectedField,
            Some(
                &(ConsumerNode::Case { .. }
                | ConsumerNode::ListFold { .. }
                | ConsumerNode::Covariable(_)
                | ConsumerNode::MuTilde { .. }
                | ConsumerNode::Destructor { .. }
                | ConsumerNode::Top),
            )
            | None => Stop::CasedNonInjection,
        },
        Stuck::PerformNoHandler(_)
        | Stuck::ShiftNoReset(_)
        | Stuck::ResumedNonStack { .. }
        | Stuck::Unobservable {
            head: DestructorTag::Project(_),
            ..
        }
        | Stuck::Primitive(_)
        | Stuck::NonScalar(_)
        | Stuck::UndefinedConstant(_)
        | Stuck::CyclicConstant(_)
        | Stuck::Unended(_)
        | Stuck::Outside(_) => {
            panic!("no focused pure core term stops a run as: {stuck}")
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
/// - provides: an independent normalizer observation for the tiers.
/// - panics: on a readback refusal or an unsupported evaluation fault.
///
/// # Adequacy
/// - hypothesis: L2 — generated run readings, normalized, agree with the
///   independent normalization-by-evaluation path. L3 exact first-order and
///   suspended-body fixtures distinguish unperformed reductions, wrong binding
///   and collapsed refusal classes. Evidence is bounded to the pure fixtures
///   and their budget, not arbitrary open code.
/// - witness: `tests::differential::the_tiers_agree_with_normalisation_by_evaluation`
/// - witness: `tests::differential::first_order_returns_compare_exactly`
/// - witness: `tests::differential::thunks_compare_structurally_through_readback`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
/// - witness: `tests::differential::hand_built_declared_data_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
#[spec(requires: core.computation(root).is_some(), ensures: |ref ret| match *ret {
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
        Ok(head) => {
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
        Err(fault) => Answer::Stopped(normaliser_stop(fault)),
    }
}

/// The stop a normaliser's fault names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the common semantic stop for each wrong-head elimination and
///   unbound variable, without conflating the six classes; a non-injection and
///   an injection without an arm are the one structural stop, as a
///   non-constructor and a constructor without a branch are the one nominal
///   stop, and a projection of the wrong kind of value or of an absent field
///   the one projection stop.
/// - provides: the normalizer side of the shared refusal vocabulary.
/// - panics: for fuel, dangling-term, domain or machine-invariant faults, or a
///   non-returning bind outside the supported fixtures.
///
/// # Adequacy
/// - hypothesis: L3 — the malformed apply, force, case and nominal match
///   fixtures and the unbound variable name their exact semantic stop in both
///   evaluators. These distinguish exchanged error classes; internal faults and
///   resource failures are deliberately outside this mapping.
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::hand_built_declared_data_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
/// - witness: `tests::differential::hand_built_projection_cases_agree`
#[spec(ensures: |ret| match fault {
    | EvalFault::AppliedNonFunction => ret == Stop::AppliedNonFunction,
    | EvalFault::ForcedNonThunk => ret == Stop::ForcedNonThunk,
    | EvalFault::CasedNonInjection | EvalFault::UnknownSummand { .. } => ret == Stop::CasedNonInjection,
    | EvalFault::CasedNonConstructor | EvalFault::UnknownConstructor { .. } => ret == Stop::UnmatchedConstructor,
    | EvalFault::UnboundVariable { .. } => ret == Stop::UnboundVariable,
    | EvalFault::ProjectedNonRecord | EvalFault::AbsentRecordField | EvalFault::ProjectedNonTuple | EvalFault::AbsentTupleComponent => ret == Stop::UnprojectedField,
    | _ => false,
})]
fn normaliser_stop(fault: EvalFault) -> Stop
{
    match fault {
        EvalFault::AppliedNonFunction => Stop::AppliedNonFunction,
        EvalFault::ForcedNonThunk => Stop::ForcedNonThunk,
        EvalFault::CasedNonInjection | EvalFault::UnknownSummand { .. } => Stop::CasedNonInjection,
        EvalFault::CasedNonConstructor | EvalFault::UnknownConstructor { .. } => {
            Stop::UnmatchedConstructor
        },
        EvalFault::UnboundVariable { .. } => Stop::UnboundVariable,
        EvalFault::ProjectedNonRecord
        | EvalFault::AbsentRecordField
        | EvalFault::ProjectedNonTuple
        | EvalFault::AbsentTupleComponent => Stop::UnprojectedField,
        EvalFault::TransportedNonPath
        | EvalFault::TransportedUnderived
        | EvalFault::RodeUncomputed
        | EvalFault::SplitNonTuple
        | EvalFault::SplitArity
        | EvalFault::RuntimeControl(_)
        | EvalFault::FoldedNonList
        | EvalFault::NativePrimitive(_)
        | EvalFault::OutOfFuel
        | EvalFault::DanglingTerm
        | EvalFault::Domain(_)
        | EvalFault::BoundNonReturner
        | EvalFault::ReturnedNonReturner
        | EvalFault::AppliedNonOperator
        | EvalFault::SessionAction
        | EvalFault::MemoryForm
        | EvalFault::WorldForm
        | EvalFault::MachineInvariant => {
            panic!("no pure core term faults the normaliser as: {fault:?}")
        },
    }
}

/// A run's answer with its reading normalised: what a suspended body
/// comes to once the normaliser runs it.
///
/// # Specification
/// - requires: a term answer is in the normalizer helper's supported domain.
/// - ensures: a stopped answer remains the same stop; a term answer has its
///   reading normalized, with any resulting term resolving in its arena.
/// - provides: the common observation for suspended run readings.
/// - panics: on a normalization failure outside the helper's domain.
///
/// # Adequacy
/// - hypothesis: L2 — generated readings agree with independent normalization
///   after settling. L3 suspended-body examples distinguish a retained redex
///   from its normal form and preserve semantic stops. Only pure bounded
///   fixture readings are covered.
/// - witness: `tests::differential::the_tiers_agree_with_normalisation_by_evaluation`
/// - witness: `tests::differential::thunks_compare_structurally_through_readback`
/// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
/// - witness: `tests::differential::refusal_classes_do_not_collapse_into_success`
#[spec(ensures: |ref ret| match *answer {
    | Answer::Stopped(stop) => matches!(*ret, Answer::Stopped(found) if found == stop),
    | Answer::Term { .. } => match *ret {
        | Answer::Term { ref core, term } => core.computation(term).is_some(),
        | Answer::Stopped(_) => true,
    },
})]
fn settled(answer: &Answer) -> Answer
{
    match *answer {
        Answer::Term { ref core, term } => normalised(core, term),
        Answer::Stopped(stop) => Answer::Stopped(stop),
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
#[spec(ensures: |ret| match (left, right) {
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
        (
            &Answer::Term {
                core: ref left_core,
                term: left_term,
            },
            &Answer::Term {
                core: ref right_core,
                term: right_term,
            },
        ) => same_computation(left_core, left_term, right_core, right_term),
        (&Answer::Stopped(left_stop), &Answer::Stopped(right_stop)) if left_stop == right_stop => {
            Agreement::Same
        },
        (&Answer::Stopped(_), &Answer::Stopped(_) | &Answer::Term { .. })
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
/// - witness: `tests::differential::hand_built_declared_data_cases_agree`
/// - witness: `tests::differential::an_unbound_forced_name_is_still_stuck`
/// - witness: `tests::differential::hand_built_projection_cases_agree`
#[spec(requires: cases.iter().all(|case| case.core.computation(case.root).is_some()))]
fn assert_cases(cases: Vec<Case>)
{
    for case in cases {
        let Label(label) = case.label;
        let ran = on_tiers(&case.core, case.root);
        let normal = normalised(&case.core, case.root);
        match case.expected {
            Expected::Exactly => assert_eq!(
                Agreement::Same,
                agreement(&ran, &normal),
                "{label}: the run's reading is the normal form"
            ),
            Expected::Normalised => {
                assert_eq!(
                    Agreement::Differ,
                    agreement(&ran, &normal),
                    "{label}: the run's reading keeps a redex under a binder"
                );
                assert_eq!(
                    Agreement::Same,
                    agreement(&settled(&ran), &normal),
                    "{label}: the reading, normalised, is the normal form"
                );
            },
            Expected::Stops(stop) => {
                assert_eq!(
                    Agreement::Same,
                    agreement(&ran, &Answer::Stopped(stop)),
                    "{label}: the run stops at {stop:?}, not {ran:?}"
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

/// A first-order answer read back from a run is the normal form node
/// for node, and a different first-order answer is not.
#[test]
fn first_order_returns_compare_exactly()
{
    let bound = case(Label("a bound pair returned"), Expected::Exactly, |core| {
        let head = returning(core, |core| {
            let one = integer(core, Integer(1_i32));
            let unit = core.value_unit();
            let left = core.value_injection(Side::Left.into(), unit);
            core.value_tuple(&[one, left])
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
                let right = core.value_injection(Side::Right.into(), unit);
                core.value_tuple(&[one, right])
            })
        },
    );
    let ran = on_tiers(&bound.core, bound.root);
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
/// twice, β and a curried application, case on both injections and on a
/// third, and four ill-typed redexes that stop both evaluators at the same
/// elimination.
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
                core.value_tuple(&[first, second])
            })
        }),
        case(Label("return an injection"), Expected::Exactly, |core| {
            returning(core, |core| {
                let unit = core.value_unit();
                core.value_injection(Side::Left.into(), unit)
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
                core.value_tuple(&[earlier, later])
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
            let scrutinee = core.value_injection(Side::Left.into(), one);
            let on_left = returning(core, |core| variable(core, Index(0)));
            let on_right = returning(core, |core| integer(core, Integer(0_i32)));
            core.computation_case(scrutinee, &[on_left, on_right])
        }),
        case(Label("case on the right"), Expected::Exactly, |core| {
            let two = integer(core, Integer(2_i32));
            let scrutinee = core.value_injection(Side::Right.into(), two);
            let on_left = returning(core, |core| integer(core, Integer(0_i32)));
            let on_right = returning(core, |core| variable(core, Index(0)));
            core.computation_case(scrutinee, &[on_left, on_right])
        }),
        case(
            Label("case on a third summand of a triple"),
            Expected::Exactly,
            |core| {
                let one = integer(core, Integer(1_i32));
                let two = integer(core, Integer(2_i32));
                let three = integer(core, Integer(3_i32));
                let triple = core.value_tuple(&[one, two, three]);
                let scrutinee = core.value_injection(Summand::from(2_usize), triple);
                let on_first = returning(core, |core| integer(core, Integer(0_i32)));
                let on_second = returning(core, |core| integer(core, Integer(0_i32)));
                let on_third = returning(core, |core| variable(core, Index(0)));
                core.computation_case(scrutinee, &[on_first, on_second, on_third])
            },
        ),
        case(
            Label("a summand past the arms"),
            Expected::Stops(Stop::CasedNonInjection),
            |core| {
                let unit = core.value_unit();
                let scrutinee = core.value_injection(Summand::from(2_usize), unit);
                let on_left = returning(core, CoreArena::value_unit);
                let on_right = returning(core, CoreArena::value_unit);
                core.computation_case(scrutinee, &[on_left, on_right])
            },
        ),
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
                core.computation_case(one, &[on_left, on_right])
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
                core.value_tuple(&[outer, inner])
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

/// A datatype's declaration constant in a hand-built case.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Declaration(usize);

/// A constructor's ordinal in a hand-built case.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Ordinal(usize);

/// How many successors a numeral stacks on zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Successors(usize);

/// Nat: zero, and successor over one Nat.
const NAT: Declaration = Declaration(0);

/// List: nil, and cons over a head and a list.
const LIST: Declaration = Declaration(1);

/// Tree: a leaf, and a node over a function from Nat to Tree.
const TREE: Declaration = Declaration(2);

/// The constructor `ordinal` of the datatype declared at `declaration`,
/// over `fields`.
///
/// # Specification
/// trivial.
fn constructed(
    core: &mut CoreArena,
    declaration: Declaration,
    ordinal: Ordinal,
    fields: Vec<ValueId>,
) -> ValueId
{
    let datatype = core.value_type_data(ConstantIndex::from(declaration.0), Vec::new());
    core.value_constructor(datatype, ordinal.0.into(), fields)
}

/// The numeral with `count` successors on zero.
///
/// # Specification
/// trivial.
fn numeral(
    core: &mut CoreArena,
    count: Successors,
) -> ValueId
{
    let mut value = constructed(core, NAT, Ordinal(0), Vec::new());
    for _ in 0 .. count.0 {
        value = constructed(core, NAT, Ordinal(1), alloc::vec![value]);
    }
    value
}

/// `F Nat`, the motive of every hand-built match.
///
/// # Specification
/// trivial.
fn returns_nat(core: &mut CoreArena) -> CompTypeId
{
    let nat = core.value_type_data(ConstantIndex::from(NAT.0), Vec::new());
    core.comp_type_returner(nat)
}

/// `r ← head; return succ r`: one successor on what `head` returns, the
/// result bound under the binders `head` stands at.
///
/// # Specification
/// trivial.
fn successor_of(
    core: &mut CoreArena,
    head: ComputationId,
) -> ComputationId
{
    let rebuilt = returning(core, |core| {
        let result = variable(core, Index(0));
        constructed(core, NAT, Ordinal(1), alloc::vec![result])
    });
    core.computation_bind(head, rebuilt)
}

/// The structural fixpoint over `function`.
///
/// # Specification
/// trivial.
fn recursive(
    core: &mut CoreArena,
    function: ComputationId,
) -> ComputationId
{
    core.computation_fixpoint(function, FixpointEvidence::StructuralDescent)
}

/// Nominal matches select by ordinal and apply their fields in order;
/// recursive definitions over Nat, List and a Tree with a function field
/// compute the normaliser's answer through their own binding; a match on a
/// literal, an ordinal past the branches and the empty match stop both
/// evaluators at the nominal match.
#[test]
fn hand_built_declared_data_cases_agree()
{
    assert_cases(alloc::vec![
        case(
            Label("the first branch over its field"),
            Expected::Exactly,
            |core| {
                let seven = integer(core, Integer(7_i32));
                let scrutinee = constructed(core, NAT, Ordinal(0), alloc::vec![seven]);
                let own = returning(core, |core| variable(core, Index(0)));
                let first = core.computation_lambda(own);
                let zero = returning(core, |core| integer(core, Integer(0_i32)));
                let second = core.computation_lambda(zero);
                let motive = returns_nat(core);
                core.computation_data_case(scrutinee, motive, alloc::vec![first, second])
            },
        ),
        case(
            Label("a later branch by ordinal"),
            Expected::Exactly,
            |core| {
                let five = integer(core, Integer(5_i32));
                let scrutinee = constructed(core, NAT, Ordinal(1), alloc::vec![five]);
                let zero = returning(core, |core| integer(core, Integer(0_i32)));
                let first = core.computation_lambda(zero);
                let own = returning(core, |core| variable(core, Index(0)));
                let second = core.computation_lambda(own);
                let motive = returns_nat(core);
                core.computation_data_case(scrutinee, motive, alloc::vec![first, second])
            },
        ),
        case(
            Label("a fieldless branch runs as written"),
            Expected::Exactly,
            |core| {
                let scrutinee = constructed(core, NAT, Ordinal(0), Vec::new());
                let branch = returning(core, |core| integer(core, Integer(99_i32)));
                let motive = returns_nat(core);
                core.computation_data_case(scrutinee, motive, alloc::vec![branch])
            },
        ),
        case(
            Label("two fields applied in order"),
            Expected::Exactly,
            |core| {
                let one = integer(core, Integer(1_i32));
                let two = integer(core, Integer(2_i32));
                let scrutinee = constructed(core, LIST, Ordinal(1), alloc::vec![one, two]);
                let empty = returning(core, CoreArena::value_unit);
                let pair = returning(core, |core| {
                    let head = variable(core, Index(1));
                    let tail = variable(core, Index(0));
                    core.value_tuple(&[head, tail])
                });
                let inner = core.computation_lambda(pair);
                let cons = core.computation_lambda(inner);
                let motive = returns_nat(core);
                core.computation_data_case(scrutinee, motive, alloc::vec![empty, cons])
            },
        ),
        case(
            Label("evaluation continues after the match"),
            Expected::Exactly,
            |core| {
                let three = integer(core, Integer(3_i32));
                let scrutinee = constructed(core, NAT, Ordinal(0), alloc::vec![three]);
                let own = returning(core, |core| variable(core, Index(0)));
                let branch = core.computation_lambda(own);
                let motive = returns_nat(core);
                let matched = core.computation_data_case(scrutinee, motive, alloc::vec![branch]);
                let doubled = returning(core, |core| {
                    let bound = variable(core, Index(0));
                    core.value_tuple(&[bound, bound])
                });
                core.computation_bind(matched, doubled)
            },
        ),
        case(Label("a returned constructor"), Expected::Exactly, |core| {
            returning(core, |core| numeral(core, Successors(2)))
        },),
        case(Label("plus 2 1 by recursion"), Expected::Exactly, |core| {
            let base = returning(core, |core| variable(core, Index(0)));
            let recurse = {
                let own = variable(core, Index(3));
                let forced = core.computation_force(own);
                let predecessor = variable(core, Index(0));
                let once = core.computation_application(forced, predecessor);
                let addend = variable(core, Index(1));
                core.computation_application(once, addend)
            };
            let rebuilt = successor_of(core, recurse);
            let step = core.computation_lambda(rebuilt);
            let augend = variable(core, Index(1));
            let motive = returns_nat(core);
            let matched = core.computation_data_case(augend, motive, alloc::vec![base, step]);
            let inner = core.computation_lambda(matched);
            let function = core.computation_lambda(inner);
            let plus = recursive(core, function);
            let two = numeral(core, Successors(2));
            let one = numeral(core, Successors(1));
            let once = core.computation_application(plus, two);
            core.computation_application(once, one)
        }),
        case(
            Label("the length of a three-element list"),
            Expected::Exactly,
            |core| {
                let base = returning(core, |core| numeral(core, Successors(0)));
                let recurse = {
                    let own = variable(core, Index(3));
                    let forced = core.computation_force(own);
                    let tail = variable(core, Index(0));
                    core.computation_application(forced, tail)
                };
                let rebuilt = successor_of(core, recurse);
                let inner = core.computation_lambda(rebuilt);
                let step = core.computation_lambda(inner);
                let list = variable(core, Index(0));
                let motive = returns_nat(core);
                let matched = core.computation_data_case(list, motive, alloc::vec![base, step]);
                let function = core.computation_lambda(matched);
                let length = recursive(core, function);
                let mut list = constructed(core, LIST, Ordinal(0), Vec::new());
                for _ in 0_u8 .. 3_u8 {
                    let head = core.value_unit();
                    list = constructed(core, LIST, Ordinal(1), alloc::vec![head, list]);
                }
                core.computation_application(length, list)
            },
        ),
        case(
            Label("the size of a tree through its function field"),
            Expected::Exactly,
            |core| {
                let base = returning(core, |core| numeral(core, Successors(0)));
                let branch = {
                    let field = variable(core, Index(0));
                    let forced = core.computation_force(field);
                    let zero = numeral(core, Successors(0));
                    core.computation_application(forced, zero)
                };
                let recurse = {
                    let own = variable(core, Index(3));
                    let forced = core.computation_force(own);
                    let subtree = variable(core, Index(0));
                    core.computation_application(forced, subtree)
                };
                let rebuilt = successor_of(core, recurse);
                let descended = core.computation_bind(branch, rebuilt);
                let step = core.computation_lambda(descended);
                let tree = variable(core, Index(0));
                let motive = returns_nat(core);
                let matched = core.computation_data_case(tree, motive, alloc::vec![base, step]);
                let function = core.computation_lambda(matched);
                let size = recursive(core, function);
                let mut tree = constructed(core, TREE, Ordinal(0), Vec::new());
                for _ in 0_u8 .. 2_u8 {
                    let below = core.computation_return(tree);
                    let ignoring = core.computation_lambda(below);
                    let children = core.value_thunk(ignoring);
                    tree = constructed(core, TREE, Ordinal(1), alloc::vec![children]);
                }
                core.computation_application(size, tree)
            },
        ),
        case(
            Label("a recursive thunk returned unforced"),
            Expected::Exactly,
            |core| {
                let own = returning(core, |core| variable(core, Index(0)));
                let function = core.computation_lambda(own);
                let identity = recursive(core, function);
                returning(core, |core| core.value_thunk(identity))
            },
        ),
        case(
            Label("a match on a literal"),
            Expected::Stops(Stop::UnmatchedConstructor),
            |core| {
                let one = integer(core, Integer(1_i32));
                let own = returning(core, |core| variable(core, Index(0)));
                let branch = core.computation_lambda(own);
                let motive = returns_nat(core);
                core.computation_data_case(one, motive, alloc::vec![branch])
            },
        ),
        case(
            Label("an ordinal past the branches"),
            Expected::Stops(Stop::UnmatchedConstructor),
            |core| {
                let scrutinee = constructed(core, LIST, Ordinal(2), Vec::new());
                let first = returning(core, CoreArena::value_unit);
                let second = returning(core, CoreArena::value_unit);
                let motive = returns_nat(core);
                core.computation_data_case(scrutinee, motive, alloc::vec![first, second])
            },
        ),
        case(
            Label("the empty match"),
            Expected::Stops(Stop::UnmatchedConstructor),
            |core| {
                let scrutinee = constructed(core, NAT, Ordinal(0), Vec::new());
                let motive = returns_nat(core);
                core.computation_data_case(scrutinee, motive, Vec::new())
            },
        ),
    ]);
}

/// A forced variable no binding answers stops both evaluators: the tiers
/// decline it as unbound before they run, the normaliser stops at it.
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

/// A projection delivers the field it names, whatever the width of the value
/// and the place of the field in it, and the run's reading is the normal
/// form; projecting past the width, an absent label, or the wrong kind of value
/// stops both evaluators at the one projection stop.
#[test]
fn hand_built_projection_cases_agree()
{
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let quadruple = |core: &mut CoreArena| {
        let fields = [0_i32, 1_i32, 2_i32, 3_i32].map(|digit| integer(core, Integer(digit)));
        core.value_tuple(&fields)
    };
    let record = |core: &mut CoreArena, names: [&str; 3]| {
        let fields = names
            .iter()
            .zip([10_i32, 20_i32, 30_i32])
            .map(|(&name, digit)| (label(name), integer(core, Integer(digit))))
            .collect();
        core.value_record(fields)
    };
    assert_cases(alloc::vec![
        case(
            Label("a quadruple's third component"),
            Expected::Exactly,
            |core| {
                let tuple = quadruple(core);
                core.computation_tuple_projection(tuple, 2_usize.into())
            }
        ),
        case(
            Label("a label second of three"),
            Expected::Exactly,
            |core| {
                let fields = record(core, ["a", "s", "z"]);
                core.computation_record_projection(fields, label("s"))
            }
        ),
        case(
            Label("the same label last of three"),
            Expected::Exactly,
            |core| {
                let fields = record(core, ["a", "b", "s"]);
                core.computation_record_projection(fields, label("s"))
            }
        ),
        case(
            Label("a projected field bound and paired"),
            Expected::Exactly,
            |core| {
                let fields = record(core, ["a", "s", "z"]);
                let projected = core.computation_record_projection(fields, label("z"));
                let body = returning(core, |core| {
                    let bound = variable(core, Index(0));
                    let one = integer(core, Integer(1_i32));
                    core.value_tuple(&[bound, one])
                });
                core.computation_bind(projected, body)
            }
        ),
        case(
            Label("a record returned whole"),
            Expected::Exactly,
            |core| { returning(core, |core| record(core, ["c", "a", "b"])) }
        ),
        case(
            Label("a component past the width"),
            Expected::Stops(Stop::UnprojectedField),
            |core| {
                let tuple = quadruple(core);
                core.computation_tuple_projection(tuple, 4_usize.into())
            },
        ),
        case(
            Label("an absent label"),
            Expected::Stops(Stop::UnprojectedField),
            |core| {
                let fields = record(core, ["a", "s", "z"]);
                core.computation_record_projection(fields, label("b"))
            },
        ),
        case(
            Label("a label of a tuple"),
            Expected::Stops(Stop::UnprojectedField),
            |core| {
                let tuple = quadruple(core);
                core.computation_record_projection(tuple, label("s"))
            },
        ),
        case(
            Label("a component of a record"),
            Expected::Stops(Stop::UnprojectedField),
            |core| {
                let fields = record(core, ["a", "s", "z"]);
                core.computation_tuple_projection(fields, 0_usize.into())
            },
        ),
    ]);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    /// Every generated closed, well-typed computation halts within the
    /// budget, and two runs of it read back as the same term.
    #[test]
    fn the_tiers_are_total_and_deterministic(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let first = on_tiers(&generated.core, root);
        let second = on_tiers(&generated.core, root);
        prop_assert!(matches!(first, Answer::Term { .. }), "a closed, well-typed computation stopped: {:?}", first);
        prop_assert_eq!(Agreement::Same, agreement(&first, &second), "two runs read back apart");
    }

    /// The tiers' reading of every generated closed, well-typed
    /// computation, normalised, is the normaliser's normal form of it.
    #[test]
    fn the_tiers_agree_with_normalisation_by_evaluation(generated in computations())
    {
        let GeneratedRoot::Computation(root) = generated.root else {
            return Err(TestCaseError::fail("the strategy yields computations"));
        };
        let ran = on_tiers(&generated.core, root);
        let normal = normalised(&generated.core, root);
        prop_assert_eq!(
            Agreement::Same,
            agreement(&settled(&ran), &normal),
            "the tiers read back {:?} against the normal form {:?}", ran, normal
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
    let value_answer = on_tiers(&core, returned);
    let forced_answer = on_tiers(&core, forced);
    let applied_answer = on_tiers(&core, applied);
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
