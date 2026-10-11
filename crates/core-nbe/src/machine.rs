//! The **conversion machine**: step 4 of the pipeline, the lazy concurrent
//! convertibility search of Courant and Leroy (POPL 2026) transcribed over the
//! glued domain as `⟨P, W, Q⟩` — a flat process arena, a wait map, and a
//! duplicate-free run queue.
//!
//! # Processes, channels, and the run queue
//!
//! A **goal** compares two weak heads; a **channel** evaluates one weak head
//! that goals demand. Both are entries of one flat arena addressed by
//! [`ProcessId`], and neither holds a reference to another: a goal names the
//! channels and children it waits on by id, and each process lists the ids
//! waiting on it — the wait map. The run queue holds each runnable process at
//! most once, guarded by a membership vector beside the arena. One turn of the
//! loop runs one process one step: a goal applies one rule, a channel runs one
//! slice of its evaluation. Nothing recurses, so the machine is total on any
//! depth of term and any length of search.
//!
//! # Demand
//!
//! A process runs only while something needs it. The root is needed by the
//! caller; a goal needs the channels and children it waits on. When a
//! combinator answers early — a biased choice whose authoritative branch
//! answered, a decomposition refuted at one subgoal — the processes it no
//! longer waits on lose that demand, and a process left with none stops being
//! scheduled. Demand propagates through an explicit worklist in both
//! directions, so a dormant subtree wakes intact if it is needed again.
//!
//! # Channels are minted from the subterm table
//!
//! Under the default granularity stance a run mints **one evaluation channel
//! per distinct definition body**, keyed by the body's subterm-table entry
//! index in a dense side vector: two unfoldings of one body — of one
//! definition or of two that the table gave one body — share one evaluation.
//! An unfolding of a neutral re-applies its spine to that shared body on a
//! channel of its own, kept per neutral; opening a closure under a fresh
//! variable and entering a thunk are channels kept per closure. Fresh variables
//! are minted once per binder level, so two goals opening binders at one depth
//! read one variable.
//!
//! # Frozen constants and biased choice
//!
//! Comparing two defined heads starts the alternatives the rule table names as
//! concurrent goals and combines them as it says. In the branch that unfolds
//! the right side the left constant is **frozen** — it may no longer unfold
//! there — so each further unfolding of it happens in one branch only. A
//! frozen branch may refute two convertible terms, so its refutation is not
//! authoritative: the biased combinator takes a convertible answer from any
//! branch and otherwise waits for the last, authoritative one.
//!
//! # The trace
//!
//! A recording sink receives the winning derivation in preorder once the root
//! answers; the null sink receives nothing and the run keeps no derivation, so
//! sink-off conversion is the same function at a different type parameter.
//!
//! # Re-sharing
//!
//! Every goal the machine starts fresh — the root and each premise of a
//! decomposition — is looked up in the run's check memo first, and a hit hands
//! back the process already comparing that pair; the key and the support
//! edges each entry records are the `resharing` module's. The null memo starts
//! every goal afresh, so the memoless machine is the same function at a
//! different type parameter, and the two are compared verdict for verdict.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::mem;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionHeight;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::MemoActivity;
use gandr_kernel_check_memo::MemoRecord;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_conversion_trace::SinkActivity;
use gandr_kernel_conversion_trace::SubgoalPosition;
use gandr_kernel_conversion_trace::TraceSink;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::GlobalIndex;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::conv::ConversionFault;
use crate::conv::Settlement;
use crate::conv::convert_computations;
use crate::conv::convert_values;
use crate::derivation::DerivationCount;
use crate::derivation::Derivations;
use crate::domain::BinderLevel;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::Glued;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::Bound;
use crate::eval::Definitions;
use crate::eval::EvalFault;
use crate::eval::Evaluation;
use crate::eval::Fuel;
use crate::eval::Progress;
use crate::eval::extend_spine;
use crate::policy::GranularityPolicy;
use crate::policy::GranularityStance;
use crate::policy::SchedulingPolicy;
use crate::policy::Share;
use crate::resharing::GoalSupport;
use crate::resharing::SupportEdges;
use crate::resharing::SupportSides;
use crate::resharing::Supports;
use crate::rules::Choice;
use crate::rules::Combination;
use crate::rules::Frozen;
use crate::rules::Move;
use crate::rules::Plan;
use crate::rules::Settled;
use crate::rules::Spines;
use crate::rules::Step;
use crate::rules::Subgoal;
use crate::rules::other;
use crate::rules::plan;
use crate::rules::spine_subgoals;

/// The evaluation steps a channel runs per turn.
///
/// Small enough that a long evaluation yields to the comparisons waiting
/// beside it, large enough that a short one finishes in one turn.
const SLICE: u32 = 64_u32;

/// The node a trace decision names, in this crate's value space.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TraceNode
{
    /// A definition, by its admission position.
    Constant(ConstantIndex),
    /// A domain value.
    Value(DomainValueId),
    /// A weak-head domain computation.
    Computation(DomainCompId),
}

impl TraceNode
{
    /// The node a glued weak head names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn of(glued: Glued) -> Self
    {
        match glued {
            | Glued::Value(value) => Self::Value(value),
            | Glued::Computation(comp) => Self::Computation(comp),
        }
    }
}

/// What the machine is asked: two weak heads of one polarity, beneath the
/// binders the caller has already opened.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Problem
{
    /// The left side.
    left: Glued,
    /// The right side.
    right: Glued,
    /// The first binder level neither side mentions: where the machine's own
    /// fresh variables start.
    depth: BinderLevel,
}

impl Problem
{
    /// Two closed values.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn values(
        left: DomainValueId,
        right: DomainValueId,
    ) -> Self
    {
        Self {
            left: Glued::Value(left),
            right: Glued::Value(right),
            depth: BinderLevel::FLOOR,
        }
    }

    /// Two closed weak-head computations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn computations(
        left: DomainCompId,
        right: DomainCompId,
    ) -> Self
    {
        Self {
            left: Glued::Computation(left),
            right: Glued::Computation(right),
            depth: BinderLevel::FLOOR,
        }
    }

    /// The same problem beneath `depth` intuitionistic binders the caller has
    /// opened, so the machine's fresh variables start past every level the
    /// sides mention.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn under(
        self,
        depth: BinderLevel,
    ) -> Self
    {
        Self { depth, ..self }
    }
}

/// How many rule instances and evaluation steps a run may spend before it
/// declines.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StepBudget(u64);

impl StepBudget
{
    /// The budget a run takes when the caller names none: about a million
    /// steps, far past any comparison a finite derivation of ordinary size
    /// needs and small enough that a diverging one declines in well under a
    /// second.
    pub const DEFAULT: Self = Self(1_u64 << 20_u32);
}

impl Default for StepBudget
{
    /// [`StepBudget::DEFAULT`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::DEFAULT
    }
}

impl From<u64> for StepBudget
{
    /// A budget of `steps`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: u64) -> Self
    {
        Self(steps)
    }
}

impl From<StepBudget> for u64
{
    /// The steps `budget` allows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: StepBudget) -> Self
    {
        budget.0
    }
}

/// The parameters a conversion run is written against.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MachineSettings
{
    /// How the run queue divides its attention.
    scheduling: SchedulingPolicy,
    /// How finely evaluations are shared.
    granularity: GranularityPolicy,
    /// How much the run may spend before it declines.
    budget: StepBudget,
}

impl MachineSettings
{
    /// Settings over the two policies and the budget.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        scheduling: SchedulingPolicy,
        granularity: GranularityPolicy,
        budget: StepBudget,
    ) -> Self
    {
        Self {
            scheduling,
            granularity,
            budget,
        }
    }

    /// The scheduling policy.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scheduling(&self) -> SchedulingPolicy
    {
        self.scheduling
    }

    /// The granularity policy.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn granularity(&self) -> GranularityPolicy
    {
        self.granularity
    }

    /// The step budget.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn budget(&self) -> StepBudget
    {
        self.budget
    }
}

/// Why a run answered neither way.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DeclineReason
{
    /// A goal was about to unfold a neutral it had already unfolded on its
    /// own chain — the same definition over the same spine — or the run's
    /// needed goals all wait on one another through a re-shared goal.
    Cycle,
    /// The run spent its step budget.
    Budget,
    /// Two codes or two static lambdas are not α-equal and one of them holds
    /// something that could still unfold, or a static lambda meets a stuck
    /// operator that η could relate it to: telling them apart needs reduction
    /// or expansion inside a type, which this rung does not perform.
    UndecidedCodes,
}

/// What the machine found.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MachineVerdict
{
    /// A derivation of convertibility was found.
    Convertible,
    /// An authoritative derivation of non-convertibility was found.
    NotConvertible,
    /// Neither was found: a decline, never a verdict on the terms.
    Declined(DeclineReason),
}

/// How many rule instances and evaluation steps a run spent.
///
/// Reports saturate at the representable ceiling; overflow still exhausts a
/// pending run's budget.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StepCount(u64);

impl StepCount
{
    /// One step: what a table read or a move charges.
    const ONE: Self = Self(1_u64);
}

impl From<StepCount> for u64
{
    /// How many steps `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: StepCount) -> Self
    {
        count.0
    }
}

/// How many processes a run started.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProcessCount(usize);

impl From<ProcessCount> for usize
{
    /// How many processes `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ProcessCount) -> Self
    {
        count.0
    }
}

/// What one run reports.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MachineReport
{
    /// The answer.
    verdict: MachineVerdict,
    /// How many processes the run started; zero when the search-free steps
    /// answered at the root.
    processes: ProcessCount,
    /// How many derivations the run kept; zero for the null sink.
    derivations: DerivationCount,
    /// How many rule instances and evaluation steps the run spent.
    steps: StepCount,
    /// The support edges the run's memo entries hold; zero for the null memo.
    edges: SupportEdges,
}

impl MachineReport
{
    /// The answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> MachineVerdict
    {
        self.verdict
    }

    /// How many processes the run started.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn processes(&self) -> ProcessCount
    {
        self.processes
    }

    /// How many derivations the run kept.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn derivations(&self) -> DerivationCount
    {
        self.derivations
    }

    /// How many rule instances and evaluation steps the run spent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn steps(&self) -> StepCount
    {
        self.steps
    }

    /// The support edges the run's memo entries hold, by verdict.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn edges(&self) -> SupportEdges
    {
        self.edges
    }
}

/// Decide whether the two sides of `problem` are convertible, re-sharing goals
/// through a fresh memo of type `M`.
///
/// # Specification
/// - requires: both sides were evaluated in this run under `definitions` and
///   mention no intuitionistic binder level at or past `problem`'s depth;
///   `core` holds their literal payloads and every lowered body.
/// - ensures: the search-free steps answer first — an identical or structurally
///   equal pair is convertible and a guard-separated pair is not, with no
///   process started; otherwise the machine runs its goals and channels fairly
///   until the root answers or the run spends its budget, and the verdict is
///   that answer: a convertible verdict rests on a derivation through the rule
///   table, a refutation on an authoritative one, and a decline on neither. A
///   goal about to unfold a neutral already unfolded on its own chain declines
///   with [`DeclineReason::Cycle`], and so does a run whose needed goals all
///   wait on one another through a re-shared goal; a run past its budget
///   declines with [`DeclineReason::Budget`]. Every goal started fresh — the
///   root and each premise of a decomposition — is first recalled from a memo
///   built for this run alone, and a hit waits on the process already comparing
///   the same sides at the same level; the report counts the support edges the
///   memo's entries hold, zero for the null memo. A recording `sink` receives
///   the winning derivation in preorder — the trace the kernel's sequential
///   replay re-derives the verdict from — and nothing for a decline; the null
///   sink receives nothing, and the report counts zero derivations kept.
/// - provides: step 4 of the conversion pipeline: the search the first three
///   steps defer to.
/// - fails: [`ConversionFault::Polarity`] for a value against a computation
///   anywhere in the search, [`ConversionFault::Evaluation`] when an evaluation
///   a goal demanded is refused, [`ConversionFault::Domain`] and
///   [`ConversionFault::LiteralPayload`] for nodes that do not resolve,
///   [`ConversionFault::Memo`] when the memo refuses to record, and
///   [`ConversionFault::MachineInvariant`] if the machine's bookkeeping
///   disagrees with itself or another binder exceeds the representable level.
/// - panics: none.
/// - intension: one rule per goal turn and one evaluation slice per channel
///   turn, round-robin over the run queue under the default scheduling stance.
///
/// # Errors
/// Every variant of [`ConversionFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the root fast path, the
///   machine's rule arms, its three declines and the memo's hit; each rule arm
///   is separated by a conversion answered through it, both verdicts and all
///   three declines are exercised, recording is pinned against the null sink
///   and the live memo against the null memo verdict for verdict, and
///   re-sharing is pinned by exact process and edge counts. Every recorded
///   derivation is replayed by the kernel to the same verdict, a tampered one
///   is refused, and a decline under a starving schedule stays a decline
///   through the kernel.
/// - witness: `machine::tests::the_search_free_steps_answer_before_any_process`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
/// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
/// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
/// - witness: `machine::tests::recording_does_not_move_the_verdict`
/// - witness: `machine::tests::the_sink_off_run_keeps_no_derivation`
/// - witness: `machine::tests::the_memo_never_moves_a_verdict`
/// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
/// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
/// - witness: `machine::tests::codes_that_could_unfold_inside_are_declined`
/// - witness: `machine::tests::invalid_roots_refuse_before_identity_or_search`
/// - witness: `machine::tests::binder_ceiling_is_refused_before_opening_or_eta_allocation`
/// - witness: `machine::tests::step_counter_overflow_cannot_disable_the_budget_backstop`
/// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
#[inline]
#[spec(
    ensures: |ret| (ret.as_ref().is_ok_and(|report| {
        usize::from(report.derivations) == if matches!(S::ACTIVITY, SinkActivity::Active) {
            report.processes.0
        } else { 0 }
            && (matches!(M::ACTIVITY, MemoActivity::Active)
                || report.edges == SupportEdges::default())
            && (report.processes.0 != 0
                || (report.steps.0 == 0
                    && !matches!(report.verdict, MachineVerdict::Declined(_))))
    }) || ret.is_err())
        && (match (problem.left, problem.right) {
        (Glued::Value(_), Glued::Computation(_))
        | (Glued::Computation(_), Glued::Value(_)) => ret == Err(ConversionFault::Polarity),
        _ => true,
    })
)]
pub fn decide<S, M>(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    settings: MachineSettings,
    problem: Problem,
    sink: &mut S,
) -> Result<MachineReport, ConversionFault>
where
    S: TraceSink<TraceNode>,
    M: CheckMemo<GoalSupport, ProcessId> + Default,
{
    let settlement = settle_root(core, domain, problem)?;
    let early = match settlement {
        | Settlement::Identical | Settlement::StructurallyEqual => {
            RootFastPath::Answered(MachineVerdict::Convertible)
        },
        | Settlement::GuardedApart => RootFastPath::Answered(MachineVerdict::NotConvertible),
        | Settlement::StructurallyApart | Settlement::Deferred(_) => RootFastPath::Search,
    };
    if let RootFastPath::Answered(verdict) = early {
        if matches!(S::ACTIVITY, SinkActivity::Active) {
            sink.record(ConversionDecision::ComparedShared {
                left: TraceNode::of(problem.left),
                right: TraceNode::of(problem.right),
            });
        }
        return Ok(MachineReport {
            verdict,
            processes: ProcessCount::default(),
            derivations: DerivationCount::default(),
            steps: StepCount::default(),
            edges: SupportEdges::default(),
        });
    }
    let mut scheduler = Scheduler::new(
        core,
        domain,
        definitions,
        settings,
        S::ACTIVITY,
        M::default(),
    );
    let root = scheduler.start_fresh(
        SupportSides::Heads(problem.left, problem.right),
        problem.depth,
    )?;
    let verdict = scheduler.run(root)?;
    if matches!(
        verdict,
        MachineVerdict::Convertible | MachineVerdict::NotConvertible
    ) {
        scheduler
            .derivations
            .emit(scheduler.core, scheduler.domain, root, sink)?;
    }
    Ok(MachineReport {
        verdict,
        processes: ProcessCount(scheduler.processes.len()),
        derivations: scheduler.derivations.count(),
        steps: scheduler.spent,
        edges: scheduler.supports.totals(),
    })
}

/// Whether the search-free steps answered at the root.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum RootFastPath
{
    /// They answered.
    Answered(MachineVerdict),
    /// They deferred, or found a separation whose derivation the search must
    /// produce.
    Search,
}

/// Steps 1 through 3 at the root.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the settlement the search-free steps give the problem's pair.
/// - provides: the fast path ahead of the machine.
/// - fails: [`ConversionFault::Polarity`] for two polarities, and whatever the
///   steps refuse.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Polarity`] — a value met a computation.
/// - [`ConversionFault`] — as the steps refuse.
///
/// # Adequacy
/// - hypothesis: L3 — over evaluated root pairs, the observer is the verdict
///   and zero-process fast path; shared identity, equal distinct units and
///   guard-separated shapes distinguish wrong identity, polarity dispatch and
///   an unnecessary search. Missing domain roots remain checked refusals rather
///   than identity successes.
/// - witness: `machine::tests::the_search_free_steps_answer_before_any_process`
/// - witness: `machine::tests::invalid_roots_refuse_before_identity_or_search`
#[spec(
    ensures: |ret| match (problem.left, problem.right) {
        (Glued::Value(left), Glued::Value(right)) => {
            if domain.value(left).is_none() || domain.value(right).is_none() {
                ret == Err(ConversionFault::Domain(DomainFault::Dangling))
            } else { left != right || ret.is_err() || ret == Ok(Settlement::Identical) }
        }
        (Glued::Computation(left), Glued::Computation(right)) => {
            if domain.computation(left).is_none() || domain.computation(right).is_none() {
                ret == Err(ConversionFault::Domain(DomainFault::Dangling))
            } else { left != right || ret.is_err() || ret == Ok(Settlement::Identical) }
        }
        _ => ret == Err(ConversionFault::Polarity),
    }
)]
fn settle_root(
    core: &CoreArena,
    domain: &DomainArena,
    problem: Problem,
) -> Result<Settlement, ConversionFault>
{
    match (problem.left, problem.right) {
        | (Glued::Value(left), Glued::Value(right)) => convert_values(core, domain, left, right),
        | (Glued::Computation(left), Glued::Computation(right)) => {
            convert_computations(core, domain, left, right)
        },
        | (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_)) => {
            Err(ConversionFault::Polarity)
        },
    }
}

/// The id of one process in a run's arena: meaningful in that run alone, which
/// is why the re-sharing memo that records it lives for one run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProcessId(usize);

impl From<ProcessId> for usize
{
    /// The arena offset the id names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: ProcessId) -> Self
    {
        id.0
    }
}

/// One side of a goal: a weak head in hand, or the channel that will give it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Slot
{
    /// The weak head.
    Ready(Glued),
    /// The channel evaluating it.
    Waiting(ProcessId),
}

/// What a goal does on its next turn.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Next
{
    /// Read the rule table.
    Classify,
    /// Take this alternative's first move.
    Move(Move),
    /// Read its children's answers.
    Combine(Combine),
}

/// How a goal's children combine into its answer.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Combine
{
    /// A decomposition: every child must agree; one refutation refutes.
    All
    {
        /// The pair decomposed.
        pair: (Glued, Glued),
        /// The children, in subgoal order.
        children: Vec<ProcessId>,
        /// Whether the emission may close the pair in one step.
        collapse: Collapse,
    },
    /// A biased choice: any convertible answer wins; otherwise the last child
    /// decides.
    Biased(Vec<ProcessId>),
    /// Either: any convertible answer wins; every child must refute.
    Either(Vec<ProcessId>),
}

/// Whether an agreeing decomposition may be emitted as one closing decision.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Collapse
{
    /// The decomposition is a structural rule a replay applies silently, so a
    /// pair the search-free steps settle may close in one step.
    Allowed,
    /// The decomposition followed a recorded decision that names it, so its
    /// children's derivations are emitted as they are.
    Never,
}

/// A goal: two sides and what it does next.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Goal
{
    /// The left side.
    left: Slot,
    /// The right side.
    right: Slot,
    /// The first binder level neither side mentions.
    depth: BinderLevel,
    /// The constants frozen on each side.
    frozen: Frozen,
    /// What each side has unfolded since the goal's last decomposition.
    chain: Chain,
    /// The next step.
    next: Next,
}

/// One unfolding on a goal's chain: a definition over a spine.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Unfolded
{
    /// The definition unfolded.
    constant: ConstantIndex,
    /// The spine it was unfolded under, by the ids its eliminations name.
    spine: Vec<Elimination>,
}

/// What each side of a goal has unfolded since the goal's last
/// decomposition, inherited by every alternative a choice starts and dropped
/// by every decomposition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Chain
{
    /// Unfolded on the left.
    left: Vec<Unfolded>,
    /// Unfolded on the right.
    right: Vec<Unfolded>,
}

/// Whether an unfolding repeats one already on its side's chain.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Repeat
{
    /// It does not, and the chain now holds it.
    Fresh,
    /// It does: unfolding again would only return to this point.
    Repeated,
}

impl Chain
{
    /// Add `unfolded` to `side`'s chain unless the chain holds it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Repeat::Repeated`] and no change when `side`'s chain holds
    ///   an equal unfolding; [`Repeat::Fresh`] with `unfolded` appended
    ///   otherwise.
    /// - provides: the cycle key: a definition over a spine compared by the ids
    ///   its eliminations name, so one function unfolded twice at different
    ///   arguments is no cycle, while a definition that unfolds back to itself
    ///   over the same arguments is.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the boundary is an unfolding repeated on one side
    ///   versus the same function under different argument spines. The verdict
    ///   and emitted unfoldings separate omitted cycle detection, a
    ///   constant-only key and a chain shared between sides; the predicate also
    ///   checks append direction and retained spine endpoints.
    /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
    /// - witness: `machine::tests::unfolding_one_function_twice_is_not_a_cycle`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
        captures: [left = self.left.len(), right = self.right.len(), constant = unfolded.constant, length = unfolded.spine.len(), first = unfolded.spine.first().copied(), last = unfolded.spine.last().copied()],
        ensures: |ret| {
            let (selected, old, untouched, other) = match side {
                ConversionSide::Left => (&self.left, left, self.right.len(), right),
                ConversionSide::Right => (&self.right, right, self.left.len(), left),
            };
            untouched == other && match ret {
                Repeat::Repeated => selected.len() == old,
                Repeat::Fresh => selected.len() == old.saturating_add(1)
                    && selected.last().is_some_and(|entry| entry.constant == constant
                        && entry.spine.len() == length
                        && entry.spine.first().copied() == first
                        && entry.spine.last().copied() == last),
            }
        }
    )]
    fn enter(
        &mut self,
        side: ConversionSide,
        unfolded: Unfolded,
    ) -> Repeat
    {
        let held = match side {
            | ConversionSide::Left => &mut self.left,
            | ConversionSide::Right => &mut self.right,
        };
        if held.contains(&unfolded) {
            return Repeat::Repeated;
        }
        held.push(unfolded);
        Repeat::Fresh
    }
}

/// Whether an unfolding step went ahead.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Advance
{
    /// The side now waits on the unfolding.
    Unfolding,
    /// The unfolding repeats one on the side's chain, so the goal declines.
    Cycle,
}

/// A channel: one evaluation goals demand.
enum Channel<'run>
{
    /// Waiting for a definition body, to re-apply a neutral's spine to it.
    Reapply
    {
        /// The body's channel.
        body: ProcessId,
        /// The neutral whose spine is re-applied.
        neutral: NeutralId,
    },
    /// Running an evaluation slice by slice.
    Running(Evaluation<'run>),
}

/// What a process is.
enum Work<'run>
{
    /// A comparison.
    Goal(Goal),
    /// An evaluation.
    Channel(Channel<'run>),
    /// Nothing left to do: the process answered.
    Spent,
}

/// What a process has produced.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Outcome
{
    /// Nothing yet.
    Pending,
    /// A goal's answer.
    Settled(Settled),
    /// A goal's decline.
    Declined(DeclineReason),
    /// A channel's weak head.
    Evaluated(Glued),
}

/// Whether a process sits in the run queue.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Queued
{
    /// It does.
    Present,
    /// It does not.
    Absent,
}

/// How many needs a process has outstanding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Demand(u32);

/// How many turns a process has been passed over since it last ran.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Credit(u32);

/// One entry of the process arena.
struct Process<'run>
{
    /// What it does.
    work: Work<'run>,
    /// What it has produced.
    outcome: Outcome,
    /// How many processes, or the caller, need it.
    demand: Demand,
    /// The processes it waits on.
    deps: Vec<ProcessId>,
    /// The processes waiting on it: its row of the wait map.
    waiters: Vec<ProcessId>,
    /// Turns passed over since it last ran.
    credit: Credit,
    /// Its share of the scheduler's attention.
    share: Share,
}

/// What one turn left a process as.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Turn
{
    /// Runnable again at once.
    Again,
    /// Waiting on a process that has not answered.
    Wait,
    /// Answered.
    Done,
}

/// Whether a definition body's channel has been minted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum BodyChannel
{
    /// Not yet.
    Unminted,
    /// It has, as this process.
    Minted(ProcessId),
}

/// One run of the machine: `⟨P, W, Q⟩`, the channel tables and the re-sharing
/// memo.
struct Scheduler<'run, M>
{
    /// The core arena literal payloads and lowered bodies live in.
    core: &'run CoreArena,
    /// The domain both sides live in, and every channel mints into.
    domain: &'run mut DomainArena,
    /// What may unfold, and where from.
    definitions: Definitions<'run>,
    /// The run's parameters.
    settings: MachineSettings,
    /// The process arena, `P`; each process's waiters are `W`.
    processes: Vec<Process<'run>>,
    /// The run queue, `Q`.
    queue: VecDeque<ProcessId>,
    /// Which processes `Q` holds, by id.
    queued: Vec<Queued>,
    /// One channel per distinct body entry, by entry index.
    bodies: Vec<BodyChannel>,
    /// One unfolding channel per neutral.
    unfoldings: BTreeMap<NeutralId, ProcessId>,
    /// One opening channel per closure and binder level.
    openings: BTreeMap<(CompClosureId, BinderLevel), ProcessId>,
    /// One entering channel per closure.
    entries: BTreeMap<CompClosureId, ProcessId>,
    /// One fresh variable per binder level, from the floor.
    variables: Vec<DomainValueId>,
    /// The derivations, kept only when recording.
    derivations: Derivations,
    /// The goals started fresh, by support; this run's alone.
    memo: M,
    /// The support edges, kept only while the memo is active.
    supports: Supports,
    /// The rule instances and evaluation steps spent so far.
    spent: StepCount,
    /// Whether the charged count exceeded its representable ceiling.
    spent_overflowed: bool,
}

impl<'run, M> Scheduler<'run, M>
where
    M: CheckMemo<GoalSupport, ProcessId>,
{
    /// An empty run over an empty `memo`.
    ///
    /// # Specification
    /// - requires: `memo` is empty and belongs to this run.
    /// - ensures: every process, queue, channel cache and variable cache starts
    ///   empty; no steps, derivations or support edges have been recorded, and
    ///   the run retains its supplied arenas, definitions, settings, recording
    ///   activity and memo.
    /// - provides: one run-local owner for all scheduling and sharing state.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for a fresh empty memo, the observer is each
    ///   independent run’s verdict, process accounting and optional
    ///   derivation/support accounting. Recorded versus unrecorded and memoized
    ///   versus memoless runs distinguish stale state, unwanted recording and
    ///   use of a different run’s arena or settings.
    /// - witness: `machine::tests::recording_does_not_move_the_verdict`
    /// - witness: `machine::tests::the_sink_off_run_keeps_no_derivation`
    /// - witness: `machine::tests::the_memo_never_moves_a_verdict`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
        captures: [domain_address = &raw const *domain],
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret.core), core::ptr::from_ref(core))
            && core::ptr::eq(&raw const *ret.domain, domain_address)
            && ret.settings == settings
            && ret.processes.is_empty() && ret.queue.is_empty() && ret.queued.is_empty()
            && ret.bodies.is_empty() && ret.unfoldings.is_empty() && ret.openings.is_empty()
            && ret.entries.is_empty() && ret.variables.is_empty()
            && usize::from(ret.derivations.count()) == 0
            && ret.supports.totals() == SupportEdges::default()
            && ret.spent.0 == 0 && !ret.spent_overflowed
    )]
    fn new(
        core: &'run CoreArena,
        domain: &'run mut DomainArena,
        definitions: Definitions<'run>,
        settings: MachineSettings,
        activity: SinkActivity,
        memo: M,
    ) -> Self
    {
        Self {
            core,
            domain,
            definitions,
            settings,
            processes: Vec::new(),
            queue: VecDeque::new(),
            queued: Vec::new(),
            bodies: Vec::new(),
            unfoldings: BTreeMap::new(),
            openings: BTreeMap::new(),
            entries: BTreeMap::new(),
            variables: Vec::new(),
            derivations: Derivations::new(activity),
            memo,
            supports: Supports::new(M::ACTIVITY),
            spent: StepCount::default(),
            spent_overflowed: false,
        }
    }

    /// The process `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the process at `id`.
    /// - provides: the one checked read of the arena.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no process at `id`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — within a run, distinct process ids must select
    ///   distinct channels and goals, while a missing slot refuses. Exact
    ///   shared-body process counts and the delayed-premise comparison
    ///   distinguish wrong-slot reads and stale outcomes; malformed waiting ids
    ///   witness the refusal boundary.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    #[spec(
        ensures: |ret| match (self.processes.get(id.0), ret) {
            (Some(expected), Ok(actual)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(actual)),
            (None, Err(ConversionFault::MachineInvariant)) => true,
            _ => false,
        }
    )]
    fn process(
        &self,
        id: ProcessId,
    ) -> Result<&Process<'run>, ConversionFault>
    {
        self.processes
            .get(id.0)
            .ok_or(ConversionFault::MachineInvariant)
    }

    /// The process `id` names, mutably.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the process at `id`.
    /// - provides: the one checked write of the arena.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no process at `id`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the domain is mutable slots in one process arena,
    ///   including an absent id. The observer is refusal without a queued wait,
    ///   plus independent body completion and a later recalled result;
    ///   selecting a different slot or manufacturing a missing one changes
    ///   those observations.
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        captures: [address = self.processes.get(id.0).map(core::ptr::from_ref)],
        ensures: |ret| match (address, ret.as_ref()) {
            (Some(expected), Ok(actual)) => core::ptr::eq(expected, &raw const **actual),
            (None, Err(&ConversionFault::MachineInvariant)) => true,
            _ => false,
        }
    )]
    fn process_mut(
        &mut self,
        id: ProcessId,
    ) -> Result<&mut Process<'run>, ConversionFault>
    {
        self.processes
            .get_mut(id.0)
            .ok_or(ConversionFault::MachineInvariant)
    }

    /// What `id` has produced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the process's outcome.
    /// - provides: the read every combinator and slot polls.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no process at `id`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pending, settled, declined and missing processes are
    ///   observed through combinator answers and slot resolution. Wrong
    ///   outcomes, lost decline reasons and a fabricated answer for an absent
    ///   process are distinguished by the finite precedence cases and the
    ///   missing-wait refusal.
    /// - witness: `machine::tests::combinators_preserve_answer_and_decline_precedence`
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    #[spec(
        ensures: |ret| ret == self.processes.get(id.0).map(|process| process.outcome)
            .ok_or(ConversionFault::MachineInvariant)
    )]
    fn outcome(
        &self,
        id: ProcessId,
    ) -> Result<Outcome, ConversionFault>
    {
        let process = self.process(id)?;
        Ok(process.outcome)
    }

    /// Start a process, needed by nothing yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arena holds one more process with no demand, no
    ///   dependency and no waiter, the derivation store one more slot when
    ///   recording, and the support store one more inner support when the memo
    ///   is active.
    /// - provides: the one place a process id is minted.
    /// - fails: [`ConversionFault::MachineInvariant`] when a store and the
    ///   arena disagree.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — a store and the arena
    ///   disagree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over newly admitted goals and channels, the observer
    ///   is the exact number of independent bodies and shared goals and the
    ///   verdict they reach. Reused ids, pre-existing demand or a wrong work
    ///   kind alter sharing counts or the finite combinator outcomes; the
    ///   predicate pins the initial process state.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::combinators_preserve_answer_and_decline_precedence`
    #[spec(
        captures: [count = self.processes.len(), work_kind = core::mem::discriminant(&work)],
        ensures: |ret| ret.as_ref().is_ok_and(|id| id.0 == count
            && self.processes.len() == count.saturating_add(1)
            && self.queued.get(id.0) == Some(&Queued::Absent)
            && self.processes.get(id.0).is_some_and(|process| {
                process.outcome == outcome && process.share == share
                    && core::mem::discriminant(&process.work) == work_kind
                    && process.demand.0 == 0 && process.credit.0 == 0
                    && process.deps.is_empty() && process.waiters.is_empty()
            })) || ret.is_err()
    )]
    fn start(
        &mut self,
        work: Work<'run>,
        outcome: Outcome,
        share: Share,
    ) -> Result<ProcessId, ConversionFault>
    {
        let id = ProcessId(self.processes.len());
        self.processes.push(Process {
            work,
            outcome,
            demand: Demand::default(),
            deps: Vec::new(),
            waiters: Vec::new(),
            credit: Credit::default(),
            share,
        });
        self.queued.push(Queued::Absent);
        self.derivations.open(id)?;
        self.supports.open(id)?;
        Ok(id)
    }

    /// The goal comparing `sides` from `level` afresh, or the process already
    /// comparing them.
    ///
    /// # Specification
    /// - requires: every node and closure `sides` names lives in the domain.
    /// - ensures: when the memo holds a support agreeing with `sides` at
    ///   `level`, the process recorded under it, and nothing is started;
    ///   otherwise a pending goal with no frozen constant and an empty chain —
    ///   two heads compared from `level`, or two closures opened at `level` on
    ///   their opening channels and compared one binder deeper — recorded under
    ///   its support as a memo entry. The null memo starts every goal.
    /// - provides: process re-sharing, at the two places a goal is started
    ///   fresh: the root and a decomposition's premises.
    /// - fails: [`ConversionFault::Domain`] for a node that does not resolve,
    ///   [`ConversionFault::Memo`] when the memo refuses the entry,
    ///   [`ConversionFault::MachineInvariant`] at the binder-level ceiling, and
    ///   as [`Scheduler::start_goal`] and a channel raise.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — a node does not resolve.
    /// - [`ConversionFault::Memo`] — the memo refused the entry.
    /// - [`ConversionFault::MachineInvariant`] — the binder levels ran out.
    /// - [`ConversionFault`] — as a channel raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the domain is fresh or previously recorded weak-head
    ///   pairs and opened closure pairs at a fixed binder level. Verdict,
    ///   process counts and unchanged domain state at the level ceiling
    ///   distinguish missed sharing, reused foreign processes and allocation
    ///   before an impossible binder entry; a completed hit must remain usable
    ///   without another wakeup.
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    /// - witness: `machine::tests::binder_ceiling_is_refused_before_opening_or_eta_allocation`
    #[spec(
        ensures: |ret| (ret.as_ref().is_ok_and(|id| self.processes.get(id.0).is_some()) || ret.is_err())
            && (!matches!(sides, SupportSides::Opened(_, _))
            || u32::from(level) != u32::MAX || ret.is_err())
    )]
    fn start_fresh(
        &mut self,
        sides: SupportSides,
        level: BinderLevel,
    ) -> Result<ProcessId, ConversionFault>
    {
        let support = if matches!(M::ACTIVITY, MemoActivity::Active) {
            let support = GoalSupport::new(self.domain, sides, level)?;
            if let Some(hit) = self.memo.recall(&support) {
                return Ok(*hit.outcome());
            }
            Some(support)
        }
        else {
            None
        };
        let goal = match sides {
            | SupportSides::Closed(left, right) => Goal {
                left: Slot::Waiting(self.enter_channel(left)?),
                right: Slot::Waiting(self.enter_channel(right)?),
                depth: level,
                frozen: Frozen::default(),
                chain: Chain::default(),
                next: Next::Classify,
            },
            | SupportSides::Heads(left, right) => Goal {
                left: Slot::Ready(left),
                right: Slot::Ready(right),
                depth: level,
                frozen: Frozen::default(),
                chain: Chain::default(),
                next: Next::Classify,
            },
            | SupportSides::Opened(left, right) => {
                let deeper = deeper(level)?;
                let left = self.open_channel(left, level)?;
                let right = self.open_channel(right, level)?;
                Goal {
                    left: Slot::Waiting(left),
                    right: Slot::Waiting(right),
                    depth: deeper,
                    frozen: Frozen::default(),
                    chain: Chain::default(),
                    next: Next::Classify,
                }
            },
        };
        let id = self.start_goal(goal)?;
        if let Some(support) = support {
            let recorded = self
                .memo
                .remember(support, id)
                .map_err(ConversionFault::Memo)?;
            if recorded == MemoRecord::Recorded {
                self.supports.enter(id)?;
            }
        }
        Ok(id)
    }

    /// Answer `settled` for `id`, read from `basis`.
    ///
    /// # Specification
    /// - requires: `id` is a pending goal and `basis` what its answer rests on,
    ///   as [`Supports::settle`] names it.
    /// - ensures: the support store records the answer's edges, and `id` holds
    ///   the answer as [`Scheduler::finish`] leaves it.
    /// - provides: the one place a goal settles.
    /// - fails: as [`Supports::settle`] and [`Scheduler::finish`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Supports::settle`] and [`Scheduler::finish`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pending goal may settle positively or negatively,
    ///   resting on different support bases. Verdicts and exact
    ///   acceptance/refusal edge counts distinguish a reversed answer, retained
    ///   dependencies and a refusal recorded with only a winning branch’s
    ///   support.
    /// - witness: `machine::tests::an_acceptance_is_keyed_on_its_winning_derivation`
    /// - witness: `machine::tests::a_refusal_is_keyed_on_the_union_over_its_branches`
    /// - witness: `machine::tests::a_refutation_outranks_a_decline`
    #[spec(
        ensures: |ret| ret.is_err() || self.processes.get(id.0).is_some_and(|process|
            process.outcome == Outcome::Settled(settled) && matches!(process.work, Work::Spent)
                && process.deps.is_empty() && process.waiters.is_empty())
    )]
    fn answer(
        &mut self,
        id: ProcessId,
        settled: Settled,
        basis: &[ProcessId],
    ) -> Result<(), ConversionFault>
    {
        self.supports.settle(id, settled, basis)?;
        self.finish(id, Outcome::Settled(settled))
    }

    /// Start a goal at the floor share.
    ///
    /// # Specification
    /// - requires: every channel the goal's slots wait on was started.
    /// - ensures: a pending goal process; its slots' channels are recorded as
    ///   its dependencies.
    /// - provides: the goal constructor every rule uses.
    /// - fails: as [`Scheduler::start`] and [`Scheduler::depend`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::start`] and [`Scheduler::depend`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a new goal’s slots are either ready heads or channels
    ///   that are pending or already answered. Forced thunks, opened binders
    ///   and reused bodies observe whether the right dependencies and depth
    ///   survive admission; missing a wait edge prevents completion, while
    ///   waiting again on a completed premise causes a false cycle.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        captures: [slots = [goal.left, goal.right], depth = goal.depth],
        ensures: |ret| ret.as_ref().is_ok_and(|id| self.processes.get(id.0).is_some_and(|process| {
            process.outcome == Outcome::Pending
                && matches!(&process.work, Work::Goal(goal) if goal.left == slots[0] && goal.right == slots[1] && goal.depth == depth)
                && slots.iter().all(|slot| match *slot {
                    Slot::Ready(_) => true,
                    Slot::Waiting(channel) => self.processes.get(channel.0).is_some_and(|dependency|
                        dependency.outcome != Outcome::Pending || process.deps.contains(&channel)),
                })
        })) || ret.is_err()
    )]
    fn start_goal(
        &mut self,
        goal: Goal,
    ) -> Result<ProcessId, ConversionFault>
    {
        let slots = [goal.left, goal.right];
        let share = self.share_at(DefinitionHeight::default());
        let id = self.start(Work::Goal(goal), Outcome::Pending, share)?;
        for slot in slots {
            if let Slot::Waiting(channel) = slot {
                self.depend(id, channel)?;
            }
        }
        Ok(id)
    }

    /// The share a process working at `height` receives.
    ///
    /// # Specification
    /// trivial.
    fn share_at(
        &self,
        height: DefinitionHeight,
    ) -> Share
    {
        self.settings.scheduling().share(height)
    }

    /// Put `id` in the run queue unless it is already there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the queue holds `id` exactly once.
    /// - provides: the duplicate-free half of `Q`.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the membership
    ///   vector does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — no membership entry for `id`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the queue boundary is absent membership, an unqueued
    ///   live process and an already queued process. Named refusals, eventual
    ///   comparison outcomes and exact process sharing distinguish invented
    ///   membership, duplicate scheduling and a lost wakeup; the predicate
    ///   observes membership and queue multiplicity.
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    #[spec(
        captures: [member = self.queued.get(id.0).copied(), count = self.queue.len()],
        ensures: |ret| (match member {
            None => ret == Err(ConversionFault::MachineInvariant) && self.queue.len() == count,
            Some(Queued::Present) => ret.is_ok() && self.queue.len() == count,
            Some(Queued::Absent) => ret.is_ok() && self.queue.len() == count.saturating_add(1)
                && self.queue.back() == Some(&id),
        })
            && (ret.is_err() || (self.queued.get(id.0) == Some(&Queued::Present)
            && self.queue.iter().filter(|&&queued| queued == id).count() == 1))
    )]
    fn enqueue(
        &mut self,
        id: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        let membership = self
            .queued
            .get_mut(id.0)
            .ok_or(ConversionFault::MachineInvariant)?;
        if *membership == Queued::Absent {
            *membership = Queued::Present;
            self.queue.push_back(id);
        }
        Ok(())
    }

    /// Record that `waiter` waits on `dependency`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when `dependency` is pending, it lists `waiter` among its
    ///   waiters, `waiter` lists it among its dependencies, and it gains one
    ///   need when `waiter` is itself needed; a dependency that has answered is
    ///   left alone. Its observed outcome is returned in either case.
    /// - provides: the one place an edge of the wait map is drawn.
    /// - fails: [`ConversionFault::MachineInvariant`] for a missing dependency,
    ///   or for a missing waiter while that dependency is pending.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — a required process is missing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependencies that are pending acquire reciprocal wait
    ///   edges; completed ones return their outcome without needing a waiter.
    ///   The observer is the checked refusal for an absent dependency, no new
    ///   edge for an answered one, and successful delayed decomposition;
    ///   dropping the observed readiness or waiting on an answer produces a
    ///   false cycle.
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        captures: [observed = self.processes.get(dependency.0).map(|process| process.outcome)],
        ensures: |ret| match observed {
            None => ret == Err(ConversionFault::MachineInvariant),
            Some(outcome) if outcome != Outcome::Pending => ret == Ok(outcome),
            Some(_) => ret.is_err() || (ret == Ok(Outcome::Pending)
                && self.processes.get(waiter.0).is_some_and(|process| process.deps.last() == Some(&dependency))
                && self.processes.get(dependency.0).is_some_and(|process| process.waiters.last() == Some(&waiter))),
        }
    )]
    fn depend(
        &mut self,
        waiter: ProcessId,
        dependency: ProcessId,
    ) -> Result<Outcome, ConversionFault>
    {
        let outcome = self.outcome(dependency)?;
        if outcome != Outcome::Pending {
            return Ok(outcome);
        }
        let needed = {
            let process = self.process_mut(waiter)?;
            process.deps.push(dependency);
            process.demand
        };
        let target = self.process_mut(dependency)?;
        target.waiters.push(waiter);
        if needed > Demand::default() {
            self.need(dependency)?;
        }
        Ok(outcome)
    }

    /// Give `id` one more need, waking it and what it waits on if it had
    /// none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `id`'s demand is one higher; a pending process whose demand
    ///   rose from zero is queued and passes one need to each of its
    ///   dependencies, transitively.
    /// - provides: the waking half of demand.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — an id the arena does not hold.
    ///
    /// # Termination
    /// - reason: the `while let Some(next) = work.pop()` loop over an explicit
    ///   worklist of processes whose demand rose from zero, not recursion.
    /// - measure: the number of pending processes with no demand: an id is
    ///   pushed onward only when its demand rises from zero, which removes it
    ///   from that set.
    /// - boundedness: the arena is finite, so the set is; each pop either
    ///   shrinks it or pushes nothing.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — on finite wait graphs, a first demand activates
    ///   pending dependencies, an additional demand does not activate them
    ///   again, and missing ids refuse. Shared ladders observe duplicated
    ///   activation through process counts; a goal depending on itself
    ///   distinguishes terminating demand propagation from recursion or
    ///   repeated activation.
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
    #[spec(
        captures: [before = self.processes.get(id.0).map(|process| process.demand.0)],
        ensures: |ret| match before {
            None => ret == Err(ConversionFault::MachineInvariant),
            Some(before) => ret.is_err() || self.processes.get(id.0).is_some_and(|process|
                if before == 0 { process.demand.0 >= 1 }
                else { process.demand.0 == before.saturating_add(1) }),
        }
    )]
    fn need(
        &mut self,
        id: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        let mut work = Vec::from([id]);
        while let Some(next) = work.pop() {
            let process = self.process_mut(next)?;
            let woke = process.demand == Demand::default() && process.outcome == Outcome::Pending;
            process.demand = Demand(process.demand.0.saturating_add(1_u32));
            if woke {
                work.extend(process.deps.iter().copied());
                self.enqueue(next)?;
            }
        }
        Ok(())
    }

    /// Take one need from `id`, letting it and what it waits on fall dormant
    /// if none is left.
    ///
    /// # Specification
    /// - requires: `id` holds the need being returned.
    /// - ensures: `id`'s demand is one lower; a pending process whose demand
    ///   fell to zero takes one need from each of its dependencies,
    ///   transitively, and is skipped by the run queue until needed again.
    /// - provides: the cancelling half of demand.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — an id the arena does not hold.
    ///
    /// # Termination
    /// - reason: the `while let Some(next) = work.pop()` loop over an explicit
    ///   worklist of processes whose demand fell to zero, not recursion.
    /// - measure: the number of pending processes with nonzero demand: an id is
    ///   pushed onward only when its demand falls to zero.
    /// - boundedness: the arena is finite, so the set is.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cancellation boundary is zero demand, multiple
    ///   demand and the final need of a pending process. A refuting sibling
    ///   must cancel irrelevant work without changing the authoritative
    ///   verdict; cycles and shared subgoals distinguish repeated propagation
    ///   or demand underflow from releasing only the last need.
    /// - witness: `machine::tests::a_refutation_outranks_a_decline`
    /// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    #[spec(
        captures: [before = self.processes.get(id.0).map(|process| process.demand.0)],
        ensures: |ret| match before {
            None => ret == Err(ConversionFault::MachineInvariant),
            Some(before) => ret.is_err() || self.processes.get(id.0).is_some_and(|process|
                process.demand.0 == before.saturating_sub(1)),
        }
    )]
    fn unneed(
        &mut self,
        id: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        let mut work = Vec::from([id]);
        while let Some(next) = work.pop() {
            let process = self.process_mut(next)?;
            let had = process.demand;
            process.demand = Demand(process.demand.0.saturating_sub(1_u32));
            if had == Demand(1_u32) && process.outcome == Outcome::Pending {
                work.extend(process.deps.iter().copied());
            }
        }
        Ok(())
    }

    /// Record `outcome` for `id`, release what it waited on and wake what
    /// waits on it.
    ///
    /// # Specification
    /// - requires: `id` is pending.
    /// - ensures: `id` holds `outcome`; each dependency loses the need `id`
    ///   gave it; every waiter still pending and needed is queued.
    /// - provides: the one place a process answers.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — an id the arena does not hold.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completion may report either verdict, a decline or an
    ///   evaluated channel. The observers are combinator precedence, comparison
    ///   completion and emitted winning derivations; failing to store the
    ///   outcome, release dependencies or wake needed waiters loses a result or
    ///   keeps cancelled work alive.
    /// - witness: `machine::tests::combinators_preserve_answer_and_decline_precedence`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_refutation_outranks_a_decline`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        ensures: |ret| ret.is_err() || self.processes.get(id.0).is_some_and(|process|
            process.outcome == outcome && matches!(process.work, Work::Spent)
                && process.deps.is_empty() && process.waiters.is_empty())
    )]
    fn finish(
        &mut self,
        id: ProcessId,
        outcome: Outcome,
    ) -> Result<(), ConversionFault>
    {
        let (deps, waiters, needed) = {
            let process = self.process_mut(id)?;
            process.outcome = outcome;
            process.work = Work::Spent;
            (
                mem::take(&mut process.deps),
                mem::take(&mut process.waiters),
                process.demand,
            )
        };
        if needed > Demand::default() {
            for dependency in deps {
                self.unneed(dependency)?;
            }
        }
        for waiter in waiters {
            let process = self.process(waiter)?;
            if process.outcome == Outcome::Pending && process.demand > Demand::default() {
                self.enqueue(waiter)?;
            }
        }
        Ok(())
    }

    /// Charge `steps` to the run.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reported count increases by `steps`, saturating at its
    ///   ceiling; exceeding the representable count sets a sticky overflow bit.
    /// - provides: budget accounting that cannot be disabled by saturation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary charging and the counter ceiling are
    ///   observed through a bounded decline, a still-pending run crossing the
    ///   ceiling and an answer obtained on that same turn. Wrapping, forgetting
    ///   overflow and checking the budget before a completed answer change
    ///   these results; the const predicates compare the counter’s inner field.
    /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
    /// - witness: `machine::tests::step_counter_overflow_cannot_disable_the_budget_backstop`
    #[spec(
        ensures: |ret| self.spent.0 >= steps.0
            && (!self.spent_overflowed || self.spent.0 == u64::MAX)
    )]
    const fn charge(
        &mut self,
        steps: StepCount,
    )
    {
        let (spent, overflowed) = self.spent.0.overflowing_add(steps.0);
        self.spent = StepCount(if overflowed { u64::MAX } else { spent });
        self.spent_overflowed |= overflowed;
    }

    /// Run until the root answers, the needed goals deadlock, or the budget is
    /// spent.
    ///
    /// # Specification
    /// - requires: `root` is a pending goal.
    /// - ensures: the root's answer, reached by turns taken round-robin over
    ///   the run queue, each process passed over until its credit reaches its
    ///   share; [`DeclineReason::Budget`] once the steps charged pass the
    ///   settings' budget or overflow their counter with the root unanswered;
    ///   [`DeclineReason::Cycle`] when the queue empties with an unanswered
    ///   root under an active memo: every needed process waits on a pending
    ///   one, and the finite wait graph therefore closes into a cycle through a
    ///   re-shared goal.
    /// - provides: the machine's one loop, and the backstop every comparison
    ///   the cycle key does not catch reaches.
    /// - fails: every fault a turn raises, and
    ///   [`ConversionFault::MachineInvariant`] when the queue empties with the
    ///   root unanswered under the null memo, where no goal is ever waited on
    ///   by its own descendant.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault a turn raises.
    ///
    /// # Termination
    /// - reason: the `while let Some(id) = self.queue.pop_front()` loop below
    ///   is the conversion driver: every unfolding, every evaluation slice and
    ///   every alternative of every goal is issued from one of its turns, so it
    ///   is the loop that must end, and per-slice fuel bounds each evaluation
    ///   slice but never this loop.
    /// - measure: the budget left, `budget - spent`. Every table read and every
    ///   move charges one step plus one per alternative a choice starts, and
    ///   every unfinished evaluation slice charges at least one step. An
    ///   already completed evaluation may answer without charging; the loop
    ///   returns once the charged steps pass the budget, including overflow.
    /// - boundedness: the turns that charge nothing are bounded by the ones
    ///   that do. A goal that waits or combines was queued by a dependency
    ///   finishing, at most once per wait edge, and every edge was drawn when a
    ///   charged turn started a process; a channel's re-application turn runs
    ///   once per channel; a process passed over for credit re-queues at most
    ///   its share less one times per turn it takes; a process popped answered
    ///   or unneeded is dropped, once per queuing.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pending root goals either settle, decline in a rule,
    ///   exhaust their budget or deadlock through a shared cycle. The verdict
    ///   and charged count distinguish fabricated answers, a lost
    ///   completed-premise wakeup, counter saturation bypass and budget
    ///   precedence over a same-turn answer; fair and weighted schedules
    ///   separate scheduling from soundness.
    /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
    /// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
    /// - witness: `machine::tests::codes_that_could_unfold_inside_are_declined`
    /// - witness: `machine::tests::step_counter_overflow_cannot_disable_the_budget_backstop`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
        ensures: |ret| match ret {
            Ok(MachineVerdict::Convertible) => self.processes.get(root.0).is_some_and(|process| process.outcome == Outcome::Settled(Settled::Convertible)),
            Ok(MachineVerdict::NotConvertible) => self.processes.get(root.0).is_some_and(|process| process.outcome == Outcome::Settled(Settled::NotConvertible)),
            Ok(MachineVerdict::Declined(reason)) => self.processes.get(root.0).is_some_and(|process|
                process.outcome == Outcome::Declined(reason)
                    || (process.outcome == Outcome::Pending && match reason {
                        DeclineReason::Budget => self.spent_overflowed || self.spent.0 > self.settings.budget.0,
                        DeclineReason::Cycle => self.queue.is_empty() && matches!(M::ACTIVITY, MemoActivity::Active),
                        DeclineReason::UndecidedCodes => false,
                    })),
            Err(_) => true,
        }
    )]
    fn run(
        &mut self,
        root: ProcessId,
    ) -> Result<MachineVerdict, ConversionFault>
    {
        self.need(root)?;
        let budget = u64::from(self.settings.budget());
        while let Some(id) = self.queue.pop_front() {
            let membership = self
                .queued
                .get_mut(id.0)
                .ok_or(ConversionFault::MachineInvariant)?;
            *membership = Queued::Absent;
            let process = self.process_mut(id)?;
            if process.outcome != Outcome::Pending || process.demand == Demand::default() {
                continue;
            }
            process.credit = Credit(process.credit.0.saturating_add(1_u32));
            if process.credit.0 < u32::from(process.share) {
                self.enqueue(id)?;
                continue;
            }
            process.credit = Credit::default();
            let turn = self.turn(id)?;
            if turn == Turn::Again {
                self.enqueue(id)?;
            }
            let answered = self.outcome(root)?;
            match answered {
                | Outcome::Settled(Settled::Convertible) => {
                    return Ok(MachineVerdict::Convertible);
                },
                | Outcome::Settled(Settled::NotConvertible) => {
                    return Ok(MachineVerdict::NotConvertible);
                },
                | Outcome::Declined(reason) => return Ok(MachineVerdict::Declined(reason)),
                | Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                | Outcome::Pending => {},
            }
            if self.spent_overflowed || self.spent.0 > budget {
                return Ok(MachineVerdict::Declined(DeclineReason::Budget));
            }
        }
        match M::ACTIVITY {
            | MemoActivity::Active => Ok(MachineVerdict::Declined(DeclineReason::Cycle)),
            | MemoActivity::Inactive => Err(ConversionFault::MachineInvariant),
        }
    }

    /// Run one turn of `id`.
    ///
    /// # Specification
    /// - requires: `id` is pending.
    /// - ensures: one rule applied for a goal, one slice for a channel.
    /// - provides: the dispatch between the two process kinds.
    /// - fails: every fault the turn raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the turn raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pending work is a goal or an evaluation channel; a
    ///   successful turn either finishes it or preserves resumable work of the
    ///   same kind. Forced comparisons and divergence under a finite budget
    ///   distinguish dropping paused work, retaining completed work and
    ///   dispatching a channel as a goal.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        captures: [kind = self.processes.get(id.0).map(|process| core::mem::discriminant(&process.work))],
        ensures: |ret| ret.is_err() || self.processes.get(id.0).is_some_and(|process| match ret {
            Ok(Turn::Done) => process.outcome != Outcome::Pending && matches!(process.work, Work::Spent),
            Ok(Turn::Again | Turn::Wait) => process.outcome == Outcome::Pending
                && Some(core::mem::discriminant(&process.work)) == kind,
            Err(_) => false,
        })
    )]
    fn turn(
        &mut self,
        id: ProcessId,
    ) -> Result<Turn, ConversionFault>
    {
        let process = self.process_mut(id)?;
        let work = mem::replace(&mut process.work, Work::Spent);
        match work {
            | Work::Goal(mut goal) => {
                let turn = self.goal_turn(id, &mut goal)?;
                if turn != Turn::Done {
                    let process = self.process_mut(id)?;
                    process.work = Work::Goal(goal);
                }
                Ok(turn)
            },
            | Work::Channel(mut channel) => {
                let turn = self.channel_turn(id, &mut channel)?;
                if turn != Turn::Done {
                    let process = self.process_mut(id)?;
                    process.work = Work::Channel(channel);
                }
                Ok(turn)
            },
            | Work::Spent => Err(ConversionFault::MachineInvariant),
        }
    }

    /// One slice of a channel.
    ///
    /// # Specification
    /// - requires: `id` is the channel's own process.
    /// - ensures: a re-application waiting on a body that has answered starts
    ///   its evaluation; a running evaluation runs one slice and answers when
    ///   it reaches its weak head.
    /// - provides: the evaluation half of the machine.
    /// - fails: [`ConversionFault::Evaluation`] when the evaluation is refused,
    ///   [`ConversionFault::MachineInvariant`] when a body answered a
    ///   computation.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Evaluation`] — the evaluation was refused.
    /// - [`ConversionFault::MachineInvariant`] — a body is not a value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reapplication waits for a value body, whereas a
    ///   running evaluation pauses or finishes within one slice. The verdict
    ///   and charged budget distinguish running before a body exists, charging
    ///   a wait, losing paused work and failing to publish the channel’s
    ///   evaluated answer.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
    /// - witness: `machine::tests::step_counter_overflow_cannot_disable_the_budget_backstop`
    #[spec(
        captures: [before = self.spent.0],
        ensures: |ret| self.spent.0 >= before && self.spent.0.saturating_sub(before) <= u64::from(SLICE)
            && match ret {
                Ok(Turn::Wait) => self.spent.0 == before && matches!(*channel,
                    Channel::Reapply { body, .. } if self.processes.get(body.0).is_some_and(|process| process.outcome == Outcome::Pending)),
                Ok(Turn::Again) => matches!(*channel, Channel::Running(_)),
                Ok(Turn::Done) => self.processes.get(id.0).is_some_and(|process|
                    matches!(process.outcome, Outcome::Evaluated(_)) && matches!(process.work, Work::Spent)),
                Err(_) => true,
            }
    )]
    fn channel_turn(
        &mut self,
        id: ProcessId,
        channel: &mut Channel<'run>,
    ) -> Result<Turn, ConversionFault>
    {
        match *channel {
            | Channel::Reapply { body, neutral } => {
                let answered = self.outcome(body)?;
                match answered {
                    | Outcome::Pending => Ok(Turn::Wait),
                    | Outcome::Evaluated(Glued::Value(head)) => {
                        let held = self
                            .domain
                            .neutral(neutral)
                            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                        let evaluation =
                            Evaluation::eliminate(self.definitions, head, held.spine());
                        *channel = Channel::Running(evaluation);
                        Ok(Turn::Again)
                    },
                    | Outcome::Evaluated(Glued::Computation(_))
                    | Outcome::Settled(_)
                    | Outcome::Declined(_) => Err(ConversionFault::MachineInvariant),
                }
            },
            | Channel::Running(ref mut evaluation) => {
                let sliced = evaluation.resume(self.core, self.domain, Fuel::from(SLICE));
                let (progress, spent) = sliced.map_err(ConversionFault::Evaluation)?;
                self.charge(StepCount(u64::from(u32::from(spent))));
                match progress {
                    | Progress::Paused => Ok(Turn::Again),
                    | Progress::Finished(glued) => {
                        self.finish(id, Outcome::Evaluated(glued))?;
                        Ok(Turn::Done)
                    },
                }
            },
        }
    }

    /// One rule of a goal.
    ///
    /// # Specification
    /// - requires: `id` is the goal's own process.
    /// - ensures: a goal whose sides are not both in hand waits; otherwise it
    ///   reads the rule table, takes its alternative's move, or reads its
    ///   children, and either answers, waits, or runs again.
    /// - provides: the comparison half of the machine.
    /// - fails: every fault a rule raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault a rule raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a goal has two ready slots or at least one pending
    ///   channel, then classifies, moves or combines. The observers are
    ///   successful forced and eta comparisons, the finite precedence outcomes
    ///   and reuse of completed premises; advancing a blocked goal or losing
    ///   its next action changes those answers.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::combinators_preserve_answer_and_decline_precedence`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        captures: [left = goal.left, right = goal.right],
        ensures: |ret| ret.is_err() || self.processes.get(id.0).is_some_and(|process|
            match ret { Ok(Turn::Done) => process.outcome != Outcome::Pending,
                Ok(Turn::Again | Turn::Wait) => process.outcome == Outcome::Pending,
                Err(_) => false })
            && (![left, right].iter().any(|slot| matches!(*slot, Slot::Waiting(channel)
                if self.processes.get(channel.0).is_some_and(|process| process.outcome == Outcome::Pending)))
                || (ret == Ok(Turn::Wait) && goal.left == left && goal.right == right))
    )]
    fn goal_turn(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
    ) -> Result<Turn, ConversionFault>
    {
        let left = self.resolve(goal.left)?;
        let right = self.resolve(goal.right)?;
        let (Slot::Ready(left), Slot::Ready(right)) = (left, right)
        else {
            return Ok(Turn::Wait);
        };
        goal.left = Slot::Ready(left);
        goal.right = Slot::Ready(right);
        let next = mem::replace(&mut goal.next, Next::Classify);
        match next {
            | Next::Classify => self.classify(id, goal, (left, right)),
            | Next::Move(chosen) => self.take(id, goal, (left, right), chosen),
            | Next::Combine(combine) => self.combine(id, goal, combine),
        }
    }

    /// A slot with its channel's answer read in, when it has one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a ready slot unchanged; a waiting slot whose channel answered
    ///   becomes ready with that answer; one whose channel is pending stays
    ///   waiting.
    /// - provides: the receive side of a channel.
    /// - fails: [`ConversionFault::MachineInvariant`] for a channel that
    ///   answered a verdict.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the slot names a goal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ready heads pass through, a pending channel remains
    ///   waiting, an evaluated channel supplies its head and an absent or
    ///   verdict-bearing process refuses. Forced and eta comparisons observe
    ///   the supplied head; malformed waits distinguish a checked refusal from
    ///   treating a goal verdict as an evaluated term.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
    /// - witness: `machine::tests::missing_processes_refuse_without_creating_waits`
    #[spec(
        ensures: |ret| ret == match slot {
            Slot::Ready(_) => Ok(slot),
            Slot::Waiting(channel) => match self.processes.get(channel.0).map(|process| process.outcome) {
                Some(Outcome::Pending) => Ok(slot),
                Some(Outcome::Evaluated(glued)) => Ok(Slot::Ready(glued)),
                None | Some(Outcome::Settled(_) | Outcome::Declined(_)) => Err(ConversionFault::MachineInvariant),
            },
        }
    )]
    fn resolve(
        &self,
        slot: Slot,
    ) -> Result<Slot, ConversionFault>
    {
        let Slot::Waiting(channel) = slot
        else {
            return Ok(slot);
        };
        let outcome = self.outcome(channel)?;
        match outcome {
            | Outcome::Pending => Ok(slot),
            | Outcome::Evaluated(glued) => Ok(Slot::Ready(glued)),
            | Outcome::Settled(_) | Outcome::Declined(_) => Err(ConversionFault::MachineInvariant),
        }
    }

    /// Read the rule table for a goal and act on it.
    ///
    /// # Specification
    /// - requires: both sides are in hand.
    /// - ensures: one step charged, and the plan's rule applied: a shared or
    ///   leaf answer recorded, a decomposition's children started, a step's
    ///   decisions recorded and its sides replaced — or the goal declined when
    ///   the step would repeat an unfolding on its chain — or a choice's
    ///   alternatives started; the goal's share tracks the height of the
    ///   defined heads it compares. Positive leaves retain an explicit shared
    ///   comparison, so the next sibling cannot consume their trace boundary.
    /// - provides: the table read once per goal turn.
    /// - fails: every fault the table or the rule raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the table or the rule raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for well-formed weak heads, the rule table selects a
    ///   leaf, decomposition, unfolding, force, eta, a choice or an
    ///   undecided-code decline. Verdicts, named trace decisions and kernel
    ///   replay distinguish a wrong arm or side; the budget witness observes
    ///   missing classification charges.
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::codes_that_could_unfold_inside_are_declined`
    /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
    #[spec(
        captures: [before = self.spent.0],
        ensures: |ret| self.spent.0 >= before.saturating_add(1)
            && (ret.is_err() || self.processes.get(id.0).is_some_and(|process| match ret {
                Ok(Turn::Done) => process.outcome != Outcome::Pending,
                Ok(Turn::Again | Turn::Wait) => process.outcome == Outcome::Pending,
                Err(_) => false,
            }))
    )]
    fn classify(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
    ) -> Result<Turn, ConversionFault>
    {
        self.charge(StepCount::ONE);
        let planned = plan(
            self.core,
            self.domain,
            self.definitions,
            &goal.frozen,
            pair.0,
            pair.1,
        )?;
        let height = self.pair_height(pair)?;
        let share = self.share_at(height);
        self.process_mut(id)?.share = share;
        match planned {
            | Plan::Shared(settled) | Plan::Leaf(settled) => {
                if matches!(planned, Plan::Shared(_)) || settled == Settled::Convertible {
                    self.derivations
                        .decide(id, ConversionDecision::ComparedShared {
                            left: TraceNode::of(pair.0),
                            right: TraceNode::of(pair.1),
                        })?;
                }
                self.answer(id, settled, &[])?;
                Ok(Turn::Done)
            },

            | Plan::Decompose(subgoals) => {
                self.decompose(id, goal, pair, subgoals, Collapse::Allowed)
            },
            | Plan::Step(Step::Unfold(side)) => {
                let advance = self.unfold(id, goal, pair, side)?;
                self.advanced(id, advance)
            },
            | Plan::Step(Step::Force) => {
                self.force(id, goal, pair)?;
                Ok(Turn::Again)
            },
            | Plan::Step(Step::Eta(side)) => {
                self.eta(id, goal, pair, side)?;
                Ok(Turn::Again)
            },
            | Plan::Choose(choice) => self.choose(id, goal, choice),
            | Plan::Decline(reason) => {
                self.finish(id, Outcome::Declined(reason))?;
                Ok(Turn::Done)
            },
        }
    }

    /// The turn an unfolding step leaves its goal at.
    ///
    /// # Specification
    /// - requires: `advance` is what unfolding one of `id`'s sides answered.
    /// - ensures: [`Turn::Again`] when the side now waits on its unfolding;
    ///   otherwise the goal declines with [`DeclineReason::Cycle`] and the turn
    ///   is [`Turn::Done`].
    /// - provides: the one place a cycle becomes a decline.
    /// - fails: as [`Scheduler::finish`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::finish`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the boundary is a fresh unfolding versus repetition
    ///   of the same side’s complete cycle key. The observer is a continuing
    ///   conversion or a cycle decline without a derivation; treating every
    ///   unfolding as a cycle, or a repeated one as progress, changes the
    ///   finite witnesses.
    /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
    /// - witness: `machine::tests::unfolding_one_function_twice_is_not_a_cycle`
    #[spec(
        ensures: |ret| match advance {
            Advance::Unfolding => ret == Ok(Turn::Again),
            Advance::Cycle => ret.is_err() || (ret == Ok(Turn::Done)
                && self.processes.get(id.0).is_some_and(|process| process.outcome == Outcome::Declined(DeclineReason::Cycle))),
        }
    )]
    fn advanced(
        &mut self,
        id: ProcessId,
        advance: Advance,
    ) -> Result<Turn, ConversionFault>
    {
        match advance {
            | Advance::Unfolding => Ok(Turn::Again),
            | Advance::Cycle => {
                self.finish(id, Outcome::Declined(DeclineReason::Cycle))?;
                Ok(Turn::Done)
            },
        }
    }

    /// The tallest definitional height among the pair's defined heads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the larger of the two sides' head heights, a side that is not
    ///   a constant-headed neutral counting as the floor.
    /// - provides: the height the scheduling share reads.
    /// - fails: [`ConversionFault::Domain`] for a node that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — a node does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over value and computation heads, only defined
    ///   neutral heads contribute height, and the taller side controls
    ///   scheduling. Fair versus height-weighted outcomes and the two-sided
    ///   ladder comparisons distinguish ignoring one head, taking the minimum
    ///   or assigning a former a definitional height.
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::head_height_is_symmetric_and_nonconstants_stay_at_the_floor`
    #[spec(
        ensures: |ret| {
            let height = |glued| -> Result<DefinitionHeight, ConversionFault> {
                let neutral = match glued {
                    Glued::Value(value) => match self.domain.value(value) {
                        Some(&DomainValue::Neutral { neutral, .. }) => Some(neutral),
                        Some(_) => None,
                        None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
                    },
                    Glued::Computation(comp) => match self.domain.computation(comp) {
                        Some(&DomainComp::Neutral { neutral, .. }) => Some(neutral),
                        Some(_) => None,
                        None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
                    },
                };
                neutral.map_or_else(|| Ok(DefinitionHeight::default()), |neutral|
                    self.domain.neutral(neutral)
                        .ok_or(ConversionFault::Domain(DomainFault::Dangling))
                        .map(|node| match node.head() {
                            NeutralHead::Constant(constant) => self.definitions.height(constant),
                            NeutralHead::Variable { .. } | NeutralHead::Module(_) => DefinitionHeight::default(),
                        }))
            };
            ret == height(pair.0).and_then(|left| height(pair.1).map(|right| left.max(right)))
        }
    )]
    fn pair_height(
        &self,
        pair: (Glued, Glued),
    ) -> Result<DefinitionHeight, ConversionFault>
    {
        let mut tallest = DefinitionHeight::default();
        for glued in [pair.0, pair.1] {
            let neutral = match glued {
                | Glued::Value(value) => match self.domain.value(value) {
                    | Some(&DomainValue::Neutral { neutral, .. }) => neutral,
                    | Some(_) => continue,
                    | None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
                },
                | Glued::Computation(comp) => match self.domain.computation(comp) {
                    | Some(&DomainComp::Neutral { neutral, .. }) => neutral,
                    | Some(_) => continue,
                    | None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
                },
            };
            let held = self
                .domain
                .neutral(neutral)
                .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
            if let NeutralHead::Constant(constant) = held.head() {
                tallest = tallest.max(self.definitions.height(constant));
            }
        }
        Ok(tallest)
    }

    /// Start a decomposition's children and wait or poll their answers.
    ///
    /// # Specification
    /// - requires: `subgoals` are the decomposition's premises in subgoal
    ///   order.
    /// - ensures: an empty decomposition answers convertible at once; otherwise
    ///   one child per subgoal, started fresh or re-shared by
    ///   [`Scheduler::start_fresh`] — a value pair as it stands, an opened pair
    ///   at this depth — with one premise per position even where two positions
    ///   name one process. A known refutation or no pending premise schedules
    ///   another turn; otherwise completion of a pending child wakes the goal.
    /// - provides: every rule with premises compared child by child.
    /// - fails: as [`Scheduler::start_fresh`] and [`Scheduler::depend`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::start_fresh`] and [`Scheduler::depend`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decomposition has no premises, pending premises or
    ///   already answered memo hits. The observer is its conjunction’s verdict,
    ///   with refutation dominant and child order retained in the trace; an
    ///   empty conjunction agrees, while completed premises must schedule a
    ///   poll rather than wait for a wakeup that cannot arrive.
    /// - witness: `machine::tests::empty_choices_refuse_instead_of_producing_a_refutation`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    /// - witness: `machine::tests::a_refutation_outranks_a_decline`
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    #[spec(
        captures: [count = subgoals.len()],
        ensures: |ret| match ret {
            Err(_) => true,
            Ok(Turn::Done) => count == 0 && self.processes.get(id.0).is_some_and(|process| process.outcome == Outcome::Settled(Settled::Convertible)),
            Ok(turn @ (Turn::Again | Turn::Wait)) => count != 0 && match goal.next {
                Next::Combine(Combine::All { pair: actual, ref children, collapse: held }) => {
                    actual == pair && held == collapse && children.len() == count
                        && children.iter().all(|child| self.processes.get(child.0).is_some())
                        && (turn == Turn::Again) == (
                            children.iter().all(|child| self.processes.get(child.0).is_some_and(|process| process.outcome != Outcome::Pending))
                            || children.iter().any(|child| self.processes.get(child.0).is_some_and(|process|
                                matches!(process.outcome, Outcome::Settled(Settled::NotConvertible) | Outcome::Evaluated(_)))))
                }
                _ => false,
            },
        }
    )]
    fn decompose(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        subgoals: Vec<Subgoal>,
        collapse: Collapse,
    ) -> Result<Turn, ConversionFault>
    {
        if subgoals.is_empty() {
            if collapse == Collapse::Allowed {
                self.derivations
                    .decide(id, ConversionDecision::ComparedShared {
                        left: TraceNode::of(pair.0),
                        right: TraceNode::of(pair.1),
                    })?;
            }
            self.answer(id, Settled::Convertible, &[])?;
            return Ok(Turn::Done);
        }
        let mut waiting = false;
        let mut ready = false;
        let mut children = Vec::with_capacity(subgoals.len());
        for subgoal in subgoals {
            let (sides, depth) = match subgoal {
                | Subgoal::Values(left, right) => (
                    SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                    goal.depth,
                ),
                | Subgoal::Opened(left, right) => (SupportSides::Opened(left, right), goal.depth),
                | Subgoal::Classifiers(left, right) => {
                    let left = self.domain.value_code(left, TermFace::Reduced);
                    let right = self.domain.value_code(right, TermFace::Reduced);
                    (
                        SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                        goal.depth,
                    )
                },
                | Subgoal::CaseMotives(left, right) => {
                    let depth = deeper(goal.depth)?;
                    let variable = self.variable(goal.depth)?;
                    let left = self.case_motive(left, variable)?;
                    let right = self.case_motive(right, variable)?;
                    (
                        SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                        depth,
                    )
                },
                | Subgoal::CaseBranch { left, right, tag } => {
                    let left = self.case_branch(left, tag)?;
                    let right = self.case_branch(right, tag)?;
                    (SupportSides::Closed(left, right), goal.depth)
                },
            };
            let child = self.start_fresh(sides, depth)?;
            let outcome = self.depend(id, child)?;
            waiting |= outcome == Outcome::Pending;
            ready |= matches!(
                outcome,
                Outcome::Settled(Settled::NotConvertible) | Outcome::Evaluated(_)
            );
            children.push(child);
        }
        goal.next = Next::Combine(Combine::All {
            pair,
            children,
            collapse,
        });
        // A recalled answer will not send another wakeup.
        // Poll a known refutation now, or combine when no child is pending.
        Ok(if ready || !waiting {
            Turn::Again
        }
        else {
            Turn::Wait
        })
    }

    /// Quote a native case motive under the same fresh scrutinee on both sides.
    ///
    /// # Specification
    /// - requires: the supplied variable is fresh at the parent goal's depth.
    /// - ensures: the motive reads that variable at index zero and preserves
    ///   outer capture.
    /// - fails: dangling or malformed case sources.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependent motives distinguish the fresh scrutinee
    ///   from outer variables.
    /// - witness: `machine::tests::native_records_cases_and_traces_agree`
    #[spec(ensures:|ret| ret.is_err() || ret.as_ref().is_ok_and(|value| matches!(self.domain.value(*value),Some(DomainValue::Code { .. }))))]
    fn case_motive(
        &mut self,
        case: CompClosureId,
        variable: DomainValueId,
    ) -> Result<DomainValueId, ConversionFault>
    {
        let (motive, _) = crate::rules::case_source(self.core, self.domain, case)?;
        let closure = self
            .domain
            .comp_closure(case)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let mut environment = closure.environment().clone();
        environment.extend(Zone::Intuitionistic, variable);
        let quoted = self
            .domain
            .value_closure_node(crate::ValueBody::CompType(motive), environment);
        Ok(self.domain.value_code(quoted, TermFace::Reduced))
    }

    /// Capture one ordinary case branch without introducing an implicit field
    /// binder.
    ///
    /// # Specification
    /// - requires: nothing; missing ordinals are refused.
    /// - ensures: returns the selected branch over the case's original ambient
    ///   environment.
    /// - fails: dangling captures or absent branch ordinals.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — branch lambdas, rather than case metadata, bind
    ///   constructor fields.
    /// - witness: `machine::tests::native_records_cases_and_traces_agree`
    #[spec(ensures:|ret| ret.is_err() || ret.as_ref().is_ok_and(|closure| self.domain.comp_closure(*closure).is_some()))]
    fn case_branch(
        &mut self,
        case: CompClosureId,
        tag: gandr_core_term::ConstructorTag,
    ) -> Result<CompClosureId, ConversionFault>
    {
        let (_, branches) = crate::rules::case_source(self.core, self.domain, case)?;
        let body = *branches
            .get(usize::from(tag))
            .ok_or(ConversionFault::MachineInvariant)?;
        let closure = self
            .domain
            .comp_closure(case)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let environment = closure.environment().clone();
        Ok(self.domain.comp_closure_node(body, environment))
    }

    /// The neutral a weak head is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the neutral the side stands for.
    /// - provides: the read every constant move starts from.
    /// - fails: [`ConversionFault::MachineInvariant`] for a side that is not a
    ///   neutral, which a move only meets if the table and the move disagree;
    ///   [`ConversionFault::Domain`] for a node that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the side is not a neutral.
    /// - [`ConversionFault::Domain`] — the side does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live neutral wrapper must expose the neutral of its
    ///   own polarity; a former or missing wrapper refuses. Value unfolding and
    ///   computation-spine refutation observe which head was extracted, while
    ///   the malformed-head probe distinguishes shape refusal from
    ///   dangling-domain refusal.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    /// - witness: `machine::tests::malformed_heads_and_channel_entries_are_refused`
    #[spec(
        ensures: |ret| ret == match glued {
            Glued::Value(value) => match self.domain.value(value) {
                Some(&DomainValue::Neutral { neutral, .. }) => Ok(neutral),
                Some(_) => Err(ConversionFault::MachineInvariant),
                None => Err(ConversionFault::Domain(DomainFault::Dangling)),
            },
            Glued::Computation(comp) => match self.domain.computation(comp) {
                Some(&DomainComp::Neutral { neutral, .. }) => Ok(neutral),
                Some(_) => Err(ConversionFault::MachineInvariant),
                None => Err(ConversionFault::Domain(DomainFault::Dangling)),
            },
        }
    )]
    fn neutral_of(
        &self,
        glued: Glued,
    ) -> Result<NeutralId, ConversionFault>
    {
        match glued {
            | Glued::Value(value) => match self.domain.value(value) {
                | Some(&DomainValue::Neutral { neutral, .. }) => Ok(neutral),
                | Some(_) => Err(ConversionFault::MachineInvariant),
                | None => Err(ConversionFault::Domain(DomainFault::Dangling)),
            },
            | Glued::Computation(comp) => match self.domain.computation(comp) {
                | Some(&DomainComp::Neutral { neutral, .. }) => Ok(neutral),
                | Some(_) => Err(ConversionFault::MachineInvariant),
                | None => Err(ConversionFault::Domain(DomainFault::Dangling)),
            },
        }
    }

    /// The constant a neutral is headed by.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the head's admission position.
    /// - provides: the identifier every constant decision names.
    /// - fails: [`ConversionFault::MachineInvariant`] for a variable or module
    ///   head, [`ConversionFault::Domain`] for a dangling neutral.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the head is not a constant.
    /// - [`ConversionFault::Domain`] — the neutral does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — constant, variable, module and missing neutral heads
    ///   lie on the extraction boundary. Exact named unfoldings separate wrong
    ///   constants; the malformed-head probe observes the different shape and
    ///   missing-domain refusals instead of letting a nonconstant head become a
    ///   definition.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::malformed_heads_and_channel_entries_are_refused`
    #[spec(
        ensures: |ret| ret == self.domain.neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))
            .and_then(|held| match held.head() {
                NeutralHead::Constant(constant) => Ok(constant),
                NeutralHead::Variable { .. } | NeutralHead::Module(_) => Err(ConversionFault::MachineInvariant),
            })
    )]
    fn head_constant(
        &self,
        neutral: NeutralId,
    ) -> Result<ConstantIndex, ConversionFault>
    {
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        match held.head() {
            | NeutralHead::Constant(constant) => Ok(constant),
            | NeutralHead::Variable { .. } | NeutralHead::Module(_) => {
                Err(ConversionFault::MachineInvariant)
            },
        }
    }

    /// The side of a pair.
    ///
    /// # Specification
    /// trivial.
    const fn side_of(
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Glued
    {
        match side {
            | ConversionSide::Left => pair.0,
            | ConversionSide::Right => pair.1,
        }
    }

    /// Replace one side of a goal.
    ///
    /// # Specification
    /// trivial.
    fn set_side(
        goal: &mut Goal,
        side: ConversionSide,
        slot: Slot,
    )
    {
        match side {
            | ConversionSide::Left => goal.left = slot,
            | ConversionSide::Right => goal.right = slot,
        }
    }

    /// Unfold the defined head on `side`: record the decision and wait on the
    /// neutral's unfolding channel.
    ///
    /// # Specification
    /// - requires: `side` holds a neutral headed by a defined constant.
    /// - ensures: [`Advance::Cycle`] with nothing recorded when the side's
    ///   chain already holds this definition over this spine; otherwise the
    ///   chain holds it, the derivation records `Unfold` and the side's
    ///   reduction, the goal's support holds the definition, the side waits on
    ///   the neutral's unfolding, and the answer is [`Advance::Unfolding`].
    /// - provides: the red-l and red-r rules, and the cycle check every
    ///   unfolding passes through.
    /// - fails: every fault the channel raises, and
    ///   [`ConversionFault::MachineInvariant`] when the side is not a defined
    ///   neutral.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the channel raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unfolding either side selects that side’s constant
    ///   and full spine; a repeated key declines without replacing either slot.
    ///   The observer is the ordered unfolding/reduction trace and resulting
    ///   verdict, separating wrong-side replacement, lost spine arguments and a
    ///   constant-only cycle key.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::unfolding_one_function_twice_is_not_a_cycle`
    /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
    #[spec(
        captures: [left = goal.left, right = goal.right],
        ensures: |ret| match ret {
            Err(_) => true,
            Ok(Advance::Cycle) => goal.left == left && goal.right == right,
            Ok(Advance::Unfolding) => match side {
                ConversionSide::Left => goal.right == right && matches!(goal.left, Slot::Waiting(channel) if self.processes.get(channel.0).is_some()),
                ConversionSide::Right => goal.left == left && matches!(goal.right, Slot::Waiting(channel) if self.processes.get(channel.0).is_some()),
            },
        }
    )]
    fn unfold(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Result<Advance, ConversionFault>
    {
        let neutral = self.neutral_of(Self::side_of(pair, side))?;
        let constant = self.head_constant(neutral)?;
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let unfolded = Unfolded {
            constant,
            spine: Vec::from(held.spine()),
        };
        if goal.chain.enter(side, unfolded) == Repeat::Repeated {
            return Ok(Advance::Cycle);
        }
        let named = TraceNode::Constant(constant);
        self.derivations
            .decide(id, ConversionDecision::Unfold { constant: named })?;
        let reduced = match side {
            | ConversionSide::Left => ConversionDecision::ReduceLeft { redex: named },
            | ConversionSide::Right => ConversionDecision::ReduceRight { redex: named },
        };
        self.derivations.decide(id, reduced)?;
        self.supports.unfolded(id, constant)?;
        let channel = self.unfold_channel(neutral)?;
        Self::set_side(goal, side, Slot::Waiting(channel));
        self.depend(id, channel)?;
        Ok(Advance::Unfolding)
    }

    /// Force both sides: enter a thunk, or stack a force on a stuck value.
    ///
    /// # Specification
    /// - requires: each side is a thunk or a neutral value, and one is a thunk.
    /// - ensures: the derivation records one `Force` per side, left first; a
    ///   thunk side waits on its entering channel, and a neutral side becomes
    ///   the neutral computation with one more force on its spine.
    /// - provides: the thunk congruence and the thunk η-rule.
    /// - fails: every fault the channel or the domain raises, and
    ///   [`ConversionFault::MachineInvariant`] for a side of another shape.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the channel or the domain raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a force step crosses from two value heads to
    ///   computation slots, entering thunks or extending a neutral spine. The
    ///   trace must name both forces and the resulting computations must agree
    ///   or refute as their returned values do; leaving a value slot behind or
    ///   forcing only one side changes that observation.
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
    #[spec(
        ensures: |ret| ret.is_err() || [goal.left, goal.right].iter().all(|slot| match *slot {
            Slot::Ready(Glued::Computation(comp)) => self.domain.computation(comp).is_some(),
            Slot::Waiting(channel) => self.processes.get(channel.0).is_some(),
            Slot::Ready(Glued::Value(_)) => false,
        })
    )]
    fn force(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
    ) -> Result<(), ConversionFault>
    {
        for side in [ConversionSide::Left, ConversionSide::Right] {
            let glued = Self::side_of(pair, side);
            self.derivations.decide(id, ConversionDecision::Force {
                thunk: TraceNode::of(glued),
            })?;
            let Glued::Value(value) = glued
            else {
                return Err(ConversionFault::MachineInvariant);
            };
            let node = self
                .domain
                .value(value)
                .copied()
                .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
            match node {
                | DomainValue::Thunk { body, .. } => {
                    let channel = self.enter_channel(body)?;
                    Self::set_side(goal, side, Slot::Waiting(channel));
                    self.depend(id, channel)?;
                },
                | DomainValue::Neutral { neutral, .. } => {
                    let grown = extend_spine(self.domain, neutral, Elimination::Force)
                        .map_err(ConversionFault::Evaluation)?;
                    let forced = self.domain.comp_neutral(grown, CompTermFace::Reduced);
                    Self::set_side(goal, side, Slot::Ready(Glued::Computation(forced)));
                },
                | DomainValue::PathCertificate { .. }
                | DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Unit { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Pair { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. } => {
                    return Err(ConversionFault::MachineInvariant);
                },
            }
        }
        Ok(())
    }

    /// η-expand the neutral on `side` against the lambda on the other.
    ///
    /// # Specification
    /// - requires: `side` holds a neutral computation and the other side a
    ///   lambda.
    /// - ensures: the derivation records `EtaExpand` naming the fresh variable
    ///   at the goal's depth; the neutral side becomes the neutral applied to
    ///   it, the lambda side waits on its body opened under it, and the goal is
    ///   one binder deeper.
    /// - provides: the safe and profitable η case of §6.2.
    /// - fails: every fault the channel or the domain raises, and
    ///   [`ConversionFault::MachineInvariant`] for sides of other shapes or at
    ///   the binder-level ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the channel or the domain raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a neutral computation is expanded against a lambda on
    ///   either side at a representable fresh level. The eta trace observes one
    ///   shared fresh variable, and the ceiling refusal observes that no
    ///   variable is allocated before an impossible increment; swapping sides,
    ///   reusing a level or allocating before the check changes these
    ///   witnesses.
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::a_lambda_meets_a_stuck_function_by_eta`
    /// - witness: `machine::tests::binder_ceiling_is_refused_before_opening_or_eta_allocation`
    #[spec(
        captures: [depth = goal.depth, left = goal.left, right = goal.right],
        ensures: |ret| match u32::from(depth).checked_add(1) {
            None => ret == Err(ConversionFault::MachineInvariant)
                && goal.depth == depth && goal.left == left && goal.right == right,
            Some(opened) => ret.is_err() || (u32::from(goal.depth) == opened
                && match side {
                    ConversionSide::Left => matches!(goal.left, Slot::Ready(Glued::Computation(_))) && matches!(goal.right, Slot::Waiting(_)),
                    ConversionSide::Right => matches!(goal.right, Slot::Ready(Glued::Computation(_))) && matches!(goal.left, Slot::Waiting(_)),
                }),
        }
    )]
    fn eta(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Result<(), ConversionFault>
    {
        let opened_depth = deeper(goal.depth)?;
        let variable = self.variable(goal.depth)?;
        self.derivations.decide(id, ConversionDecision::EtaExpand {
            side,
            variable: TraceNode::Value(variable),
        })?;
        let neutral = self.neutral_of(Self::side_of(pair, side))?;
        let grown = extend_spine(self.domain, neutral, Elimination::Apply(variable))
            .map_err(ConversionFault::Evaluation)?;
        let applied = self.domain.comp_neutral(grown, CompTermFace::Reduced);
        Self::set_side(goal, side, Slot::Ready(Glued::Computation(applied)));
        let lambda_side = other(side);
        let Glued::Computation(lambda) = Self::side_of(pair, lambda_side)
        else {
            return Err(ConversionFault::MachineInvariant);
        };
        let body = match self.domain.computation(lambda) {
            | Some(&DomainComp::Lambda { body, .. }) => body,
            | Some(_) => return Err(ConversionFault::MachineInvariant),
            | None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
        };
        let channel = self.open_channel(body, goal.depth)?;
        Self::set_side(goal, lambda_side, Slot::Waiting(channel));
        self.depend(id, channel)?;
        goal.depth = opened_depth;
        Ok(())
    }

    /// Start a choice's alternatives and wait on their combination.
    ///
    /// # Specification
    /// - requires: both sides are in hand.
    /// - ensures: one step charged per alternative, and one goal per
    ///   alternative over this goal's sides, depth, frozen constants and chain,
    ///   each starting with its move; the goal waits on them under the choice's
    ///   combinator.
    /// - provides: every choice point.
    /// - fails: as [`Scheduler::start_goal`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::start_goal`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four choice constructors have two or three
    ///   ordered alternatives, with frozen inputs and the authoritative move
    ///   preserved. The observer is the selected conversion trace and its
    ///   independent replay; missing a branch, charging the wrong arity, moving
    ///   authority or dropping inherited freezes changes those results.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    #[spec(
        captures: [before = self.spent.0],
        ensures: |ret| ret.is_err() || (ret == Ok(Turn::Wait) && {
            let expected: &[Move] = match choice {
                Choice::Same => &[Move::Shortcut, Move::FreezeUnfold(ConversionSide::Left), Move::PostponeUnfold(ConversionSide::Left)],
                Choice::Different => &[Move::FreezeUnfold(ConversionSide::Left), Move::PostponeUnfold(ConversionSide::Left)],
                Choice::Frozen { defined } => &[Move::Shortcut, Move::Unfold(defined)],
                Choice::Lambda { defined } => &[Move::FreezeEta(defined), Move::Unfold(defined)],
            };
            let children = match goal.next {
                Next::Combine(Combine::Biased(ref children)) if !matches!(choice, Choice::Frozen { .. }) => Some(children),
                Next::Combine(Combine::Either(ref children)) if matches!(choice, Choice::Frozen { .. }) => Some(children),
                _ => None,
            };
            self.spent.0 == before.saturating_add(u64::try_from(expected.len()).unwrap_or(u64::MAX))
                && children.is_some_and(|children| children.len() == expected.len()
                    && children.iter().zip(expected).all(|(child, expected)| self.processes.get(child.0).is_some_and(|process|
                        process.outcome == Outcome::Pending && matches!(process.work, Work::Goal(ref branch)
                            if branch.left == goal.left && branch.right == goal.right
                                && branch.depth == goal.depth && branch.frozen == goal.frozen && branch.chain == goal.chain
                                && branch.next == Next::Move(*expected)))))
        })
    )]
    fn choose(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        choice: Choice,
    ) -> Result<Turn, ConversionFault>
    {
        let (combination, moves) = choice.alternatives();
        let branches = u64::try_from(moves.len()).unwrap_or(u64::MAX);
        self.charge(StepCount(branches));
        let mut children = Vec::with_capacity(moves.len());
        for chosen in moves {
            let child = self.start_goal(Goal {
                left: goal.left,
                right: goal.right,
                depth: goal.depth,
                frozen: goal.frozen.clone(),
                chain: goal.chain.clone(),
                next: Next::Move(chosen),
            })?;
            self.depend(id, child)?;
            children.push(child);
        }
        goal.next = Next::Combine(match combination {
            | Combination::Biased => Combine::Biased(children),
            | Combination::Either => Combine::Either(children),
        });
        Ok(Turn::Wait)
    }

    /// Take an alternative's first move.
    ///
    /// # Specification
    /// - requires: both sides are in hand and the move suits them, as the
    ///   choice that started this goal guarantees.
    /// - ensures: one step charged; the shortcut records `ConstShortcut` and
    ///   decomposes the two spines, refuting at once when their shapes differ;
    ///   an unfolding records and unfolds; a frozen unfolding records `Freeze`,
    ///   freezes the head and unfolds the other side; a postponed unfolding
    ///   records `Postpone` for the other head and unfolds; a frozen
    ///   η-expansion records `Freeze`, freezes the head and η-expands it. An
    ///   unfolding that repeats one on its side's chain declines the goal.
    /// - provides: the moves the §6.1 and §6.2 alternatives start with.
    /// - fails: every fault the move raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the move raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the five moves are shortcut, unfolding, frozen
    ///   unfolding, postponed unfolding and frozen eta. Ordered decisions, the
    ///   kernel’s replay and cycle behavior distinguish the wrong side, an
    ///   omitted freeze/postponement, a shortcut that unfolds unnecessarily and
    ///   an uncharged move.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
    #[spec(
        captures: [before = self.spent.0],
        ensures: |ret| self.spent.0 == before.saturating_add(1)
            && (ret.is_err() || self.processes.get(id.0).is_some_and(|process| match ret {
                Ok(Turn::Done) => process.outcome != Outcome::Pending,
                Ok(Turn::Again | Turn::Wait) => process.outcome == Outcome::Pending,
                Err(_) => false,
            }))
    )]
    fn take(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        chosen: Move,
    ) -> Result<Turn, ConversionFault>
    {
        self.charge(StepCount::ONE);
        match chosen {
            | Move::Shortcut => {
                let left = self.neutral_of(pair.0)?;
                let right = self.neutral_of(pair.1)?;
                let constant = self.head_constant(left)?;
                self.derivations
                    .decide(id, ConversionDecision::ConstShortcut {
                        constant: TraceNode::Constant(constant),
                    })?;
                let spines = spine_subgoals(self.core, self.domain, left, right)?;
                match spines {
                    | Spines::Agree(subgoals) => {
                        self.decompose(id, goal, pair, subgoals, Collapse::Never)
                    },
                    | Spines::Disagree => {
                        self.answer(id, Settled::NotConvertible, &[])?;
                        Ok(Turn::Done)
                    },
                }
            },
            | Move::Unfold(side) => {
                let advance = self.unfold(id, goal, pair, side)?;
                self.advanced(id, advance)
            },
            | Move::FreezeUnfold(side) => {
                let constant = self.side_constant(pair, side)?;
                self.derivations.decide(id, ConversionDecision::Freeze {
                    constant: TraceNode::Constant(constant),
                    side,
                })?;
                goal.frozen.freeze(side, constant);
                let advance = self.unfold(id, goal, pair, other(side))?;
                self.advanced(id, advance)
            },
            | Move::PostponeUnfold(side) => {
                let postponed = self.side_constant(pair, other(side))?;
                self.derivations.decide(id, ConversionDecision::Postpone {
                    constant: TraceNode::Constant(postponed),
                })?;
                let advance = self.unfold(id, goal, pair, side)?;
                self.advanced(id, advance)
            },
            | Move::FreezeEta(side) => {
                let constant = self.side_constant(pair, side)?;
                self.derivations.decide(id, ConversionDecision::Freeze {
                    constant: TraceNode::Constant(constant),
                    side,
                })?;
                goal.frozen.freeze(side, constant);
                self.eta(id, goal, pair, side)?;
                Ok(Turn::Again)
            },
        }
    }

    /// The constant heading the neutral on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Scheduler::head_constant`] of the side's neutral.
    /// - provides: the read every constant move names its decision with.
    /// - fails: as [`Scheduler::neutral_of`] and [`Scheduler::head_constant`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::neutral_of`] and [`Scheduler::head_constant`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a side selects a constant-headed neutral rather than
    ///   its peer. The observer is the exact constant named by Freeze, Postpone
    ///   and the following reduction; two distinct definitions and a defined
    ///   function against eta separate swapped-side extraction from a correct
    ///   identifier.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    #[spec(
        ensures: |ret| ret.is_err() || ret.is_ok_and(|constant| {
                let selected = match side { ConversionSide::Left => pair.0, ConversionSide::Right => pair.1 };
                let neutral = match selected {
                    Glued::Value(value) => match self.domain.value(value) { Some(&DomainValue::Neutral { neutral, .. }) => Some(neutral), _ => None },
                    Glued::Computation(comp) => match self.domain.computation(comp) { Some(&DomainComp::Neutral { neutral, .. }) => Some(neutral), _ => None },
                };
                neutral.and_then(|id| self.domain.neutral(id)).is_some_and(|node| node.head() == NeutralHead::Constant(constant))
        })
    )]
    fn side_constant(
        &self,
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Result<ConstantIndex, ConversionFault>
    {
        let neutral = self.neutral_of(Self::side_of(pair, side))?;
        self.head_constant(neutral)
    }

    /// Read a goal's children and answer when the combinator can.
    ///
    /// # Specification
    /// - requires: the children were started by this goal.
    /// - ensures: a decomposition refutes at the first refuted child in subgoal
    ///   order, recording `NegativeSubgoal` with its position, and agrees once
    ///   every child agreed; a biased choice agrees on any agreeing child and
    ///   otherwise answers its last child's answer once it has one; an either
    ///   agrees on any agreeing child and refutes once all refuted. A decline
    ///   combines as the third value of Kleene's logic: a decomposition with no
    ///   refutation declines once every child answered and one declined; a
    ///   biased choice whose last child declined declines once no other child
    ///   can still agree; an either declines once every child answered, none
    ///   agreed and one declined. Decomposition and either take the first
    ///   decline's reason in child order; biased choice takes its authoritative
    ///   child's reason. Otherwise the goal waits. The children an answer rests
    ///   on are recorded as its derivation's continuation, and the others lose
    ///   this goal's need. The support an answer is read from is its winning
    ///   children for an acceptance, the refuted premise for a refuted
    ///   decomposition, and every alternative for a refuted choice.
    /// - provides: the three combinators.
    /// - fails: [`ConversionFault::MachineInvariant`] for a child that answered
    ///   a weak head, an empty choice, or a position past the subgoal ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the children are malformed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — conjunction, biased choice and either combine
    ///   pending, accepted, refuted and differently declined children,
    ///   including a decisive middle child and empty inputs. The root outcome
    ///   and resumed work distinguish wrong dominance, premature decline,
    ///   first-versus-authoritative decline reasons and a vacuous empty-choice
    ///   refutation; conjunction traces also expose the selected negative
    ///   premise.
    /// - witness: `machine::tests::combinators_preserve_answer_and_decline_precedence`
    /// - witness: `machine::tests::empty_choices_refuse_instead_of_producing_a_refutation`
    /// - witness: `machine::tests::a_refutation_outranks_a_decline`
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    #[spec(
        captures: [boundary = match combine {
            Combine::All { ref children, .. } => (true, false, children.len(), children.first().copied(), children.last().copied()),
            Combine::Biased(ref children) => (false, true, children.len(), children.first().copied(), children.last().copied()),
            Combine::Either(ref children) => (false, false, children.len(), children.first().copied(), children.last().copied()),
        }],
        ensures: |ret| {
            let (all, biased, count, first, last) = boundary;
            let outcome = self.processes.get(id.0).map(|process| process.outcome);
            let first = first.and_then(|child| self.processes.get(child.0)).map(|process| process.outcome);
            let last = last.and_then(|child| self.processes.get(child.0)).map(|process| process.outcome);
            if !all && count == 0 { ret == Err(ConversionFault::MachineInvariant) }
            else {
                (ret.is_err() || match ret {
                    Ok(Turn::Done) => outcome.is_some_and(|outcome| matches!(outcome, Outcome::Settled(_) | Outcome::Declined(_))),
                    Ok(Turn::Wait) => outcome == Some(Outcome::Pending) && match goal.next {
                        Next::Combine(Combine::All { .. }) => all,
                        Next::Combine(Combine::Biased(_)) => biased,
                        Next::Combine(Combine::Either(_)) => !all && !biased,
                        _ => false,
                    },
                    Ok(Turn::Again) | Err(_) => false,
                })
                    && (ret.is_err() || !all || count != 0 || outcome == Some(Outcome::Settled(Settled::Convertible)))
                    && (ret.is_err() || !matches!(outcome, Some(Outcome::Declined(_)))
                        || if biased { outcome == last }
                        else { !matches!(first, Some(Outcome::Declined(_))) || outcome == first })
                    && (ret.is_err() || !matches!((all, first),
                        (true, Some(Outcome::Settled(Settled::NotConvertible)))
                        | (false, Some(Outcome::Settled(Settled::Convertible))))
                        || (ret == Ok(Turn::Done) && outcome == first))
            }
        }
    )]
    fn combine(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        combine: Combine,
    ) -> Result<Turn, ConversionFault>
    {
        match combine {
            | Combine::All {
                pair,
                children,
                collapse,
            } => {
                let mut waiting = 0_usize;
                let mut declined = None;
                for (position, &child) in children.iter().enumerate() {
                    let answered = self.outcome(child)?;
                    match answered {
                        | Outcome::Settled(Settled::NotConvertible) => {
                            let position = u32::try_from(position)
                                .map_err(|_overflow| ConversionFault::MachineInvariant)?;
                            self.derivations
                                .decide(id, ConversionDecision::NegativeSubgoal {
                                    position: SubgoalPosition::from(position),
                                })?;
                            self.answer(id, Settled::NotConvertible, &[child])?;
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            return Ok(Turn::Done);
                        },
                        | Outcome::Settled(Settled::Convertible) => {},
                        | Outcome::Declined(reason) => {
                            declined.get_or_insert(reason);
                        },
                        | Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        | Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                    }
                }
                if waiting > 0_usize {
                    goal.next = Next::Combine(Combine::All {
                        pair,
                        children,
                        collapse,
                    });
                    return Ok(Turn::Wait);
                }
                if let Some(reason) = declined {
                    self.finish(id, Outcome::Declined(reason))?;
                    return Ok(Turn::Done);
                }
                self.answer(id, Settled::Convertible, &children)?;
                match collapse {
                    | Collapse::Allowed => self.derivations.agree_on(id, pair, children)?,
                    | Collapse::Never => self.derivations.rest_on(id, children)?,
                }
                Ok(Turn::Done)
            },
            | Combine::Biased(children) => {
                let Some((&last, rest)) = children.split_last()
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let mut waiting = 0_usize;
                for &child in rest {
                    let answered = self.outcome(child)?;
                    match answered {
                        | Outcome::Settled(Settled::Convertible) => {
                            self.answer(id, Settled::Convertible, &[child])?;
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            return Ok(Turn::Done);
                        },
                        | Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        | Outcome::Settled(Settled::NotConvertible) | Outcome::Declined(_) => {},
                        | Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                    }
                }
                let authoritative = self.outcome(last)?;
                match authoritative {
                    | Outcome::Settled(settled) => {
                        // An acceptance rests on the winning branch; a refusal
                        // on every branch, each of which had to fail.
                        let winner = [last];
                        let basis: &[ProcessId] = match settled {
                            | Settled::Convertible => &winner,
                            | Settled::NotConvertible => &children,
                        };
                        self.answer(id, settled, basis)?;
                        self.derivations.rest_on(id, Vec::from([last]))?;
                        Ok(Turn::Done)
                    },
                    | Outcome::Declined(_) if waiting == 0_usize => {
                        self.finish(id, authoritative)?;
                        Ok(Turn::Done)
                    },
                    | Outcome::Pending | Outcome::Declined(_) => {
                        goal.next = Next::Combine(Combine::Biased(children));
                        Ok(Turn::Wait)
                    },
                    | Outcome::Evaluated(_) => Err(ConversionFault::MachineInvariant),
                }
            },
            | Combine::Either(children) => {
                if children.is_empty() {
                    return Err(ConversionFault::MachineInvariant);
                }
                let mut refuted = 0_usize;
                let mut waiting = 0_usize;
                let mut declined = None;
                for &child in &children {
                    let answered = self.outcome(child)?;
                    match answered {
                        | Outcome::Settled(Settled::Convertible) => {
                            self.answer(id, Settled::Convertible, &[child])?;
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            return Ok(Turn::Done);
                        },
                        | Outcome::Settled(Settled::NotConvertible) => {
                            refuted = refuted.saturating_add(1_usize);
                        },
                        | Outcome::Declined(reason) => {
                            declined.get_or_insert(reason);
                        },
                        | Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        | Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                    }
                }
                if waiting > 0_usize {
                    goal.next = Next::Combine(Combine::Either(children));
                    return Ok(Turn::Wait);
                }
                if refuted == children.len() {
                    self.answer(id, Settled::NotConvertible, &children)?;
                    self.derivations.rest_on(id, children)?;
                    return Ok(Turn::Done);
                }
                let reason = declined.ok_or(ConversionFault::MachineInvariant)?;
                self.finish(id, Outcome::Declined(reason))?;
                Ok(Turn::Done)
            },
        }
    }

    /// The fresh variable at `level`, minted once per level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a rigid intuitionistic variable neutral at `level`, the same
    ///   node for every request at that level in this run.
    /// - provides: the variable every binder opened at one depth is read under,
    ///   so two goals opening binders at one depth compare one variable.
    /// - fails: [`ConversionFault::Domain`] when the domain refuses the node,
    ///   [`ConversionFault::MachineInvariant`] at the level ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — the domain refused the node.
    /// - [`ConversionFault::MachineInvariant`] — the level ceiling.
    ///
    /// # Termination
    /// - reason: the `while self.variables.len() <= index` loop below, which
    ///   mints the variables of every level up to `level` that no earlier
    ///   request reached, not recursion.
    /// - measure: `index + 1 - self.variables.len()`, which falls by one per
    ///   iteration because each pushes one variable.
    /// - boundedness: `index` is fixed on entry, at most the problem's depth
    ///   plus the binders the run has opened, so the loop mints at most that
    ///   many variables over the whole run.
    /// - input recursion: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh variable is cached by intuitionistic level,
    ///   with a rigid empty spine, and different opened levels must remain
    ///   different binders. The eta trace and two-level channel evaluation
    ///   observe the actual variable returned; using the wrong zone, adjacent
    ///   level or a shared variable for distinct levels changes them.
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    /// - witness: `machine::tests::opened_channels_preserve_distinct_binder_levels`
    #[spec(
        captures: [before = self.variables.len()],
        ensures: |ret| ret.as_ref().map_or(true, |value| {
            usize::try_from(u32::from(level)).is_ok_and(|index|
                self.variables.get(index) == Some(value)
                    && self.variables.len() == before.max(index.saturating_add(1)))
                && matches!(self.domain.value(*value), Some(&DomainValue::Neutral { neutral, face: TermFace::Reduced })
                    if self.domain.neutral(neutral).is_some_and(|node|
                        node.head() == (NeutralHead::Variable { zone: Zone::Intuitionistic, level })
                            && node.spine().is_empty() && node.unfolding() == Unfolding::Rigid))
        })
    )]
    fn variable(
        &mut self,
        level: BinderLevel,
    ) -> Result<DomainValueId, ConversionFault>
    {
        let index = usize::try_from(u32::from(level))
            .map_err(|_overflow| ConversionFault::MachineInvariant)?;
        while self.variables.len() <= index {
            let next = u32::try_from(self.variables.len())
                .map_err(|_overflow| ConversionFault::MachineInvariant)?;
            let head = NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level: BinderLevel::from(next),
            };
            let neutral = self
                .domain
                .neutral_node(head, Vec::new(), Unfolding::Rigid)
                .map_err(ConversionFault::Domain)?;
            let value = self
                .domain
                .value_neutral(neutral, TermFace::Reduced)
                .map_err(ConversionFault::Domain)?;
            self.variables.push(value);
        }
        self.variables
            .get(index)
            .copied()
            .ok_or(ConversionFault::MachineInvariant)
    }

    /// The channel evaluating the definition body at `entry`, minted once per
    /// distinct entry.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same channel for every request naming `entry` in this
    ///   run, evaluating the body the lowered chain holds for it.
    /// - provides: the skeleton granularity: one channel per distinct
    ///   subterm-table entry, in a dense side vector.
    /// - fails: [`ConversionFault::Evaluation`] with
    ///   [`EvalFault::DanglingTerm`] when the chain lowered no body for
    ///   `entry`, and [`ConversionFault::MachineInvariant`] for a granularity
    ///   stance no installed policy can hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Evaluation`] — no lowered body for `entry`.
    /// - [`ConversionFault::MachineInvariant`] — an uninstallable stance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one lowered body may belong to one definition or be
    ///   named by two definitions, while an entry with no lowering refuses.
    ///   Exact process counts and the missing-entry refusal distinguish
    ///   per-definition rather than per-body caching, repeated evaluation and
    ///   inventing a body for an absent entry.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::malformed_heads_and_channel_entries_are_refused`
    #[spec(
        captures: [cached = usize::try_from(u32::from(entry)).ok().and_then(|index| self.bodies.get(index)).copied(), processes = self.processes.len()],
        ensures: |ret| ret.as_ref().map_or(true, |channel| {
            usize::try_from(u32::from(entry)).ok().and_then(|index| self.bodies.get(index)) == Some(&BodyChannel::Minted(*channel))
                && self.processes.get(channel.0).is_some()
                && match cached { Some(BodyChannel::Minted(before)) => *channel == before && self.processes.len() == processes,
                    None | Some(BodyChannel::Unminted) => self.processes.len() == processes.saturating_add(1) }
        })
    )]
    fn body_channel(
        &mut self,
        entry: GlobalIndex,
        height: DefinitionHeight,
    ) -> Result<ProcessId, ConversionFault>
    {
        match self.settings.granularity().stance() {
            | GranularityStance::Skeleton => {},
            // The policy's constructor refuses this stance, so no installed
            // policy holds it; the arm answers a typed refusal rather than
            // standing in for a stance it does not implement.
            | GranularityStance::Spinal => return Err(ConversionFault::MachineInvariant),
        }
        let index = usize::try_from(u32::from(entry))
            .map_err(|_overflow| ConversionFault::MachineInvariant)?;
        if let Some(&BodyChannel::Minted(channel)) = self.bodies.get(index) {
            return Ok(channel);
        }
        let body = self
            .definitions
            .bodies()
            .get(&entry)
            .copied()
            .ok_or(ConversionFault::Evaluation(EvalFault::DanglingTerm))?;
        let evaluation = Evaluation::body(self.definitions, body);
        let share = self.share_at(height);
        let channel = self.start(
            Work::Channel(Channel::Running(evaluation)),
            Outcome::Pending,
            share,
        )?;
        if self.bodies.len() <= index {
            let length = index
                .checked_add(1_usize)
                .ok_or(ConversionFault::MachineInvariant)?;
            self.bodies.resize(length, BodyChannel::Unminted);
        }
        let slot = self
            .bodies
            .get_mut(index)
            .ok_or(ConversionFault::MachineInvariant)?;
        *slot = BodyChannel::Minted(channel);
        Ok(channel)
    }

    /// The channel giving a neutral's unfolding, minted once per neutral.
    ///
    /// # Specification
    /// - requires: `neutral` is headed by a constant with a body here.
    /// - ensures: for an empty spine, the body's own channel — or a channel
    ///   already answered with a forced body; otherwise a channel re-applying
    ///   the spine to the body once the body's channel answers. The same
    ///   channel for every request naming `neutral`.
    /// - provides: δ, shared: every goal unfolding one neutral reads one
    ///   evaluation.
    /// - fails: [`ConversionFault::MachineInvariant`] for a rigid neutral or a
    ///   body forced to a computation, and every fault minting a body channel
    ///   raises.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — nothing to unfold.
    /// - [`ConversionFault`] — as [`Scheduler::body_channel`] raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant neutral may have a bare or reapplied spine
    ///   and a forced or unforced value body; rigid, wrong-polarity and missing
    ///   heads refuse. Trace replay, shared-body counts and repeated
    ///   applications distinguish a lost spine, repeated evaluation and a body
    ///   channel mistaken for a reapplied one.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::unfolding_one_function_twice_is_not_a_cycle`
    /// - witness: `machine::tests::malformed_heads_and_channel_entries_are_refused`
    #[spec(
        captures: [entries = self.unfoldings.len(), processes = self.processes.len()],
        ensures: |ret| ret.as_ref().map_or(true, |channel| self.unfoldings.get(&neutral) == Some(channel)
            && self.processes.get(channel.0).is_some()
            && (self.unfoldings.len() != entries || self.processes.len() == processes)
            && self.unfoldings.len() <= entries.saturating_add(1))
    )]
    fn unfold_channel(
        &mut self,
        neutral: NeutralId,
    ) -> Result<ProcessId, ConversionFault>
    {
        if let Some(&channel) = self.unfoldings.get(&neutral) {
            return Ok(channel);
        }
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let unfolding = held.unfolding();
        let bare = held.spine().is_empty();
        let height = match held.head() {
            | NeutralHead::Constant(constant) => self.definitions.height(constant),
            | NeutralHead::Variable { .. } | NeutralHead::Module(_) => {
                return Err(ConversionFault::MachineInvariant);
            },
        };
        let share = self.share_at(height);
        let channel = match (unfolding, bare) {
            | (Unfolding::Rigid | Unfolding::Forced(Glued::Computation(_)), _) => {
                return Err(ConversionFault::MachineInvariant);
            },
            | (Unfolding::Forced(Glued::Value(body)), true) => {
                self.start(Work::Spent, Outcome::Evaluated(Glued::Value(body)), share)?
            },
            | (Unfolding::Forced(Glued::Value(body)), false) => {
                let evaluation = Evaluation::eliminate(self.definitions, body, held.spine());
                self.start(
                    Work::Channel(Channel::Running(evaluation)),
                    Outcome::Pending,
                    share,
                )?
            },
            | (Unfolding::Unforced(entry), true) => self.body_channel(entry, height)?,
            | (Unfolding::Unforced(entry), false) => {
                let body = self.body_channel(entry, height)?;
                let channel = self.start(
                    Work::Channel(Channel::Reapply { body, neutral }),
                    Outcome::Pending,
                    share,
                )?;
                self.depend(channel, body)?;
                channel
            },
        };
        self.unfoldings.insert(neutral, channel);
        Ok(channel)
    }

    /// The channel giving a closure's body opened under the fresh variable at
    /// `level`, minted once per closure and level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same channel for every request naming the pair.
    /// - provides: the binder-opening half of the lambda, bind and case rules.
    /// - fails: [`ConversionFault::Evaluation`] when `closure` does not
    ///   resolve, and as [`Scheduler::variable`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Evaluation`] — the closure does not resolve.
    /// - [`ConversionFault`] — as [`Scheduler::variable`] raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the opening key is the closure together with its
    ///   fresh level, not either component alone. Evaluated return values at
    ///   two levels and a repeated request observe capture preservation and
    ///   cache reuse; wrong-level sharing changes the neutral variable that eta
    ///   and binder comparison receive.
    /// - witness: `machine::tests::opened_channels_preserve_distinct_binder_levels`
    /// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
    #[spec(
        captures: [entries = self.openings.len(), processes = self.processes.len()],
        ensures: |ret| ret.as_ref().map_or(true, |channel| self.openings.get(&(closure, level)) == Some(channel)
            && self.processes.get(channel.0).is_some()
            && if self.openings.len() == entries { self.processes.len() == processes }
                else { self.openings.len() == entries.saturating_add(1) && self.processes.len() == processes.saturating_add(1) })
    )]
    fn open_channel(
        &mut self,
        closure: CompClosureId,
        level: BinderLevel,
    ) -> Result<ProcessId, ConversionFault>
    {
        if let Some(&channel) = self.openings.get(&(closure, level)) {
            return Ok(channel);
        }
        let variable = self.variable(level)?;
        let evaluation = Evaluation::enter(
            self.definitions,
            self.domain,
            closure,
            Bound::Variable(variable),
        )
        .map_err(ConversionFault::Evaluation)?;
        let share = self.share_at(DefinitionHeight::default());
        let channel = self.start(
            Work::Channel(Channel::Running(evaluation)),
            Outcome::Pending,
            share,
        )?;
        self.openings.insert((closure, level), channel);
        Ok(channel)
    }

    /// The channel giving a thunk's body, minted once per closure.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same channel for every request naming `closure`.
    /// - provides: the entering half of the force rules.
    /// - fails: [`ConversionFault::Evaluation`] when `closure` does not
    ///   resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Evaluation`] — the closure does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — entering a thunk supplies no binder and shares its
    ///   body channel by closure identity. Forced comparisons and a delayed
    ///   reuse of the same closures observe the returned computations and
    ///   completed-channel reuse; allocating a new channel for every force or
    ///   reusing a different closure changes those results.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::completed_premises_wake_a_later_decomposition`
    #[spec(
        captures: [entries = self.entries.len(), processes = self.processes.len()],
        ensures: |ret| ret.as_ref().map_or(true, |channel| self.entries.get(&closure) == Some(channel)
            && self.processes.get(channel.0).is_some()
            && if self.entries.len() == entries { self.processes.len() == processes }
                else { self.entries.len() == entries.saturating_add(1) && self.processes.len() == processes.saturating_add(1) })
    )]
    fn enter_channel(
        &mut self,
        closure: CompClosureId,
    ) -> Result<ProcessId, ConversionFault>
    {
        if let Some(&channel) = self.entries.get(&closure) {
            return Ok(channel);
        }
        let evaluation = Evaluation::enter(self.definitions, self.domain, closure, Bound::Nothing)
            .map_err(ConversionFault::Evaluation)?;
        let share = self.share_at(DefinitionHeight::default());
        let channel = self.start(
            Work::Channel(Channel::Running(evaluation)),
            Outcome::Pending,
            share,
        )?;
        self.entries.insert(closure, channel);
        Ok(channel)
    }
}

/// The binder level one past `level`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `level` plus one.
/// - provides: the depth a goal reaches by opening one binder.
/// - fails: [`ConversionFault::MachineInvariant`] at the level ceiling.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::MachineInvariant`] — the level ceiling.
///
/// # Adequacy
/// - hypothesis: L3 — opening a representable level increments it once, while
///   the maximum refuses before any binder allocation. Fresh-variable equality
///   in eta and the ceiling probe distinguish a reused level, wrapping
///   arithmetic and a late refusal after constructing a huge variable prefix.
/// - witness: `machine::tests::a_lambda_meets_a_defined_function_by_eta`
/// - witness: `machine::tests::binder_ceiling_is_refused_before_opening_or_eta_allocation`
#[spec(
    ensures: |ret| ret == u32::from(level).checked_add(1).map(BinderLevel::from)
        .ok_or(ConversionFault::MachineInvariant)
)]
fn deeper(level: BinderLevel) -> Result<BinderLevel, ConversionFault>
{
    let next = u32::from(level)
        .checked_add(1_u32)
        .ok_or(ConversionFault::MachineInvariant)?;
    Ok(BinderLevel::from(next))
}

#[cfg(test)]
mod tests
{
    mod trace_pairing;

    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_term::CompType;
    use gandr_core_term::CompTypeId;
    use gandr_core_term::Computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Sort;
    use gandr_core_term::Transparency;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueType;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_check_memo::CheckMemo;
    use gandr_kernel_check_memo::NullMemo;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    use gandr_kernel_conversion_trace::NullSink;
    use gandr_kernel_conversion_trace::SubgoalPosition;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_conversion_trace::TraceSink;
    use gandr_kernel_core::EngineClaim;
    use gandr_kernel_core::KernelVerdict;
    use gandr_kernel_core::ReplayBudget;
    use gandr_kernel_core::ReplayDecline;
    use gandr_kernel_core::ReplayNode;
    use gandr_kernel_core::ReplayRefusal;
    use gandr_kernel_core::ReplaySides;
    use gandr_kernel_core::TracePosition;
    use gandr_kernel_core::Unfoldable;
    use gandr_kernel_core::Unfoldings;
    use gandr_kernel_core::replay;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::TermArena;

    use super::DeclineReason;
    use super::MachineReport;
    use super::MachineSettings;
    use super::MachineVerdict;
    use super::Problem;
    use super::ProcessId;
    use super::StepBudget;
    use super::TraceNode;
    use super::decide;
    use crate::arena::DomainArena;
    use crate::eval::Definitions;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_computation;
    use crate::eval::eval_value;
    use crate::free::CoreTerm;
    use crate::measure::ShareCount;
    use crate::measure::SharingMeasure;
    use crate::overlay::Bound;
    use crate::overlay::CompGraft;
    use crate::overlay::CompNode;
    use crate::overlay::Overlay;
    use crate::overlay::OverlayId;
    use crate::overlay::ShareArity;
    use crate::overlay::ShareDistance;
    use crate::overlay::SharePosition;
    use crate::overlay::Sharing;
    use crate::overlay::ValueGraft;
    use crate::overlay::ValueNode;
    use crate::policy::DuplicationStance;
    use crate::policy::GranularityPolicy;
    use crate::policy::SchedulingPolicy;
    use crate::policy::SchedulingStance;
    use crate::resharing::GoalSupport;
    use crate::resharing::ResharingMemo;
    use crate::traced::TracedDuplication;

    /// A pair of core terms of one polarity, to be evaluated and compared.
    #[derive(Clone, Copy, Debug)]
    enum Sides
    {
        /// Two values.
        Values(ValueId, ValueId),
        /// Two computations.
        Computations(ComputationId, ComputationId),
    }

    /// A core arena and the definitions lowered into it.
    struct World
    {
        /// The terms.
        core: CoreArena,
        /// The definitions, constant `n` the `n`th admitted.
        chain: LoweredChain,
        /// The definitional environment, which seals nothing.
        environment: DefinitionalEnvironment,
        /// Every constant's body, at its admission position.
        bodies: Vec<ValueId>,
    }

    /// Which earlier definitions a fixture's definition declares it mentions.
    #[derive(Clone, Copy, Debug)]
    enum Mentions
    {
        /// None: every definition sits at height one.
        Nothing,
        /// The one admitted just before it: constant `n` sits at height `n +
        /// 1`.
        Previous,
    }

    impl World
    {
        /// Admit one manifest definition per `(entry, body)`, in order: the
        /// `n`th is the constant [`Name`] `n` names, its body stored under the
        /// table entry `entry` names.
        ///
        /// # Specification
        /// - requires: two definitions naming one entry name one body.
        /// - ensures: as [`World::admit`] over the entries the names give.
        /// - provides: the fixture every machine test over named constants runs
        ///   in.
        /// - panics: as [`World::admit`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — for coherent named entry/body fixtures, admission
        ///   order assigns constants while names choose shared table entries.
        ///   Observable unfolding traces and the one-body/two-definition
        ///   process count distinguish confusing a name with an admission
        ///   position, losing a body or duplicating a shared lowering.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
        #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(name, body))|
                    ret.bodies.get(position) == Some(&body)
                        && ret.chain.chain().entry(ConstantIndex::from(position)).is_some_and(|entry| entry.body() == name.entry())
                        && Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).bodies().get(&name.entry()) == Some(&body))
        )]
        fn new(
            core: CoreArena,
            bodies: &[(Name, ValueId)],
        ) -> Self
        {
            let entries: Vec<(GlobalIndex, ValueId)> = bodies
                .iter()
                .map(|&(name, body)| (name.entry(), body))
                .collect();
            Self::admit(core, &entries)
        }

        /// Admit one manifest definition per `(entry, body)`, in order: the
        /// `n`th is constant `n`, its body stored under table entry `entry`.
        ///
        /// # Specification
        /// - requires: two definitions naming one entry name one body.
        /// - ensures: every constant admitted unfolds to its body; every other
        ///   constant is rigid.
        /// - provides: the fixture every machine test runs in.
        /// - panics: when the chain refuses a definition, which no fixture
        ///   provokes.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — coherent table entries are admitted without
        ///   mentions, including repeated entries and recursive bodies. The
        ///   observer is the resulting comparison trace and exact shared-body
        ///   count; wrong ordinal assignment, accidental dependency heights or
        ///   per-definition lowering change those observations.
        /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
        /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
        /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
        #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(entry, body))|
                    ret.bodies.get(position) == Some(&body)
                        && ret.chain.chain().entry(ConstantIndex::from(position)).is_some_and(|definition| definition.body() == entry)
                        && Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).bodies().get(&entry) == Some(&body)
                        && u32::from(Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).height(ConstantIndex::from(position))) == 1)
        )]
        fn admit(
            core: CoreArena,
            bodies: &[(GlobalIndex, ValueId)],
        ) -> Self
        {
            Self::chained(core, bodies, Mentions::Nothing)
        }

        /// Admit one manifest definition per `(entry, body)` as
        /// [`World::admit`] does, but with each definition declaring a
        /// mention of the one before it, so constant `n` sits at height
        /// `n + 1`.
        ///
        /// # Specification
        /// - requires: as [`World::admit`].
        /// - ensures: as [`World::admit`], with the heights rising by one per
        ///   position.
        /// - provides: the fixture whose heights a weighted schedule reads.
        /// - panics: as [`World::admit`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a positional chain mentions its immediate
        ///   predecessor, so unequal heights remain observable on either side
        ///   of a comparison. The height probe and fair/weighted divergence
        ///   fixture distinguish flat heights, wrong predecessor references and
        ///   a shifted admission order.
        /// - witness: `machine::tests::head_height_is_symmetric_and_nonconstants_stay_at_the_floor`
        /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
        #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(entry, body))|
                    ret.bodies.get(position) == Some(&body)
                        && Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).bodies().get(&entry) == Some(&body)
                        && usize::try_from(u32::from(Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).height(ConstantIndex::from(position)))).ok() == position.checked_add(1))
        )]
        fn stacked(
            core: CoreArena,
            bodies: &[(GlobalIndex, ValueId)],
        ) -> Self
        {
            Self::chained(core, bodies, Mentions::Previous)
        }

        /// Admit one manifest definition per `(entry, body)`, each declaring
        /// the mentions `mentions` names.
        ///
        /// # Specification
        /// - requires: as [`World::admit`].
        /// - ensures: as [`World::admit`], at the heights the mentions give.
        /// - provides: the one admission both fixtures share.
        /// - panics: as [`World::admit`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the input is a coherent ordered list of table
        ///   entries, with either no mentions or only the immediate
        ///   predecessor. The observer is exact body sharing and unequal head
        ///   heights; swapped bodies, ordinal/entry confusion and the wrong
        ///   mention policy alter counts, traces or weighted scheduling.
        /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
        /// - witness: `machine::tests::head_height_is_symmetric_and_nonconstants_stay_at_the_floor`
        /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
        #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && ret.chain.chain().entries().len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(entry, body))| {
                    let definitions = Definitions::new(&ret.chain, &ret.environment, ret.environment.root());
                    ret.bodies.get(position) == Some(&body) && definitions.bodies().get(&entry) == Some(&body)
                        && ret.chain.chain().entry(ConstantIndex::from(position)).is_some_and(|definition| definition.body() == entry)
                        && usize::try_from(u32::from(definitions.height(ConstantIndex::from(position)))).ok()
                            == match mentions { Mentions::Nothing => Some(1), Mentions::Previous => position.checked_add(1) }
                })
        )]
        fn chained(
            core: CoreArena,
            bodies: &[(GlobalIndex, ValueId)],
            mentions: Mentions,
        ) -> Self
        {
            let mut chain = DefinitionChain::new();
            for (position, &(entry, _)) in bodies.iter().enumerate() {
                let previous = match (mentions, position.checked_sub(1)) {
                    | (Mentions::Previous, Some(previous)) => {
                        Vec::from([ConstantIndex::from(previous)])
                    },
                    | (Mentions::Nothing, _) | (Mentions::Previous, None) => Vec::new(),
                };
                let defined = chain.define(
                    ConstantIndex::from(position),
                    entry,
                    Transparency::Manifest,
                    &previous,
                );
                assert!(defined.is_ok(), "fixtures admit constants in order");
            }
            let Ok(chain) = LoweredChain::lower(chain, |entry| {
                bodies
                    .get(usize::from(entry.constant()))
                    .map(|&(_, body)| body)
                    .ok_or_else(|| entry.constant())
            })
            else {
                panic!("every admitted constant has a body");
            };
            Self {
                core,
                chain,
                environment: DefinitionalEnvironment::new(),
                bodies: bodies.iter().map(|&(_, body)| body).collect(),
            }
        }

        /// Evaluate `sides` into a fresh domain and decide them under the
        /// default settings.
        ///
        /// # Specification
        /// - requires: both sides are closed.
        /// - ensures: as [`World::run_under`] with the default settings.
        /// - provides: the entry every machine test with no settings of its own
        ///   goes through.
        /// - panics: as [`World::run_under`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — closed catalogue and ladder sides that evaluate
        ///   within the fixture fuel are run from fresh domains. Verdict,
        ///   process and derivation counts separate stale run state, a lost
        ///   definitive answer and recording that changes the comparison; the
        ///   same inputs are checked with recording off and on.
        /// - witness: `machine::tests::recording_does_not_move_the_verdict`
        /// - witness: `machine::tests::the_sink_off_run_keeps_no_derivation`
        /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
        #[spec(
            ensures: |ret| usize::from(ret.derivations()) == if matches!(S::ACTIVITY, super::SinkActivity::Active) {
                usize::from(ret.processes())
            } else { 0 }
                && (usize::from(ret.processes()) != 0
                    || (u64::from(ret.steps()) == 0 && !matches!(ret.verdict(), MachineVerdict::Declined(_))))
        )]
        fn run<S>(
            &self,
            sides: Sides,
            sink: &mut S,
        ) -> MachineReport
        where
            S: TraceSink<TraceNode>,
        {
            self.run_under(MachineSettings::default(), sides, sink)
        }

        /// Evaluate `sides` into a fresh domain and decide them under
        /// `settings`, re-sharing through the engine path's memo.
        ///
        /// # Specification
        /// - requires: both sides are closed.
        /// - ensures: as [`World::run_with`] at [`ResharingMemo`].
        /// - provides: the entry every machine test with settings of its own
        ///   goes through.
        /// - panics: as [`World::run_with`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — closed sides with bounded weak-head evaluation
        ///   are compared under caller-supplied scheduling and step budgets.
        ///   The observed verdict and trace distinguish ignoring the budget,
        ///   ignoring the stance and mistaking a decline for a refutation.
        /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
        /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
        /// - witness: `machine::tests::recording_does_not_move_the_verdict`
        #[spec(
            ensures: |ret| usize::from(ret.derivations()) == if matches!(S::ACTIVITY, super::SinkActivity::Active) {
                usize::from(ret.processes())
            } else { 0 }
                && (usize::from(ret.processes()) != 0
                    || (u64::from(ret.steps()) == 0 && !matches!(ret.verdict(), MachineVerdict::Declined(_))))
        )]
        fn run_under<S>(
            &self,
            settings: MachineSettings,
            sides: Sides,
            sink: &mut S,
        ) -> MachineReport
        where
            S: TraceSink<TraceNode>,
        {
            self.run_with::<S, ResharingMemo>(settings, sides, sink)
        }

        /// Evaluate `sides` into a fresh domain and decide them under
        /// `settings`, re-sharing through a memo of type `M`.
        ///
        /// # Specification
        /// - requires: both sides are closed.
        /// - ensures: the machine's report.
        /// - provides: the one entry every machine test goes through, and the
        ///   one the memo differential instantiates twice.
        /// - panics: when evaluation or the machine refuses, which no fixture
        ///   provokes.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the domain is closed fixture sides with weak
        ///   heads obtainable within the fixed fuel, under either a run-local
        ///   sharing memo or the null memo. Verdict, process and support-edge
        ///   counts distinguish stale domains, lost sharing and accounting
        ///   retained in a memoless run; a genuine shared wait cycle may
        ///   decline differently from its unrolled reference.
        /// - witness: `machine::tests::the_memo_never_moves_a_verdict`
        /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
        /// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
        /// - witness: `machine::tests::edges_per_revision_grow_with_the_distinct_goals`
        #[spec(
            ensures: |ret| (usize::from(ret.derivations()) == if matches!(S::ACTIVITY, super::SinkActivity::Active) {
                usize::from(ret.processes())
            } else { 0 }
                && (usize::from(ret.processes()) != 0
                    || (u64::from(ret.steps()) == 0 && !matches!(ret.verdict(), MachineVerdict::Declined(_)))))
                && (matches!(M::ACTIVITY, super::MemoActivity::Active) || ret.edges() == super::SupportEdges::default())
        )]
        fn run_with<S, M>(
            &self,
            settings: MachineSettings,
            sides: Sides,
            sink: &mut S,
        ) -> MachineReport
        where
            S: TraceSink<TraceNode>,
            M: CheckMemo<GoalSupport, ProcessId> + Default,
        {
            let definitions =
                Definitions::new(&self.chain, &self.environment, self.environment.root());
            let mut domain = DomainArena::new();
            let fuel = Fuel::from(4_096_u32);
            let problem = match sides {
                | Sides::Values(left, right) => {
                    let left = eval_value(&self.core, &mut domain, definitions, fuel, left)
                        .expect("the left side evaluates");
                    let right = eval_value(&self.core, &mut domain, definitions, fuel, right)
                        .expect("the right side evaluates");
                    Problem::values(left, right)
                },
                | Sides::Computations(left, right) => {
                    let left = eval_computation(&self.core, &mut domain, definitions, fuel, left)
                        .expect("the left side evaluates");
                    let right = eval_computation(&self.core, &mut domain, definitions, fuel, right)
                        .expect("the right side evaluates");
                    Problem::computations(left, right)
                },
            };
            decide::<S, M>(
                &self.core,
                &mut domain,
                definitions,
                settings,
                problem,
                sink,
            )
            .expect("the machine answers every fixture")
        }

        /// Decide `sides` and keep the trace.
        ///
        /// # Specification
        /// - requires: as [`World::run`].
        /// - ensures: the verdict and the decisions recorded, in order.
        /// - provides: the trace every decision-level assertion reads.
        /// - panics: as [`World::run`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — closed fixtures may produce either verdict or
        ///   decline on a cycle or unresolved code. The observer is the exact
        ///   ordered trace and the empty conversion derivation on decline;
        ///   eager emission of speculative branches, wrong-side decisions and a
        ///   decline emitted as evidence change these witnesses.
        /// - witness: `machine::tests::a_refutation_outranks_a_decline`
        /// - witness: `machine::tests::codes_that_could_unfold_inside_are_declined`
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        #[spec(
            ensures: |ret| !matches!(ret.0, MachineVerdict::Declined(_)) || ret.1.is_empty()
        )]
        fn traced(
            &self,
            sides: Sides,
        ) -> (MachineVerdict, Vec<ConversionDecision<TraceNode>>)
        {
            let mut log = TraceLog::new();
            let report = self.run(sides, &mut log);
            (report.verdict(), log.decisions().copied().collect())
        }

        /// Replay `decisions` for `sides` in the kernel, against the claim
        /// `verdict` makes.
        ///
        /// # Specification
        /// - requires: `sides` lie in this world's arena.
        /// - ensures: the kernel's verdict over a translation of the world's
        ///   terms and bodies, every admitted constant unfoldable and every
        ///   other one opaque.
        /// - provides: the end-to-end check every replay test runs.
        /// - panics: as [`Kernel::translate`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — supported intuitionistic fixtures are translated
        ///   independently, and the supplied trace may be genuine or have a
        ///   changed branch decision. The observer is kernel agreement, a named
        ///   refusal for the tampering, or an engine-decline result; trusting
        ///   the claim or treating a decline/refusal as the opposite verdict
        ///   changes these outcomes.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
        #[spec(
            ensures: |ret| (!matches!(verdict, MachineVerdict::Declined(_))
                || ret == KernelVerdict::Declined(ReplayDecline::EngineDeclined))
                && (ret != KernelVerdict::Convertible || verdict == MachineVerdict::Convertible)
                && (ret != KernelVerdict::NotConvertible || verdict == MachineVerdict::NotConvertible)
        )]
        fn replayed(
            &self,
            sides: Sides,
            verdict: MachineVerdict,
            decisions: &[ConversionDecision<TraceNode>],
        ) -> KernelVerdict
        {
            let mut kernel = Kernel::default();
            let mut bodies = Vec::new();
            for &body in &self.bodies {
                bodies.push(Unfoldable::Body(kernel.value(&self.core, body)));
            }
            let sides = match sides {
                | Sides::Values(left, right) => ReplaySides::Values(
                    kernel.value(&self.core, left),
                    kernel.value(&self.core, right),
                ),
                | Sides::Computations(left, right) => ReplaySides::Computations(
                    kernel.computation(&self.core, left),
                    kernel.computation(&self.core, right),
                ),
            };
            let claim = match verdict {
                | MachineVerdict::Convertible => EngineClaim::Convertible,
                | MachineVerdict::NotConvertible => EngineClaim::NotConvertible,
                | MachineVerdict::Declined(_) => EngineClaim::Declined,
            };
            replay(
                &mut kernel.arena,
                &Unfoldings::new(bodies),
                sides,
                claim,
                decisions.iter().map(|&decision| kernel_decision(decision)),
                ReplayBudget::DEFAULT,
            )
        }

        /// Lift each side into an overlay sharing every node it reaches along
        /// two edges, evaluate both under the spinal stance into a fresh
        /// domain over a copy of the world's arena, and decide them under
        /// `settings` through the installation's recording sink.
        ///
        /// # Specification
        /// - requires: both sides are closed.
        /// - ensures: the machine's report and the decisions the bound sink
        ///   recorded, in order.
        /// - provides: the spinal run every certification test replays.
        /// - panics: when installation, evaluation or the machine refuses,
        ///   which no fixture provokes.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — supported closed value and computation fixtures
        ///   are lifted and evaluated with recorded spinal duplication before
        ///   conversion. Kernel agreement on both verdicts and on a
        ///   schedule-induced decline distinguishes changed denotation,
        ///   misplaced shares and partial duplication evidence mistaken for a
        ///   conversion verdict.
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::an_unlucky_spinal_schedule_declines_and_the_kernel_with_it`
        #[spec(
            ensures: |ret| usize::from(ret.0.derivations()) == usize::from(ret.0.processes())
                && (usize::from(ret.0.processes()) != 0
                    || (u64::from(ret.0.steps()) == 0 && !matches!(ret.0.verdict(), MachineVerdict::Declined(_))))
        )]
        fn spinal(
            &self,
            settings: MachineSettings,
            sides: Sides,
        ) -> (MachineReport, Vec<ConversionDecision<TraceNode>>)
        {
            let definitions =
                Definitions::new(&self.chain, &self.environment, self.environment.root());
            let mut core = self.core.clone();
            let mut domain = DomainArena::new();
            let fuel = Fuel::from(4_096_u32);
            let mut log = TraceLog::new();
            let report = {
                let mut spinal = TracedDuplication::install(DuplicationStance::Spinal, &mut log)
                    .expect("a recording sink carries the spinal stance");
                let problem = match sides {
                    | Sides::Values(left, right) => {
                        let [left, right] = [left, right].map(|side| {
                            let (mut overlay, root) = lifted(&self.core, CoreTerm::Value(side));
                            let OverlayId::Value(root) = root
                            else {
                                panic!("a value lifts to a value");
                            };
                            spinal
                                .eval_overlay_value(
                                    &mut overlay,
                                    &mut core,
                                    &mut domain,
                                    definitions,
                                    fuel,
                                    root,
                                )
                                .expect("the side evaluates under the spinal stance")
                                .0
                        });
                        Problem::values(left, right)
                    },
                    | Sides::Computations(left, right) => {
                        let [left, right] = [left, right].map(|side| {
                            let (mut overlay, root) =
                                lifted(&self.core, CoreTerm::Computation(side));
                            let OverlayId::Computation(root) = root
                            else {
                                panic!("a computation lifts to a computation");
                            };
                            spinal
                                .eval_overlay_computation(
                                    &mut overlay,
                                    &mut core,
                                    &mut domain,
                                    definitions,
                                    fuel,
                                    root,
                                )
                                .expect("the side evaluates under the spinal stance")
                                .0
                        });
                        Problem::computations(left, right)
                    },
                };
                spinal
                    .decide::<ResharingMemo>(&core, &mut domain, definitions, settings, problem)
                    .expect("the machine answers every fixture")
            };
            (report, log.decisions().copied().collect())
        }

        /// The shares each side's lifted overlay holds.
        ///
        /// # Specification
        /// - requires: both sides lie in this world's arena.
        /// - ensures: the share count of the left side's lifted overlay, then
        ///   the right side's.
        /// - provides: the check that a certification test exercised sharing.
        /// - panics: when a lifted overlay does not measure, which a fixture
        ///   this small never provokes.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — supported acyclic term fixtures include a leaf
        ///   and distinct arena nodes for equal nested pairs. Exact counts of
        ///   zero and two shared legs, plus erasure to the original tree,
        ///   distinguish pointer-only sharing, missing inner shares and a
        ///   non-share node counted as a share.
        /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        #[spec(
            ensures: |ret| {
             let roots = match sides { Sides::Values(a,b) => [CoreTerm::Value(a),CoreTerm::Value(b)], Sides::Computations(a,b) => [CoreTerm::Computation(a),CoreTerm::Computation(b)] };
             (roots[0] != roots[1] || ret[0] == ret[1]) && roots.into_iter().zip(ret).all(|(root,count)|
                !matches!(root, CoreTerm::Value(id) if matches!(self.core.value(id), Some(Value::Unit | Value::Variable{..} | Value::Constant(_) | Value::Literal(_)))) || u64::from(count) == 0)
            }
        )]
        fn shares(
            &self,
            sides: Sides,
        ) -> [ShareCount; 2]
        {
            let roots = match sides {
                | Sides::Values(left, right) => [CoreTerm::Value(left), CoreTerm::Value(right)],
                | Sides::Computations(left, right) => {
                    [CoreTerm::Computation(left), CoreTerm::Computation(right)]
                },
            };
            roots.map(|side| {
                let (overlay, root) = lifted(&self.core, side);
                SharingMeasure::of(&overlay, root)
                    .expect("a lifted side measures")
                    .shares()
            })
        }
    }

    /// A share's place in a lifted overlay's nest, outermost first; read as a
    /// count, the shares around a lifted leg or body.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct Nest(usize);

    /// One step of a walk over a core term.
    #[derive(Clone, Copy, Debug)]
    enum Lifting
    {
        /// Visit a node, or queue its children.
        Enter(CoreTerm),
        /// Finish a node once its children are done.
        Exit(CoreTerm),
    }

    /// The children of the core node `node`, left to right.
    ///
    /// # Specification
    /// - requires: `node` resolves in `core`.
    /// - ensures: each child the former names, in the order erasure mints them.
    /// - provides: the one reading of a core former the lifting walks share.
    /// - panics: when `node` does not resolve, which the requirement excludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — resolved term formers are observed through lifted
    ///   erasure and independent kernel replay. Ordered mixed-family
    ///   application, bind and case children distinguish omitted, swapped or
    ///   wrong-family edges; the leaf and nested-pair witness also exercises
    ///   zero, one and repeated children.
    /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
    #[spec(
        ensures: |ret| match node {
         CoreTerm::Value(id) => core.value(id).is_some_and(|value| match *value {
          Value::Constructor {ref fields,..} => ret.iter().copied().eq(fields.iter().copied().map(CoreTerm::Value)),
          Value::Record(ref fields) => ret.iter().copied().eq(fields.values().copied().map(CoreTerm::Value)),
          Value::PathRefl(code) => ret.as_slice() == [CoreTerm::Value(code)],
          Value::PathProduct(first, second) => ret.as_slice() == [CoreTerm::Value(first), CoreTerm::Value(second)],
          Value::PathEquiv { forward, backward, .. } => ret.as_slice() == [CoreTerm::Value(forward), CoreTerm::Value(backward)],
          Value::Pair(a,b) | Value::StaticApplication(a,b) => ret.as_slice() == [CoreTerm::Value(a),CoreTerm::Value(b)],
          Value::StaticLambda(body) | Value::Injection(_,body) | Value::Lift{body,..} => ret.as_slice() == [CoreTerm::Value(body)],
          Value::Thunk(body) => ret.as_slice() == [CoreTerm::Computation(body)],
          Value::Primitive { .. } | Value::Variable{..} | Value::Constant(_) | Value::Unit | Value::Literal(_) | Value::Quote(_) | Value::QuoteComputation(_) => ret.is_empty(),
         }),
         CoreTerm::Computation(id) => core.computation(id).is_some_and(|computation| match *computation {
          Computation::DataCase {scrutinee,ref branches,..} => ret.iter().copied().eq(core::iter::once(CoreTerm::Value(scrutinee)).chain(branches.iter().copied().map(CoreTerm::Computation))),
          Computation::RecordProjection(record,_) => ret.as_slice() == [CoreTerm::Value(record)],
          Computation::Primitive { arguments, .. } => ret.iter().copied().eq(arguments.iter().copied().map(CoreTerm::Value)),
          Computation::Transport(path, value) => ret.as_slice() == [CoreTerm::Value(path), CoreTerm::Value(value)],
          Computation::Lambda(body) => ret.as_slice() == [CoreTerm::Computation(body)],
          Computation::Application(head,arg) => ret.as_slice() == [CoreTerm::Computation(head),CoreTerm::Value(arg)],
          Computation::Return(value) | Computation::Force(value) => ret.as_slice() == [CoreTerm::Value(value)],
          Computation::Bind(bound,body) => ret.as_slice() == [CoreTerm::Computation(bound),CoreTerm::Computation(body)],
          Computation::Case{scrutinee,on_left,on_right} => ret.as_slice() == [CoreTerm::Value(scrutinee),CoreTerm::Computation(on_left),CoreTerm::Computation(on_right)],
         }),
        }
    )]
    fn core_children(
        core: &CoreArena,
        node: CoreTerm,
    ) -> Vec<CoreTerm>
    {
        match node {
            | CoreTerm::Value(id) => match *core.value(id).expect("a reached value resolves") {
                | Value::Constructor { ref fields, .. } => {
                    fields.iter().copied().map(CoreTerm::Value).collect()
                },
                | Value::Record(ref fields) => {
                    fields.values().copied().map(CoreTerm::Value).collect()
                },
                | Value::Primitive { .. }
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Unit
                | Value::Literal(_)
                | Value::Quote(_)
                | Value::QuoteComputation(_) => Vec::new(),
                | Value::PathRefl(code) => Vec::from([CoreTerm::Value(code)]),
                | Value::PathEquiv {
                    forward, backward, ..
                } => Vec::from([CoreTerm::Value(forward), CoreTerm::Value(backward)]),
                | Value::PathProduct(first, second)
                | Value::Pair(first, second)
                | Value::StaticApplication(first, second) => {
                    Vec::from([CoreTerm::Value(first), CoreTerm::Value(second)])
                },
                | Value::StaticLambda(body) => Vec::from([CoreTerm::Value(body)]),
                | Value::Injection(_, body) | Value::Lift { body, .. } => {
                    Vec::from([CoreTerm::Value(body)])
                },
                | Value::Thunk(body) => Vec::from([CoreTerm::Computation(body)]),
            },
            | CoreTerm::Computation(id) => {
                match *core
                    .computation(id)
                    .expect("a reached computation resolves")
                {
                    | Computation::DataCase {
                        scrutinee,
                        ref branches,
                        ..
                    } => core::iter::once(CoreTerm::Value(scrutinee))
                        .chain(branches.iter().copied().map(CoreTerm::Computation))
                        .collect(),
                    | Computation::RecordProjection(record, _) => {
                        Vec::from([CoreTerm::Value(record)])
                    },
                    | Computation::Primitive { arguments, .. } => {
                        arguments.iter().copied().map(CoreTerm::Value).collect()
                    },
                    | Computation::Transport(path, value) => {
                        Vec::from([CoreTerm::Value(path), CoreTerm::Value(value)])
                    },
                    | Computation::Lambda(body) => Vec::from([CoreTerm::Computation(body)]),
                    | Computation::Application(head, argument) => {
                        Vec::from([CoreTerm::Computation(head), CoreTerm::Value(argument)])
                    },
                    | Computation::Return(value) | Computation::Force(value) => {
                        Vec::from([CoreTerm::Value(value)])
                    },
                    | Computation::Bind(bound, body) => {
                        Vec::from([CoreTerm::Computation(bound), CoreTerm::Computation(body)])
                    },
                    | Computation::Case {
                        scrutinee,
                        on_left,
                        on_right,
                    } => Vec::from([
                        CoreTerm::Value(scrutinee),
                        CoreTerm::Computation(on_left),
                        CoreTerm::Computation(on_right),
                    ]),
                }
            },
        }
    }

    /// Each node `root` reaches in `core`, mapped to the first node of equal
    /// structure the walk completed.
    ///
    /// # Specification
    /// - requires: `root` resolves in `core`.
    /// - ensures: a representative per reached term node, equal as a tree with
    ///   quoted type ids opaque; equal trees share a representative.
    /// - provides: the hash-consing the lifter shares repeated subterms by.
    /// - panics: when a reached node does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite resolved term DAGs are compared structurally,
    ///   with quoted type ids kept opaque. The observer is exact shared-leg
    ///   count and the erased tree; retaining nominally distinct equal pairs,
    ///   merging unlike formers or returning non-idempotent representatives
    ///   changes these observations.
    /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
    #[spec(
        ensures: |ret| ret.contains_key(&root) && ret.iter().all(|(node,representative)| {
         ret.get(representative) == Some(representative) && match (*node,*representative) {
         (CoreTerm::Value(node),CoreTerm::Value(representative)) => core.value(node).is_some() && core.value(representative).is_some(),
         (CoreTerm::Computation(node),CoreTerm::Computation(representative)) => core.computation(node).is_some() && core.computation(representative).is_some(),
         _ => false,
         }
        })
    )]
    fn canonical(
        core: &CoreArena,
        root: CoreTerm,
    ) -> BTreeMap<CoreTerm, CoreTerm>
    {
        let mut canon: BTreeMap<CoreTerm, CoreTerm> = BTreeMap::new();
        let mut values: Vec<(Value, CoreTerm)> = Vec::new();
        let mut computations: Vec<(Computation, CoreTerm)> = Vec::new();
        let mut walk = Vec::from([Lifting::Enter(root)]);
        while let Some(step) = walk.pop() {
            match step {
                | Lifting::Enter(node) => {
                    if canon.contains_key(&node) {
                        continue;
                    }
                    walk.push(Lifting::Exit(node));
                    for child in core_children(core, node).into_iter().rev() {
                        walk.push(Lifting::Enter(child));
                    }
                },
                | Lifting::Exit(node) => {
                    if canon.contains_key(&node) {
                        continue;
                    }
                    let value = |id: ValueId| match canon[&CoreTerm::Value(id)] {
                        | CoreTerm::Value(id) => id,
                        | CoreTerm::Computation(_) => panic!("a value is represented by a value"),
                    };
                    let computation = |id: ComputationId| match canon[&CoreTerm::Computation(id)] {
                        | CoreTerm::Computation(id) => id,
                        | CoreTerm::Value(_) => {
                            panic!("a computation is represented by a computation")
                        },
                    };
                    let representative = match node {
                        | CoreTerm::Value(id) => {
                            let key =
                                match core.value(id).expect("a reached value resolves").clone() {
                                    | Value::Constructor {
                                        datatype,
                                        tag,
                                        mut fields,
                                    } => {
                                        for field in &mut fields {
                                            *field = value(*field);
                                        }
                                        Value::Constructor {
                                            datatype,
                                            tag,
                                            fields,
                                        }
                                    },
                                    | Value::Record(mut fields) => {
                                        for field in fields.values_mut() {
                                            *field = value(*field);
                                        }
                                        Value::Record(fields)
                                    },
                                    | value @ Value::Primitive { .. } => value,
                                    | Value::PathRefl(code) => Value::PathRefl(value(code)),
                                    | Value::PathProduct(first, second) => {
                                        Value::PathProduct(value(first), value(second))
                                    },
                                    | Value::PathEquiv {
                                        path_type,
                                        forward,
                                        backward,
                                        evidence,
                                    } => Value::PathEquiv {
                                        path_type,
                                        forward: value(forward),
                                        backward: value(backward),
                                        evidence,
                                    },
                                    | Value::Pair(first, second) => {
                                        Value::Pair(value(first), value(second))
                                    },
                                    | Value::Injection(side, body) => {
                                        Value::Injection(side, value(body))
                                    },
                                    | Value::Thunk(body) => Value::Thunk(computation(body)),
                                    | Value::StaticLambda(body) => Value::StaticLambda(value(body)),
                                    | Value::StaticApplication(head, argument) => {
                                        Value::StaticApplication(value(head), value(argument))
                                    },
                                    | Value::Lift { target, body } => Value::Lift {
                                        target,
                                        body: value(body),
                                    },
                                    | leaf @ (Value::Variable { .. }
                                    | Value::Constant(_)
                                    | Value::Unit
                                    | Value::Literal(_)
                                    | Value::Quote(_)
                                    | Value::QuoteComputation(_)) => leaf,
                                };
                            match values.iter().find(|entry| entry.0 == key) {
                                | Some(&(_, representative)) => representative,
                                | None => {
                                    values.push((key, node));
                                    node
                                },
                            }
                        },
                        | CoreTerm::Computation(id) => {
                            let key = match *core
                                .computation(id)
                                .expect("a reached computation resolves")
                            {
                                | Computation::DataCase {
                                    scrutinee,
                                    motive,
                                    ref branches,
                                } => Computation::DataCase {
                                    scrutinee: value(scrutinee),
                                    motive,
                                    branches: branches
                                        .iter()
                                        .map(|branch| computation(*branch))
                                        .collect(),
                                },
                                | Computation::RecordProjection(record, ref label) => {
                                    Computation::RecordProjection(value(record), label.clone())
                                },
                                | Computation::Primitive {
                                    primitive,
                                    mut arguments,
                                } => {
                                    for argument in arguments.iter_mut() {
                                        *argument = value(*argument);
                                    }
                                    Computation::Primitive {
                                        primitive,
                                        arguments,
                                    }
                                },
                                | Computation::Transport(path, argument) => {
                                    Computation::Transport(value(path), value(argument))
                                },
                                | Computation::Lambda(body) => {
                                    Computation::Lambda(computation(body))
                                },
                                | Computation::Application(head, argument) => {
                                    Computation::Application(computation(head), value(argument))
                                },
                                | Computation::Return(returned) => {
                                    Computation::Return(value(returned))
                                },
                                | Computation::Force(forced) => Computation::Force(value(forced)),
                                | Computation::Bind(bound, body) => {
                                    Computation::Bind(computation(bound), computation(body))
                                },
                                | Computation::Case {
                                    scrutinee,
                                    on_left,
                                    on_right,
                                } => Computation::Case {
                                    scrutinee: value(scrutinee),
                                    on_left: computation(on_left),
                                    on_right: computation(on_right),
                                },
                            };
                            match computations.iter().find(|entry| entry.0 == key) {
                                | Some(&(_, representative)) => representative,
                                | None => {
                                    computations.push((key, node));
                                    node
                                },
                            }
                        },
                    };
                    canon.insert(node, representative);
                },
            }
        }
        canon
    }

    /// The children of `node`, each read through `canon`.
    ///
    /// # Specification
    /// - requires: `canon` maps every child of `node`.
    /// - ensures: the representatives of `node`'s children, left to right.
    /// - provides: the children the lifting walks descend into.
    /// - panics: when a child is unmapped, which the requirement excludes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every child has a canonical representative. The
    ///   lifted output is checked for two nested shared legs and exact erased
    ///   shape, then replayed independently; ignoring canonical
    ///   representatives, reordering operands or collapsing duplicate edges
    ///   alters those observations.
    /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    #[spec(
        ensures: |ret| match node {
         CoreTerm::Value(id) => core.value(id).is_some_and(|value| match *value {
          Value::Constructor {ref fields,..} => ret.iter().copied().eq(fields.iter().map(|field| canon[&CoreTerm::Value(*field)])),
          Value::Record(ref fields) => ret.iter().copied().eq(fields.values().map(|field| canon[&CoreTerm::Value(*field)])),
          Value::PathRefl(code) => ret.as_slice() == [canon[&CoreTerm::Value(code)]],
          Value::PathProduct(first, second) => ret.as_slice() == [canon[&CoreTerm::Value(first)], canon[&CoreTerm::Value(second)]],
          Value::PathEquiv { forward, backward, .. } => ret.as_slice() == [canon[&CoreTerm::Value(forward)], canon[&CoreTerm::Value(backward)]],
          Value::Pair(a,b) | Value::StaticApplication(a,b) => ret.as_slice() == [canon[&CoreTerm::Value(a)],canon[&CoreTerm::Value(b)]],
          Value::StaticLambda(body) | Value::Injection(_,body) | Value::Lift{body,..} => ret.as_slice() == [canon[&CoreTerm::Value(body)]],
          Value::Thunk(body) => ret.as_slice() == [canon[&CoreTerm::Computation(body)]],
          Value::Primitive { .. } | Value::Variable{..} | Value::Constant(_) | Value::Unit | Value::Literal(_) | Value::Quote(_) | Value::QuoteComputation(_) => ret.is_empty(),
         }),
         CoreTerm::Computation(id) => core.computation(id).is_some_and(|computation| match *computation {
          Computation::DataCase {scrutinee,ref branches,..} => ret.iter().copied().eq(core::iter::once(canon[&CoreTerm::Value(scrutinee)]).chain(branches.iter().map(|branch| canon[&CoreTerm::Computation(*branch)]))),
          Computation::RecordProjection(record,_) => ret.as_slice() == [canon[&CoreTerm::Value(record)]],
          Computation::Primitive { arguments, .. } => ret.iter().copied().eq(arguments.iter().map(|argument| canon[&CoreTerm::Value(*argument)])),
          Computation::Transport(path, value) => ret.as_slice() == [canon[&CoreTerm::Value(path)], canon[&CoreTerm::Value(value)]],
          Computation::Lambda(body) => ret.as_slice() == [canon[&CoreTerm::Computation(body)]],
          Computation::Application(head,arg) => ret.as_slice() == [canon[&CoreTerm::Computation(head)],canon[&CoreTerm::Value(arg)]],
          Computation::Return(value) | Computation::Force(value) => ret.as_slice() == [canon[&CoreTerm::Value(value)]],
          Computation::Bind(bound,body) => ret.as_slice() == [canon[&CoreTerm::Computation(bound)],canon[&CoreTerm::Computation(body)]],
          Computation::Case{scrutinee,on_left,on_right} => ret.as_slice() == [canon[&CoreTerm::Value(scrutinee)],canon[&CoreTerm::Computation(on_left)],canon[&CoreTerm::Computation(on_right)]],
         }),
        }
    )]
    fn canonical_children(
        core: &CoreArena,
        canon: &BTreeMap<CoreTerm, CoreTerm>,
        node: CoreTerm,
    ) -> Vec<CoreTerm>
    {
        core_children(core, node)
            .into_iter()
            .map(|child| canon[&child])
            .collect()
    }

    /// The core term `root` of `core` as an overlay: every former grafted,
    /// subterms of equal tree read as one node, and each node the term
    /// reaches along two or more edges shared, the shares nested at the root
    /// in the order their nodes complete, the first outermost.
    ///
    /// # Specification
    /// - requires: all nodes beneath `root` resolve in `core`; the fixture
    ///   contains no quoted types or static operators.
    /// - ensures: an overlay that validates from the returned root and erases
    ///   to a term equal to `root` as a tree; a node reached once is grafted
    ///   where it stands.
    /// - provides: the spinal side of every certification test.
    /// - panics: when a mint is refused, which no fixture provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — resolved quote-free, static-operator-free term DAGs
    ///   are lifted. Validation, exact sharing counts, erased constructors and
    ///   kernel replay distinguish reused occurrence nodes, wrong share
    ///   distance or position, missed structural sharing and a changed term
    ///   family.
    /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    #[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok() && matches!((root,ret.1),
         (CoreTerm::Value(_),OverlayId::Value(_)) | (CoreTerm::Computation(_),OverlayId::Computation(_)))
    )]
    fn lifted(
        core: &CoreArena,
        root: CoreTerm,
    ) -> (Overlay, OverlayId)
    {
        let canon = canonical(core, root);
        let root = canon[&root];
        let mut edges: BTreeMap<CoreTerm, u32> = BTreeMap::new();
        let mut seen = BTreeSet::new();
        let mut completed = Vec::new();
        let mut walk = Vec::from([Lifting::Enter(root)]);
        while let Some(step) = walk.pop() {
            match step {
                | Lifting::Enter(node) => {
                    if !seen.insert(node) {
                        continue;
                    }
                    walk.push(Lifting::Exit(node));
                    for child in canonical_children(core, &canon, node).into_iter().rev() {
                        let reached = edges.entry(child).or_default();
                        *reached = reached.saturating_add(1);
                        walk.push(Lifting::Enter(child));
                    }
                },
                | Lifting::Exit(node) => completed.push(node),
            }
        }
        let shared: Vec<CoreTerm> = completed
            .into_iter()
            .filter(|node| edges.get(node).copied().unwrap_or(0) >= 2)
            .collect();
        let index: BTreeMap<CoreTerm, Nest> = shared
            .iter()
            .enumerate()
            .map(|(share, &node)| (node, Nest(share)))
            .collect();
        let mut overlay = Overlay::new();
        let mut taken = Vec::from_iter(shared.iter().map(|_| SharePosition::from(0_u32)));
        let mut legs = Vec::new();
        for (depth, &leg) in shared.iter().enumerate() {
            legs.push(lifted_under(
                &mut overlay,
                core,
                &canon,
                leg,
                Nest(depth),
                &index,
                &mut taken,
            ));
        }
        let mut built = lifted_under(
            &mut overlay,
            core,
            &canon,
            root,
            Nest(shared.len()),
            &index,
            &mut taken,
        );
        for (share, &leg) in legs.iter().enumerate().rev() {
            let arity = ShareArity::from(u32::from(taken[share]));
            built = match built {
                | OverlayId::Value(body) => OverlayId::Value(
                    overlay
                        .mint_value(ValueNode::Shared(Sharing { arity, leg, body }))
                        .expect("the leg and the body resolve"),
                ),
                | OverlayId::Computation(body) => OverlayId::Computation(
                    overlay
                        .mint_computation(CompNode::Shared(Sharing { arity, leg, body }))
                        .expect("the leg and the body resolve"),
                ),
                | OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                    panic!("a core term lifts to an evaluation node")
                },
            };
        }
        (overlay, built)
    }

    /// Graft `top` under `depth` shares, each shared node below it an
    /// occurrence of its share numbered in the order occurrences are minted.
    ///
    /// # Specification
    /// - requires: every shared node `top` reaches has a share index below
    ///   `depth`; the resolved fixture contains no quotes or static operators.
    /// - ensures: the grafted node; `taken` counts each share's occurrences
    ///   minted so far, left to right, which is preorder.
    /// - provides: the one minting walk [`lifted`] runs per leg and for the
    ///   body.
    /// - panics: when a mint is refused, which no fixture provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a canonical quote-free, static-operator-free term is
    ///   grafted beneath already indexed shares. The complete overlay must
    ///   validate and erase to the fixture tree; wrong distance, occurrence
    ///   numbering, child order or family changes validation, exact sharing or
    ///   kernel certification.
    /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
    #[spec(
        captures: [taken_len = taken.len()],
        ensures: |ret| taken.len() == taken_len && match (top,ret) {
         (CoreTerm::Value(_),OverlayId::Value(id)) => overlay.value(id).is_some(),
         (CoreTerm::Computation(_),OverlayId::Computation(id)) => overlay.computation(id).is_some(),
         _ => false,
        }
    )]
    fn lifted_under(
        overlay: &mut Overlay,
        core: &CoreArena,
        canon: &BTreeMap<CoreTerm, CoreTerm>,
        top: CoreTerm,
        depth: Nest,
        index: &BTreeMap<CoreTerm, Nest>,
        taken: &mut [SharePosition],
    ) -> OverlayId
    {
        let mut results: Vec<OverlayId> = Vec::new();
        let mut walk = Vec::from([Lifting::Enter(top)]);
        while let Some(step) = walk.pop() {
            match step {
                | Lifting::Enter(node) => {
                    if node != top
                        && let Some(&Nest(share)) = index.get(&node)
                    {
                        let distance = depth
                            .0
                            .checked_sub(1)
                            .and_then(|innermost| innermost.checked_sub(share))
                            .and_then(|distance| u32::try_from(distance).ok())
                            .expect("a shared node below lies in an outer share");
                        let bound = Bound {
                            distance: ShareDistance::from(distance),
                            position: taken[share],
                        };
                        taken[share] =
                            SharePosition::from(u32::from(taken[share]).saturating_add(1));
                        results.push(match node {
                            | CoreTerm::Value(_) => OverlayId::Value(
                                overlay
                                    .mint_value(ValueNode::Bound(bound))
                                    .expect("an occurrence names no child"),
                            ),
                            | CoreTerm::Computation(_) => OverlayId::Computation(
                                overlay
                                    .mint_computation(CompNode::Bound(bound))
                                    .expect("an occurrence names no child"),
                            ),
                        });
                        continue;
                    }
                    walk.push(Lifting::Exit(node));
                    for child in canonical_children(core, canon, node).into_iter().rev() {
                        walk.push(Lifting::Enter(child));
                    }
                },
                | Lifting::Exit(node) => {
                    let count = core_children(core, node).len();
                    let split = results
                        .len()
                        .checked_sub(count)
                        .expect("a node's children are on the stack");
                    let children = results.split_off(split);
                    let value = |at: usize| match children[at] {
                        | OverlayId::Value(id) => id,
                        | other => panic!("a value child: {other:?}"),
                    };
                    let computation = |at: usize| match children[at] {
                        | OverlayId::Computation(id) => id,
                        | other => panic!("a computation child: {other:?}"),
                    };
                    let made = match node {
                        | CoreTerm::Value(id) => {
                            let graft = match *core.value(id).expect("a reached value resolves") {
                                | Value::Primitive { .. } => {
                                    panic!("the duplication fixtures carry no native operation")
                                },
                                | Value::Variable { zone, index } => {
                                    ValueGraft::Variable { zone, index }
                                },
                                | Value::Constant(constant) => ValueGraft::Constant(constant),
                                | Value::Unit => ValueGraft::Unit,
                                | Value::Literal(ref literal) => {
                                    ValueGraft::Literal(literal.clone())
                                },
                                | Value::Pair(..) => ValueGraft::Pair(value(0), value(1)),
                                | Value::Injection(side, _) => {
                                    ValueGraft::Injection(side, value(0))
                                },
                                | Value::Thunk(_) => ValueGraft::Thunk(computation(0)),
                                | Value::Lift { ref target, .. } => ValueGraft::Lift {
                                    target: target.clone(),
                                    body: value(0),
                                },
                                | Value::PathRefl(_)
                                | Value::Constructor { .. }
                                | Value::Record(_)
                                | Value::PathProduct(..)
                                | Value::PathEquiv { .. }
                                | Value::Quote(_)
                                | Value::QuoteComputation(_)
                                | Value::StaticLambda(_)
                                | Value::StaticApplication(..) => {
                                    panic!(
                                        "the duplication fixtures carry no quote, operator or path"
                                    )
                                },
                            };
                            OverlayId::Value(
                                overlay
                                    .mint_value(ValueNode::Grafted(graft))
                                    .expect("the children resolve"),
                            )
                        },
                        | CoreTerm::Computation(id) => {
                            let graft = match *core
                                .computation(id)
                                .expect("a reached computation resolves")
                            {
                                | Computation::DataCase { .. }
                                | Computation::RecordProjection(..) => {
                                    panic!("native eliminators are outside the duplication fixture")
                                },
                                | Computation::Primitive { .. } => {
                                    panic!("the duplication fixtures carry no native operation")
                                },
                                | Computation::Transport(..) => {
                                    panic!("the duplication fixtures carry no transport")
                                },
                                | Computation::Lambda(_) => CompGraft::Lambda(computation(0)),
                                | Computation::Application(..) => {
                                    CompGraft::Application(computation(0), value(1))
                                },
                                | Computation::Return(_) => CompGraft::Return(value(0)),
                                | Computation::Force(_) => CompGraft::Force(value(0)),
                                | Computation::Bind(..) => {
                                    CompGraft::Bind(computation(0), computation(1))
                                },
                                | Computation::Case { .. } => CompGraft::Case {
                                    scrutinee: value(0),
                                    on_left: computation(1),
                                    on_right: computation(2),
                                },
                            };
                            OverlayId::Computation(
                                overlay
                                    .mint_computation(CompNode::Grafted(graft))
                                    .expect("the children resolve"),
                            )
                        },
                    };
                    results.push(made);
                },
            }
        }
        results.pop().expect("the walk leaves the top")
    }

    /// The kernel's copy of a world's terms and the types their codes quote,
    /// each core node translated once.
    #[derive(Default)]
    struct Kernel
    {
        /// The kernel's terms.
        arena: TermArena,
        /// The kernel node of every core value translated.
        values: BTreeMap<ValueId, gandr_kernel_term::ValueId>,
        /// The kernel node of every core computation translated.
        computations: BTreeMap<ComputationId, gandr_kernel_term::ComputationId>,
        /// The kernel node of every core value type translated.
        value_types: BTreeMap<ValueTypeId, gandr_kernel_term::ValueTypeId>,
        /// The kernel node of every core computation type translated.
        comp_types: BTreeMap<CompTypeId, gandr_kernel_term::CompTypeId>,
    }

    /// A core node awaiting translation.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Node
    {
        /// A value.
        Value(ValueId),
        /// A computation.
        Computation(ComputationId),
        /// A value type.
        ValueType(ValueTypeId),
        /// A computation type.
        CompType(CompTypeId),
    }

    /// Whether a core node has its kernel copy yet.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Translated
    {
        /// The copy exists.
        Made,
        /// The copy is still to be minted.
        Missing,
    }

    impl Kernel
    {
        /// The kernel copy of the core value `value`.
        ///
        /// # Specification
        /// - requires: as [`Kernel::translate`].
        /// - ensures: the kernel node `value` translates to.
        /// - provides: a side's or a body's translation.
        /// - panics: as [`Kernel::translate`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a resolved supported value belongs to the run’s
        ///   source arena. Independent replay of positive and negative
        ///   comparisons, including quoted codes, observes preserved
        ///   constructors and constants; a wrong cache entry, wrong node family
        ///   or swapped operand changes certification.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
        #[spec(
            ensures: |ret| self.values.get(&value) == Some(&ret) && self.arena.value(ret).is_some()
        )]
        fn value(
            &mut self,
            core: &CoreArena,
            value: ValueId,
        ) -> gandr_kernel_term::ValueId
        {
            self.translate(core, Node::Value(value));
            *self.values.get(&value).expect("the value was translated")
        }

        /// The kernel copy of the core computation `computation`.
        ///
        /// # Specification
        /// - requires: as [`Kernel::translate`].
        /// - ensures: the kernel node `computation` translates to.
        /// - provides: a side's translation.
        /// - panics: as [`Kernel::translate`].
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a resolved supported computation belongs to the
        ///   run’s source arena. Kernel replay of lambdas, applications and
        ///   forcing distinguishes a wrong copy, changed binder structure or
        ///   misplaced value/computation child.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
        #[spec(
            ensures: |ret| self.computations.get(&computation) == Some(&ret) && self.arena.computation(ret).is_some()
        )]
        fn computation(
            &mut self,
            core: &CoreArena,
            computation: ComputationId,
        ) -> gandr_kernel_term::ComputationId
        {
            self.translate(core, Node::Computation(computation));
            *self
                .computations
                .get(&computation)
                .expect("the computation was translated")
        }

        /// Translate `root` and everything beneath it, children first.
        ///
        /// # Specification
        /// - requires: `core` is this translator's source arena; every reached
        ///   node resolves, variables are intuitionistic, and no static lambda
        ///   or parameterized universe sort occurs.
        /// - ensures: `root` and every node beneath it have a kernel copy of
        ///   the same shape, constants at the same positions.
        /// - provides: the one translation the replay tests share.
        /// - panics: on a dangling or unsupported node or a linear variable,
        ///   excluded by the requirements.
        ///
        /// # Termination
        /// - reason: the `while let Some(&node) = stack.last()` loop over an
        ///   explicit stack, not recursion.
        /// - measure: the reachable nodes without a copy, then the stack's
        ///   length: a node is pushed only while it has no copy, beneath a
        ///   parent minted after it, and popped once it has one.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — one source arena supplies finite intuitionistic
        ///   term/type DAGs without static lambdas or parameterized universe
        ///   sorts. Kernel agreement on ordinary terms and quoted codes
        ///   observes children-first translation, retained sharing and constant
        ///   positions; wrong-family caches or dropped descendants alter
        ///   replay.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
        #[spec(
            captures: [counts = [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()]],
            ensures: |ret| self.translated(root) == Translated::Made
             && [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()].into_iter().zip(counts).all(|(after,before)| after >= before)
             && self.values.values().all(|&id| self.arena.value(id).is_some())
             && self.computations.values().all(|&id| self.arena.computation(id).is_some())
             && self.value_types.values().all(|&id| self.arena.value_type(id).is_some())
             && self.comp_types.values().all(|&id| self.arena.comp_type(id).is_some())
        )]
        fn translate(
            &mut self,
            core: &CoreArena,
            root: Node,
        )
        {
            let mut stack = Vec::from([root]);
            while let Some(&node) = stack.last() {
                let pending: Vec<Node> = self
                    .children(core, node)
                    .into_iter()
                    .filter(|&child| self.translated(child) == Translated::Missing)
                    .collect();
                if pending.is_empty() {
                    stack.pop();
                    self.build(core, node);
                }
                else {
                    stack.extend(pending);
                }
            }
        }

        /// Whether `node` has a kernel copy.
        ///
        /// # Specification
        /// - requires: nothing; a node need not have a copy yet.
        /// - ensures: Made exactly when the node's own family map contains its
        ///   id.
        /// - provides: the completed-node boundary of the postorder
        ///   translation.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — translation may encounter a new node, a completed
        ///   node or an already translated shared child in each supported
        ///   family. Kernel certification and shared-ladder comparisons observe
        ///   premature completion, wrong-family membership and discarded cached
        ///   copies.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
        #[spec(
            ensures: |ret| (ret == Translated::Made) == match node {
             Node::Value(id) => self.values.contains_key(&id), Node::Computation(id) => self.computations.contains_key(&id),
             Node::ValueType(id) => self.value_types.contains_key(&id), Node::CompType(id) => self.comp_types.contains_key(&id),
            }
        )]
        fn translated(
            &self,
            node: Node,
        ) -> Translated
        {
            let made = match node {
                | Node::Value(value) => self.values.contains_key(&value),
                | Node::Computation(computation) => self.computations.contains_key(&computation),
                | Node::ValueType(value_type) => self.value_types.contains_key(&value_type),
                | Node::CompType(comp_type) => self.comp_types.contains_key(&comp_type),
            };
            if made {
                Translated::Made
            }
            else {
                Translated::Missing
            }
        }

        /// The nodes `node` is built from.
        ///
        /// # Specification
        /// - requires: an untranslated node resolves in the run's source arena.
        /// - ensures: no children for a completed copy; otherwise the source
        ///   node's immediate children in constructor order, including quoted
        ///   types.
        /// - provides: the edges followed by the postorder translator.
        /// - panics: when an untranslated source node does not resolve.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — an untranslated resolved node contributes its
        ///   ordered children, while a cached node contributes none. Kernel
        ///   replay spans value, computation and quoted-type edges; wrong
        ///   arity, operand order or family changes certification, and repeated
        ///   ladder subterms exercise the completed-node boundary.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
        #[spec(
            ensures: |ret| if self.translated(node) == Translated::Made { ret.is_empty() } else { match node {
             Node::Value(id) => core.value(id).is_some_and(|value| match *value {
              Value::Constructor {datatype,ref fields,..} => ret.iter().copied().eq(core::iter::once(Node::ValueType(datatype)).chain(fields.iter().copied().map(Node::Value))),
              Value::Record(ref fields) => ret.iter().copied().eq(fields.values().copied().map(Node::Value)),
              Value::PathRefl(code) => ret.as_slice() == [Node::Value(code)],
              Value::PathProduct(first, second) => ret.as_slice() == [Node::Value(first), Node::Value(second)],
              Value::PathEquiv { path_type, forward, backward, .. } => ret.as_slice() == [Node::ValueType(path_type), Node::Value(forward), Node::Value(backward)],
              Value::Pair(a,b) | Value::StaticApplication(a,b) => ret.as_slice() == [Node::Value(a),Node::Value(b)],
              Value::StaticLambda(body) | Value::Injection(_,body) | Value::Lift{body,..} => ret.as_slice() == [Node::Value(body)],
              Value::Thunk(body) => ret.as_slice() == [Node::Computation(body)],
             Value::Quote(id) => ret.as_slice() == [Node::ValueType(id)],
             Value::QuoteComputation(id) => ret.as_slice() == [Node::CompType(id)],
              Value::Primitive { .. } | Value::Variable{..} | Value::Constant(_) | Value::Unit | Value::Literal(_) => ret.is_empty(),
             }),
             Node::Computation(id) => core.computation(id).is_some_and(|computation| match *computation {
              Computation::DataCase {scrutinee,motive,ref branches} => ret.iter().copied().eq([Node::Value(scrutinee),Node::CompType(motive)].into_iter().chain(branches.iter().copied().map(Node::Computation))),
              Computation::RecordProjection(record,_) => ret.as_slice() == [Node::Value(record)],
              Computation::Primitive { arguments, .. } => ret.iter().copied().eq(arguments.iter().copied().map(Node::Value)),
              Computation::Transport(path, value) => ret.as_slice() == [Node::Value(path), Node::Value(value)],
              Computation::Lambda(body) => ret.as_slice() == [Node::Computation(body)],
              Computation::Application(head,arg) => ret.as_slice() == [Node::Computation(head),Node::Value(arg)],
              Computation::Return(value) | Computation::Force(value) => ret.as_slice() == [Node::Value(value)],
              Computation::Bind(bound,body) => ret.as_slice() == [Node::Computation(bound),Node::Computation(body)],
              Computation::Case{scrutinee,on_left,on_right} => ret.as_slice() == [Node::Value(scrutinee),Node::Computation(on_left),Node::Computation(on_right)],
             }),
             Node::ValueType(id) => core.value_type(id).is_some_and(|value_type| match *value_type {
              ValueType::Data {ref arguments,..} => ret.iter().copied().eq(arguments.iter().copied().map(Node::Value)),
              ValueType::Record(ref fields) => ret.iter().copied().eq(fields.values().copied().map(Node::ValueType)),
              ValueType::PathUniverse(source, target) => ret.as_slice() == [Node::Value(source), Node::Value(target)],
              ValueType::Product(a,b) | ValueType::Sum(a,b) | ValueType::StaticPi{domain:a,codomain:b} => ret.as_slice() == [Node::ValueType(a),Node::ValueType(b)],
              ValueType::Thunk(body) => ret.as_slice() == [Node::CompType(body)],
              ValueType::Lift{inner,..} => ret.as_slice() == [Node::ValueType(inner)],
              ValueType::Element{code,..} => ret.as_slice() == [Node::Value(code)],
              ValueType::Base(_) | ValueType::Unit | ValueType::Universe{..} | ValueType::Abstract(_) => ret.is_empty(),
             }),
             Node::CompType(id) => core.comp_type(id).is_some_and(|comp_type| match *comp_type {
              CompType::Returner(result) => ret.as_slice() == [Node::ValueType(result)],
              CompType::Arrow{domain,codomain} | CompType::Pi{domain,codomain} => ret.as_slice() == [Node::ValueType(domain),Node::CompType(codomain)],
              CompType::Element{code,..} => ret.as_slice() == [Node::Value(code)],
             }),
            } }
        )]
        fn children(
            &self,
            core: &CoreArena,
            node: Node,
        ) -> Vec<Node>
        {
            if self.translated(node) == Translated::Made {
                return Vec::new();
            }
            match node {
                | Node::Value(value) => {
                    match *(core.value(value).expect("a fixture value resolves")) {
                        | Value::Constructor {
                            ref datatype,
                            ref fields,
                            ..
                        } => core::iter::once(Node::ValueType(*datatype))
                            .chain(fields.iter().copied().map(Node::Value))
                            .collect(),
                        | Value::Record(ref fields) => {
                            fields.values().copied().map(Node::Value).collect()
                        },
                        | Value::PathRefl(code) => Vec::from([Node::Value(code)]),
                        | Value::PathEquiv {
                            path_type,
                            forward,
                            backward,
                            ..
                        } => Vec::from([
                            Node::ValueType(path_type),
                            Node::Value(forward),
                            Node::Value(backward),
                        ]),
                        | Value::PathProduct(first, second)
                        | Value::Pair(first, second)
                        | Value::StaticApplication(first, second) => {
                            Vec::from([Node::Value(first), Node::Value(second)])
                        },
                        | Value::StaticLambda(body) => Vec::from([Node::Value(body)]),
                        | Value::Injection(_, body) | Value::Lift { body, .. } => {
                            Vec::from([Node::Value(body)])
                        },
                        | Value::Thunk(body) => Vec::from([Node::Computation(body)]),
                        | Value::Quote(quoted) => Vec::from([Node::ValueType(quoted)]),
                        | Value::QuoteComputation(quoted) => Vec::from([Node::CompType(quoted)]),
                        | Value::Primitive { .. }
                        | Value::Variable { .. }
                        | Value::Constant(_)
                        | Value::Unit
                        | Value::Literal(_) => Vec::new(),
                    }
                },
                | Node::Computation(computation) => {
                    match *(core
                        .computation(computation)
                        .expect("a fixture computation resolves"))
                    {
                        | Computation::DataCase {
                            ref scrutinee,
                            ref motive,
                            ref branches,
                        } => [Node::Value(*scrutinee), Node::CompType(*motive)]
                            .into_iter()
                            .chain(branches.iter().copied().map(Node::Computation))
                            .collect(),
                        | Computation::RecordProjection(ref record, _) => {
                            Vec::from([Node::Value(*record)])
                        },
                        | Computation::Primitive { ref arguments, .. } => {
                            arguments.iter().copied().map(Node::Value).collect()
                        },
                        | Computation::Transport(path, value) => {
                            Vec::from([Node::Value(path), Node::Value(value)])
                        },
                        | Computation::Lambda(body) => Vec::from([Node::Computation(body)]),
                        | Computation::Application(head, argument) => {
                            Vec::from([Node::Computation(head), Node::Value(argument)])
                        },
                        | Computation::Return(value) | Computation::Force(value) => {
                            Vec::from([Node::Value(value)])
                        },
                        | Computation::Bind(bound, body) => {
                            Vec::from([Node::Computation(bound), Node::Computation(body)])
                        },
                        | Computation::Case {
                            scrutinee,
                            on_left,
                            on_right,
                        } => Vec::from([
                            Node::Value(scrutinee),
                            Node::Computation(on_left),
                            Node::Computation(on_right),
                        ]),
                    }
                },
                | Node::ValueType(value_type) => {
                    match *core
                        .value_type(value_type)
                        .expect("a fixture type resolves")
                    {
                        | ValueType::Data { ref arguments, .. } => {
                            arguments.iter().copied().map(Node::Value).collect()
                        },
                        | ValueType::Record(ref fields) => {
                            fields.values().copied().map(Node::ValueType).collect()
                        },
                        | ValueType::PathUniverse(source, target) => {
                            Vec::from([Node::Value(source), Node::Value(target)])
                        },
                        | ValueType::Product(first, second)
                        | ValueType::Sum(first, second)
                        | ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        } => Vec::from([Node::ValueType(first), Node::ValueType(second)]),
                        | ValueType::Thunk(body) => Vec::from([Node::CompType(body)]),
                        | ValueType::Lift { inner, .. } => Vec::from([Node::ValueType(inner)]),
                        | ValueType::Element { code, .. } => Vec::from([Node::Value(code)]),
                        | ValueType::Base(_)
                        | ValueType::Unit
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_) => Vec::new(),
                    }
                },
                | Node::CompType(comp_type) => {
                    match *core.comp_type(comp_type).expect("a fixture type resolves") {
                        | CompType::Returner(result) => Vec::from([Node::ValueType(result)]),
                        | CompType::Arrow { domain, codomain }
                        | CompType::Pi { domain, codomain } => {
                            Vec::from([Node::ValueType(domain), Node::CompType(codomain)])
                        },
                        | CompType::Element { code, .. } => Vec::from([Node::Value(code)]),
                    }
                },
            }
        }

        /// Mint the kernel copy of `node`, whose children have theirs.
        ///
        /// # Specification
        /// - requires: the source and all descendants satisfy
        ///   `Kernel::translate`'s requirements; every immediate child already
        ///   has its kernel copy.
        /// - ensures: the node has a same-shape kernel copy; an existing copy
        ///   remains unchanged, otherwise only this node's family gains an
        ///   entry.
        /// - provides: the constructor-preserving step of the translation.
        /// - panics: on an unresolved or unsupported node, or an untranslated
        ///   child.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — supported source nodes have translated children,
        ///   or already have their own copy. Independent kernel certification
        ///   checks preserved constructor, constants, binders and quoted types;
        ///   overwriting another family, changing a child or rebuilding shared
        ///   copies changes the checked translation.
        /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
        /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
        /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
        #[spec(
            captures: [counts = [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()]],
            ensures: |ret| self.translated(node) == Translated::Made && {
             let after = [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()];
             let family = match node { Node::Value(_) => 0, Node::Computation(_) => 1, Node::ValueType(_) => 2, Node::CompType(_) => 3 };
             after.into_iter().zip(counts).enumerate().all(|(at,(after,before))| if at == family { after == before || before.checked_add(1) == Some(after) } else { after == before })
            }
        )]
        fn build(
            &mut self,
            core: &CoreArena,
            node: Node,
        )
        {
            if self.translated(node) == Translated::Made {
                return;
            }
            let value =
                |kernel: &Self, value: ValueId| *kernel.values.get(&value).expect("children first");
            let computation = |kernel: &Self, computation: ComputationId| {
                *kernel
                    .computations
                    .get(&computation)
                    .expect("children first")
            };
            match node {
                | Node::Value(id) => {
                    let copy = match *(core.value(id).expect("a fixture value resolves")) {
                        | Value::Constructor {
                            ref datatype,
                            ref tag,
                            ref fields,
                        } => {
                            let datatype = self.value_types[datatype];
                            let fields = fields.iter().map(|field| value(self, *field)).collect();
                            self.arena.value_constructor(datatype, *tag, fields)
                        },
                        | Value::Record(ref fields) => {
                            let fields = fields
                                .iter()
                                .map(|(label, field)| (label.clone(), value(self, *field)))
                                .collect();
                            self.arena.value_record(fields)
                        },
                        | Value::Primitive { .. } => panic!("the kernel has no native operation"),
                        | Value::Variable {
                            zone: Zone::Intuitionistic,
                            index,
                        } => self.arena.value_variable(index),
                        | Value::Variable {
                            zone: Zone::Linear, ..
                        } => {
                            panic!("the kernel's terms have no linear zone")
                        },
                        | Value::Constant(constant) => self.arena.value_constant(constant),
                        | Value::Unit => self.arena.value_unit(),
                        | Value::Literal(ref literal) => self.arena.value_literal(literal.clone()),
                        | Value::PathRefl(code) => {
                            let code = value(self, code);
                            self.arena.value_path_refl(code)
                        },
                        | Value::PathProduct(first, second) => {
                            let (first, second) = (value(self, first), value(self, second));
                            self.arena.value_path_product(first, second)
                        },
                        | Value::PathEquiv {
                            path_type,
                            forward,
                            backward,
                            ref evidence,
                        } => {
                            let path_type =
                                *self.value_types.get(&path_type).expect("children first");
                            let (forward, backward) = (value(self, forward), value(self, backward));
                            self.arena.value_path_equiv(
                                path_type,
                                forward,
                                backward,
                                alloc::sync::Arc::clone(evidence),
                            )
                        },
                        | Value::Pair(first, second) => {
                            let (first, second) = (value(self, first), value(self, second));
                            self.arena.value_pair(first, second)
                        },
                        | Value::Injection(side, body) => {
                            let body = value(self, body);
                            self.arena.value_injection(side, body)
                        },
                        | Value::Thunk(body) => {
                            let body = computation(self, body);
                            self.arena.value_thunk(body)
                        },
                        | Value::Quote(quoted) => {
                            let quoted = *self.value_types.get(&quoted).expect("children first");
                            self.arena.value_quote(quoted)
                        },
                        | Value::QuoteComputation(quoted) => {
                            let quoted = *self.comp_types.get(&quoted).expect("children first");
                            self.arena.value_quote_computation(quoted)
                        },
                        | Value::Lift { ref target, body } => {
                            let body = value(self, body);
                            self.arena.value_lift(target.clone(), body)
                        },
                        | Value::StaticApplication(head, argument) => {
                            let (head, argument) = (value(self, head), value(self, argument));
                            self.arena.value_static_application(head, argument)
                        },
                        | Value::StaticLambda(_) => {
                            panic!("the kernel has no static lambda: a replay fixture lifts it")
                        },
                    };
                    self.values.insert(id, copy);
                },
                | Node::Computation(id) => {
                    let copy = match *core
                        .computation(id)
                        .expect("a fixture computation resolves")
                    {
                        | Computation::DataCase {
                            scrutinee,
                            motive,
                            ref branches,
                        } => {
                            let scrutinee = value(self, scrutinee);
                            let motive = self.comp_types[&motive];
                            let branches = branches
                                .iter()
                                .map(|branch| computation(self, *branch))
                                .collect();
                            self.arena
                                .computation_data_case(scrutinee, motive, branches)
                        },
                        | Computation::RecordProjection(record, ref label) => {
                            let record = value(self, record);
                            self.arena
                                .computation_record_projection(record, label.clone())
                        },
                        | Computation::Primitive { .. } => {
                            panic!("the kernel has no native operation")
                        },
                        | Computation::Transport(path, argument) => {
                            let (path, argument) = (value(self, path), value(self, argument));
                            self.arena.computation_transport(path, argument)
                        },
                        | Computation::Lambda(body) => {
                            let body = computation(self, body);
                            self.arena.computation_lambda(body)
                        },
                        | Computation::Application(head, argument) => {
                            let (head, argument) = (computation(self, head), value(self, argument));
                            self.arena.computation_application(head, argument)
                        },
                        | Computation::Return(returned) => {
                            let returned = value(self, returned);
                            self.arena.computation_return(returned)
                        },
                        | Computation::Bind(bound, body) => {
                            let (bound, body) = (computation(self, bound), computation(self, body));
                            self.arena.computation_bind(bound, body)
                        },
                        | Computation::Force(forced) => {
                            let forced = value(self, forced);
                            self.arena.computation_force(forced)
                        },
                        | Computation::Case {
                            scrutinee,
                            on_left,
                            on_right,
                        } => {
                            let scrutinee = value(self, scrutinee);
                            let (on_left, on_right) =
                                (computation(self, on_left), computation(self, on_right));
                            self.arena.computation_case(scrutinee, on_left, on_right)
                        },
                    };
                    self.computations.insert(id, copy);
                },
                | Node::ValueType(id) => {
                    let value_type = |kernel: &Self, id: ValueTypeId| {
                        *kernel.value_types.get(&id).expect("children first")
                    };
                    let comp_type = |kernel: &Self, id: CompTypeId| {
                        *kernel.comp_types.get(&id).expect("children first")
                    };
                    let copy = match *core.value_type(id).expect("a fixture type resolves") {
                        | ValueType::Data {
                            declaration,
                            ref arguments,
                        } => {
                            let arguments = arguments
                                .iter()
                                .map(|argument| value(self, *argument))
                                .collect();
                            self.arena.value_type_data(declaration, arguments)
                        },
                        | ValueType::Record(ref fields) => {
                            let fields = fields
                                .iter()
                                .map(|(label, field)| (label.clone(), value_type(self, *field)))
                                .collect();
                            self.arena.value_type_record(fields)
                        },
                        | ValueType::PathUniverse(source, target) => {
                            let (source, target) = (value(self, source), value(self, target));
                            self.arena.value_type_path_universe(source, target)
                        },
                        | ValueType::Base(base) => self.arena.value_type_base(base),
                        | ValueType::Unit => self.arena.value_type_unit(),
                        | ValueType::Product(first, second) => {
                            let (first, second) =
                                (value_type(self, first), value_type(self, second));
                            self.arena.value_type_product(first, second)
                        },
                        | ValueType::Sum(first, second) => {
                            let (first, second) =
                                (value_type(self, first), value_type(self, second));
                            self.arena.value_type_sum(first, second)
                        },
                        | ValueType::Thunk(body) => {
                            let body = comp_type(self, body);
                            self.arena.value_type_thunk(body)
                        },
                        | ValueType::Universe {
                            sort: Sort::Ground(sort),
                            ref level,
                        } => self.arena.value_type_universe(sort, level.clone()),
                        | ValueType::Universe {
                            sort: Sort::Parameter(_),
                            ..
                        } => panic!("no fixture quotes a sort-polymorphic universe"),
                        | ValueType::Lift { inner, ref target } => {
                            let inner = value_type(self, inner);
                            self.arena.value_type_lift(inner, target.clone())
                        },
                        | ValueType::Element { code, ref target } => {
                            let code = value(self, code);
                            self.arena.value_type_element(code, target.clone())
                        },
                        | ValueType::Abstract(atom) => self.arena.value_type_abstract(atom),
                        | ValueType::StaticPi { domain, codomain } => {
                            let (domain, codomain) =
                                (value_type(self, domain), value_type(self, codomain));
                            self.arena.value_type_static_pi(domain, codomain)
                        },
                    };
                    self.value_types.insert(id, copy);
                },
                | Node::CompType(id) => {
                    let value_type = |kernel: &Self, id: ValueTypeId| {
                        *kernel.value_types.get(&id).expect("children first")
                    };
                    let comp_type = |kernel: &Self, id: CompTypeId| {
                        *kernel.comp_types.get(&id).expect("children first")
                    };
                    let copy = match *core.comp_type(id).expect("a fixture type resolves") {
                        | CompType::Returner(result) => {
                            let result = value_type(self, result);
                            self.arena.comp_type_returner(result)
                        },
                        | CompType::Arrow { domain, codomain } => {
                            let (domain, codomain) =
                                (value_type(self, domain), comp_type(self, codomain));
                            self.arena.comp_type_arrow(domain, codomain)
                        },
                        | CompType::Pi { domain, codomain } => {
                            let (domain, codomain) =
                                (value_type(self, domain), comp_type(self, codomain));
                            self.arena.comp_type_pi(domain, codomain)
                        },
                        | CompType::Element { code, ref target } => {
                            let code = value(self, code);
                            self.arena.comp_type_element(code, target.clone())
                        },
                    };
                    self.comp_types.insert(id, copy);
                },
            }
        }
    }

    /// The decision the kernel reads for the machine's `decision`: a constant
    /// keeps its position, and every other node is opaque to the replay.
    ///
    /// # Specification
    /// - requires: nothing; every machine decision is representable in replay.
    /// - ensures: the decision kind, side and subgoal position remain
    ///   unchanged; constant nodes retain their index and run-local nodes
    ///   become Other.
    /// - provides: the trust-boundary projection into kernel replay decisions.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — machine decisions carry constant identities or
    ///   run-local value/computation ids. Exact constructor and side
    ///   preservation is observed by independent certification and the
    ///   wrong-branch refusal; erasing a constant identity, retaining a
    ///   run-local id or swapping a side changes replay.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
        ensures: |ret| {
         let node = |node| match node { TraceNode::Constant(constant) => ReplayNode::Constant(constant), TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other };
         ret == match decision {
         ConversionDecision::Decompose => ConversionDecision::Decompose,
         ConversionDecision::ReduceLeft{redex} => ConversionDecision::ReduceLeft{redex:node(redex)},
         ConversionDecision::ReduceRight{redex} => ConversionDecision::ReduceRight{redex:node(redex)},
         ConversionDecision::ConstShortcut{constant} => ConversionDecision::ConstShortcut{constant:node(constant)},
         ConversionDecision::Unfold{constant} => ConversionDecision::Unfold{constant:node(constant)},
         ConversionDecision::Postpone{constant} => ConversionDecision::Postpone{constant:node(constant)},
         ConversionDecision::Freeze{constant,side} => ConversionDecision::Freeze{constant:node(constant),side},
         ConversionDecision::EtaExpand{side,variable} => ConversionDecision::EtaExpand{side,variable:node(variable)},
         ConversionDecision::Force{thunk} => ConversionDecision::Force{thunk:node(thunk)},
         ConversionDecision::ComparedShared{left,right} => ConversionDecision::ComparedShared{left:node(left),right:node(right)},
         ConversionDecision::NegativeSubgoal{position} => ConversionDecision::NegativeSubgoal{position},
         }
        }
    )]
    fn kernel_decision(decision: ConversionDecision<TraceNode>) -> ConversionDecision<ReplayNode>
    {
        let node = |node: TraceNode| match node {
            | TraceNode::Constant(constant) => ReplayNode::Constant(constant),
            | TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
        };
        match decision {
            | ConversionDecision::ReduceLeft { redex } => {
                ConversionDecision::ReduceLeft { redex: node(redex) }
            },
            | ConversionDecision::ReduceRight { redex } => {
                ConversionDecision::ReduceRight { redex: node(redex) }
            },
            | ConversionDecision::ConstShortcut { constant } => ConversionDecision::ConstShortcut {
                constant: node(constant),
            },
            | ConversionDecision::Unfold { constant } => ConversionDecision::Unfold {
                constant: node(constant),
            },
            | ConversionDecision::Postpone { constant } => ConversionDecision::Postpone {
                constant: node(constant),
            },
            | ConversionDecision::Freeze { constant, side } => ConversionDecision::Freeze {
                constant: node(constant),
                side,
            },
            | ConversionDecision::EtaExpand { side, variable } => ConversionDecision::EtaExpand {
                side,
                variable: node(variable),
            },
            | ConversionDecision::Force { thunk } => {
                ConversionDecision::Force { thunk: node(thunk) }
            },
            | ConversionDecision::ComparedShared { left, right } => {
                ConversionDecision::ComparedShared {
                    left: node(left),
                    right: node(right),
                }
            },
            | ConversionDecision::NegativeSubgoal { position } => {
                ConversionDecision::NegativeSubgoal { position }
            },
            | ConversionDecision::Decompose => ConversionDecision::Decompose,
        }
    }

    /// The certified kernel verdict a machine verdict corresponds to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: definitive verdicts keep their truth value; every machine
    ///   decline maps to the kernel's `EngineDeclined` result.
    /// - provides: the expected independent replay verdict, not a
    ///   certification.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the domain is both definitive verdicts and every
    ///   engine decline. Kernel comparisons check positive, negative and
    ///   schedule-induced declined results, distinguishing negation, treating
    ///   decline as refutation and inventing a kernel failure.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
        ensures: |ret| match verdict {
         MachineVerdict::Convertible => ret == KernelVerdict::Convertible,
         MachineVerdict::NotConvertible => ret == KernelVerdict::NotConvertible,
         MachineVerdict::Declined(_) => ret == KernelVerdict::Declined(ReplayDecline::EngineDeclined),
        }
    )]
    fn certified(verdict: MachineVerdict) -> KernelVerdict
    {
        match verdict {
            | MachineVerdict::Convertible => KernelVerdict::Convertible,
            | MachineVerdict::NotConvertible => KernelVerdict::NotConvertible,
            | MachineVerdict::Declined(_) => KernelVerdict::Declined(ReplayDecline::EngineDeclined),
        }
    }

    /// The constants a fixture names: the first four admitted, in order, and
    /// one never admitted.
    #[derive(Clone, Copy, Debug)]
    enum Name
    {
        /// The constant admitted first.
        Zero,
        /// The constant admitted second.
        One,
        /// The constant admitted third.
        Two,
        /// The constant admitted fourth.
        Three,
        /// A constant no fixture admits, so it never unfolds.
        Rigid,
    }

    impl Name
    {
        /// The admission position this name stands for.
        ///
        /// # Specification
        /// trivial.
        fn constant(self) -> ConstantIndex
        {
            ConstantIndex::from(match self {
                | Self::Zero => 0_usize,
                | Self::One => 1_usize,
                | Self::Two => 2_usize,
                | Self::Three => 3_usize,
                | Self::Rigid => 9_usize,
            })
        }

        /// The table entry a body stored under this name takes.
        ///
        /// # Specification
        /// trivial.
        fn entry(self) -> GlobalIndex
        {
            GlobalIndex::from(match self {
                | Self::Zero => 0_u32,
                | Self::One => 1_u32,
                | Self::Two => 2_u32,
                | Self::Three => 3_u32,
                | Self::Rigid => 9_u32,
            })
        }
    }

    /// The trace node naming the constant `name` stands for.
    ///
    /// # Specification
    /// trivial.
    fn named(name: Name) -> TraceNode
    {
        TraceNode::Constant(name.constant())
    }

    /// The innermost bound variable.
    ///
    /// # Specification
    /// trivial.
    fn innermost(core: &mut CoreArena) -> ValueId
    {
        core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
    }

    /// `thunk (λx. return x)`: the identity function as a value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a thunk of a lambda returning its innermost intuitionistic
    ///   variable.
    /// - provides: a closed identity function for forcing and eta comparisons.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh intuitionistic identity fixture is observed
    ///   through application, eta comparison and independent replay. Wrong
    ///   binder zone or index, missing suspension or missing return changes its
    ///   reduction and certification.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
        ensures: |ret| core.value(ret).is_some_and(|value| match *value {
         Value::Thunk(body) => core.computation(body).is_some_and(|comp| match *comp {
         Computation::Lambda(body) => core.computation(body).is_some_and(|comp| match *comp {
         Computation::Return(value) => matches!(core.value(value), Some(Value::Variable{zone:Zone::Intuitionistic,index}) if u32::from(*index) == 0), _ => false,
         }), _ => false,
         }), _ => false,
        })
    )]
    fn identity(core: &mut CoreArena) -> ValueId
    {
        let occurrence = innermost(core);
        let returned = core.computation_return(occurrence);
        let lambda = core.computation_lambda(returned);
        core.value_thunk(lambda)
    }

    /// `force head` applied to each argument in turn.
    ///
    /// # Specification
    /// - requires: the head and arguments resolve in core.
    /// - ensures: force head applied left-associatively to every argument in
    ///   order; an empty argument list is just force head.
    /// - provides: the fixture constructor for rigid and reducible application
    ///   spines.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a live value head and ordered live arguments form a
    ///   left-associated application spine. Rigid-spine comparisons and
    ///   independent replay distinguish reversing arguments, dropping an
    ///   application or failing to force the head.
    /// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
        ensures: |ret| {
         let mut cursor = ret;
         let mut valid = true;
         for &expected in arguments.iter().rev() {
          match core.computation(cursor) {
           Some(&Computation::Application(head,argument)) if argument == expected => cursor = head,
           _ => { valid = false; break; },
          }
         }
         valid && matches!(core.computation(cursor),Some(&Computation::Force(value)) if value == head)
        }
    )]
    fn call(
        core: &mut CoreArena,
        head: ValueId,
        arguments: &[ValueId],
    ) -> ComputationId
    {
        let mut applied = core.computation_force(head);
        for &argument in arguments {
            applied = core.computation_application(applied, argument);
        }
        applied
    }

    /// A world of four definitions and a rigid constant, and one pair per
    /// rule arm, each with the verdict it must reach.
    ///
    /// Constants zero and one are `unit` over two table entries, two is the
    /// identity function, three is a pair of units, and the rigid one has no
    /// body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: pairs covering the forced unfolding, both §6.1 choices, the
    ///   §6.2 choice, forcing, η against a rigid head, a rigid spine and two
    ///   lambdas, with both verdicts represented.
    /// - provides: the catalogue the sink comparisons run over.
    /// - panics: as [`World::new`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fixed catalogue contains both verdicts over live
    ///   value and computation roots. Each expected verdict is compared with
    ///   the actual machine and independently certified, distinguishing
    ///   mislabeled examples, dangling fixture roots and rule cases lost from
    ///   the sink differential.
    /// - witness: `machine::tests::recording_does_not_move_the_verdict`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
        ensures: |ret| ret.1.iter().any(|&(_,verdict)| verdict == MachineVerdict::Convertible)
         && ret.1.iter().any(|&(_,verdict)| verdict == MachineVerdict::NotConvertible)
         && ret.1.iter().all(|&(sides,verdict)| !matches!(verdict,MachineVerdict::Declined(_)) && match sides {
         Sides::Values(left,right) => ret.0.core.value(left).is_some() && ret.0.core.value(right).is_some(),
         Sides::Computations(left,right) => ret.0.core.computation(left).is_some() && ret.0.core.computation(right).is_some(),
         })
    )]
    fn catalogue() -> (World, Vec<(Sides, MachineVerdict)>)
    {
        let mut core = CoreArena::new();
        let first_unit = core.value_unit();
        let second_unit = core.value_unit();
        let function = identity(&mut core);
        let units = core.value_pair(first_unit, second_unit);
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let two = core.value_constant(Name::Two.constant());
        let three = core.value_constant(Name::Three.constant());
        let rigid = core.value_constant(Name::Rigid.constant());
        let unit = core.value_unit();

        let mut cases = Vec::from([
            (Sides::Values(zero, unit), MachineVerdict::Convertible),
            (Sides::Values(zero, units), MachineVerdict::NotConvertible),
            (Sides::Values(zero, one), MachineVerdict::Convertible),
            (Sides::Values(zero, three), MachineVerdict::NotConvertible),
        ]);
        let left = call(&mut core, two, &[zero]);
        let right = call(&mut core, two, &[unit]);
        cases.push((
            Sides::Computations(left, right),
            MachineVerdict::Convertible,
        ));
        let left = call(&mut core, rigid, &[unit, zero]);
        let right = call(&mut core, rigid, &[unit, units]);
        cases.push((
            Sides::Computations(left, right),
            MachineVerdict::NotConvertible,
        ));
        let occurrence = innermost(&mut core);
        let body = call(&mut core, two, &[occurrence]);
        let left = core.computation_lambda(body);
        let right = core.computation_force(two);
        cases.push((
            Sides::Computations(left, right),
            MachineVerdict::Convertible,
        ));
        let body = call(&mut core, rigid, &[occurrence]);
        let left = core.computation_lambda(body);
        let right = core.computation_force(rigid);
        cases.push((
            Sides::Computations(left, right),
            MachineVerdict::Convertible,
        ));
        let returned = core.computation_return(zero);
        let left = core.value_thunk(returned);
        let returned = core.computation_return(unit);
        let right = core.value_thunk(returned);
        cases.push((Sides::Values(left, right), MachineVerdict::Convertible));
        let returned = core.computation_return(zero);
        let left = core.computation_lambda(returned);
        let returned = core.computation_return(units);
        let right = core.computation_lambda(returned);
        cases.push((
            Sides::Computations(left, right),
            MachineVerdict::NotConvertible,
        ));

        let world = World::new(core, &[
            (Name::Zero, first_unit),
            (Name::One, second_unit),
            (Name::Two, function),
            (Name::Three, units),
        ]);
        (world, cases)
    }

    #[test]
    fn the_search_free_steps_answer_before_any_process()
    {
        let mut core = CoreArena::new();
        let left = core.value_unit();
        let right = core.value_unit();
        let paired = core.value_pair(left, right);
        let world = World::new(core, &[]);

        let mut log = TraceLog::new();
        let agreed = world.run(Sides::Values(left, right), &mut log);
        assert_eq!(MachineVerdict::Convertible, agreed.verdict());
        assert_eq!(
            0_usize,
            usize::from(agreed.processes()),
            "two units are structurally equal, so no goal is started"
        );
        let decisions: Vec<_> = log.decisions().copied().collect();
        assert!(
            matches!(decisions.as_slice(), [
                ConversionDecision::ComparedShared { .. }
            ]),
            "and the trace closes the pair in one decision: {decisions:?}"
        );

        let apart = world.run(Sides::Values(left, paired), &mut NullSink);
        assert_eq!(MachineVerdict::NotConvertible, apart.verdict());
        assert_eq!(
            0_usize,
            usize::from(apart.processes()),
            "a unit and a pair are separated by their guards, so no goal is started"
        );
    }

    #[test]
    fn a_code_constant_unfolds_to_its_quote()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let body = core.value_quote(unit);
        let reference = core.value_constant(Name::Zero.constant());
        let same = core.value_type_unit();
        let written = core.value_quote(same);
        let integer = core.value_type_base(BaseType::Integer);
        let other = core.value_quote(integer);
        let world = World::new(core, &[(Name::Zero, body)]);

        let alike = Sides::Values(reference, written);
        let (verdict, decisions) = world.traced(alike);
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert!(
            matches!(decisions.as_slice(), &[
                ConversionDecision::Unfold { constant },
                ConversionDecision::ReduceLeft { redex },
                ConversionDecision::ComparedShared { .. },
            ] if constant == named(Name::Zero) && redex == named(Name::Zero)),
            "the constant unfolds to a code, and two codes of one type close as shared: \
             {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::Convertible,
            world.replayed(alike, verdict, &decisions),
            "and the kernel replays the unfolding and the closing over its own quotes"
        );

        let apart = Sides::Values(reference, other);
        let (verdict, decisions) = world.traced(apart);
        assert_eq!(
            MachineVerdict::NotConvertible,
            verdict,
            "and two codes of rigidly different types are apart"
        );
        assert!(
            matches!(
                decisions.last(),
                Some(&ConversionDecision::ComparedShared { .. })
            ),
            "by a shared comparison the kernel separates on its own terms: {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::NotConvertible,
            world.replayed(apart, verdict, &decisions),
            "which the kernel's replay confirms"
        );
    }

    #[test]
    fn codes_that_could_unfold_inside_are_declined()
    {
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let body = core.value_quote(unit);
        let defined = core.value_constant(Name::Zero.constant());
        let decodes_defined = core.value_type_element(defined, Level::zero());
        let flexible = core.value_quote(decodes_defined);
        let opaque = core.value_constant(Name::Rigid.constant());
        let decodes_opaque = core.value_type_element(opaque, Level::zero());
        let rigid = core.value_quote(decodes_opaque);
        let plain = core.value_type_unit();
        let written = core.value_quote(plain);
        let world = World::new(core, &[(Name::Zero, body)]);

        let undecided = Sides::Values(flexible, written);
        let (verdict, decisions) = world.traced(undecided);
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::UndecidedCodes),
            verdict,
            "the decode names a constant with a body, which could unfold to the very code \
             it is compared against, and nothing reduces inside a type at this rung"
        );
        assert_eq!(
            certified(verdict),
            world.replayed(undecided, verdict, &decisions),
            "and the kernel declines with it: {decisions:?}"
        );
        let apart = Sides::Values(rigid, written);
        let (verdict, decisions) = world.traced(apart);
        assert_eq!(
            MachineVerdict::NotConvertible,
            verdict,
            "while a decode of a constant with no body cannot, so the codes are apart"
        );
        assert_eq!(
            KernelVerdict::NotConvertible,
            world.replayed(apart, verdict, &decisions),
            "and the kernel separates them on its own reading of rigidity: {decisions:?}"
        );
    }

    #[test]
    fn one_body_is_evaluated_once_for_two_definitions()
    {
        let processes = |entries: [Name; 2]| {
            let mut core = CoreArena::new();
            let body = core.value_unit();
            let zero = core.value_constant(Name::Zero.constant());
            let one = core.value_constant(Name::One.constant());
            let [first, second] = entries;
            let world = World::new(core, &[(first, body), (second, body)]);
            let report = world.run(Sides::Values(zero, one), &mut NullSink);
            assert_eq!(MachineVerdict::Convertible, report.verdict());
            usize::from(report.processes())
        };
        assert_eq!(
            5_usize,
            processes([Name::Zero, Name::One]),
            "the root, its two alternatives, and one channel per body"
        );
        assert_eq!(
            4_usize,
            processes([Name::Zero, Name::Zero]),
            "two definitions the table gave one body unfold through one channel"
        );
    }

    #[test]
    fn a_lambda_meets_a_defined_function_by_eta()
    {
        let mut core = CoreArena::new();
        let function = identity(&mut core);
        let head = core.value_constant(Name::Zero.constant());
        let occurrence = innermost(&mut core);
        let body = call(&mut core, head, &[occurrence]);
        let left = core.computation_lambda(body);
        let right = core.computation_force(head);
        let world = World::new(core, &[(Name::Zero, function)]);

        let (verdict, decisions) = world.traced(Sides::Computations(left, right));
        assert_eq!(MachineVerdict::Convertible, verdict);
        let &[
            ConversionDecision::Freeze {
                constant: frozen,
                side: ConversionSide::Right,
            },
            ConversionDecision::EtaExpand {
                side: ConversionSide::Right,
                variable,
            },
            ConversionDecision::ConstShortcut { constant: compared },
            ConversionDecision::ComparedShared { left, right },
        ] = decisions.as_slice()
        else {
            panic!("the frozen η-expansion answers before the unfolding does: {decisions:?}");
        };
        assert_eq!((named(Name::Zero), named(Name::Zero)), (frozen, compared));
        assert_eq!(
            (variable, variable),
            (left, right),
            "both sides apply the head to the one variable the expansion minted"
        );
    }

    #[test]
    fn a_lambda_meets_a_stuck_function_by_eta()
    {
        let mut core = CoreArena::new();
        let rigid = core.value_constant(Name::Rigid.constant());
        let occurrence = innermost(&mut core);
        let body = call(&mut core, rigid, &[occurrence]);
        let left = core.computation_lambda(body);
        let right = core.computation_force(rigid);
        let world = World::new(core, &[]);

        let (verdict, decisions) = world.traced(Sides::Computations(left, right));
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert!(
            matches!(decisions.as_slice(), [
                ConversionDecision::EtaExpand {
                    side: ConversionSide::Right,
                    variable: TraceNode::Value(_),
                },
                ConversionDecision::ComparedShared { .. },
            ]),
            "a rigid head cannot unfold, so η is the one rule, and the expanded pair closes \
             structurally: {decisions:?}"
        );
    }

    #[test]
    fn a_rigid_spine_refutes_at_its_differing_argument()
    {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let rigid = core.value_constant(Name::Rigid.constant());
        let reference = core.value_constant(Name::Zero.constant());
        let unit = core.value_unit();
        let paired = core.value_pair(unit, unit);
        let left = call(&mut core, rigid, &[unit, reference]);
        let right = call(&mut core, rigid, &[unit, paired]);
        let world = World::new(core, &[(Name::Zero, body)]);

        let (verdict, decisions) = world.traced(Sides::Computations(left, right));
        assert_eq!(MachineVerdict::NotConvertible, verdict);
        assert!(
            matches!(decisions.as_slice(), &[
                ConversionDecision::NegativeSubgoal { position },
                ConversionDecision::Unfold { constant },
                ConversionDecision::ReduceLeft { redex },
                ConversionDecision::ComparedShared { .. },
            ] if position == SubgoalPosition::from(1_u32)
                && constant == named(Name::Zero)
                && redex == named(Name::Zero)),
            "the refutation names the second argument, then refutes it on its own; the \
             first argument's agreement is not part of it: {decisions:?}"
        );
    }

    #[test]
    fn a_definition_cycle_declines_rather_than_unfolding_forever()
    {
        let mut core = CoreArena::new();
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let unit = core.value_unit();
        // Each body is the other constant, and neither definition declares the
        // other among its mentions, so the chain admits the cycle and nothing
        // ahead of conversion refuses it.
        let world = World::new(core, &[(Name::Zero, one), (Name::One, zero)]);

        let mut log = TraceLog::new();
        let report = world.run(Sides::Values(zero, unit), &mut log);
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Cycle),
            report.verdict(),
            "the left side unfolds to the other constant and back, so its third \
             unfolding repeats its first"
        );
        assert!(
            u64::from(report.steps()) < 64_u64,
            "the chain caught the cycle at its first repeat, long before any budget"
        );
        assert!(
            log.decisions().next().is_none(),
            "and a decline emits no derivation"
        );

        let (verdict, _) = world.traced(Sides::Values(zero, one));
        assert_eq!(
            MachineVerdict::Convertible,
            verdict,
            "the cycle does not hide that the two constants unfold to each other"
        );
    }

    #[test]
    fn unfolding_one_function_twice_is_not_a_cycle()
    {
        let mut core = CoreArena::new();
        let function = identity(&mut core);
        let head = Name::Zero.constant();
        let head = core.value_constant(head);
        let unit = core.value_unit();
        let applied = call(&mut core, head, &[unit]);
        let occurrence = innermost(&mut core);
        let again = call(&mut core, head, &[occurrence]);
        let twice = core.computation_bind(applied, again);
        let returned = core.computation_return(unit);
        let world = World::new(core, &[(Name::Zero, function)]);

        let (verdict, decisions) = world.traced(Sides::Computations(twice, returned));
        assert_eq!(
            MachineVerdict::Convertible,
            verdict,
            "the identity unfolds twice on one chain, under two spines, which is no cycle"
        );
        let unfoldings = decisions
            .iter()
            .filter(|decision| matches!(decision, ConversionDecision::Unfold { .. }))
            .count();
        assert_eq!(2_usize, unfoldings, "{decisions:?}");
    }

    #[test]
    fn a_diverging_evaluation_declines_on_the_budget()
    {
        let mut core = CoreArena::new();
        let occurrence = innermost(&mut core);
        let self_applied = call(&mut core, occurrence, &[occurrence]);
        let lambda = core.computation_lambda(self_applied);
        let omega = core.value_thunk(lambda);
        let looping = call(&mut core, omega, &[omega]);
        let body = core.value_thunk(looping);
        let head = core.value_constant(Name::Zero.constant());
        let forced = core.computation_force(head);
        let unit = core.value_unit();
        let returned = core.computation_return(unit);
        let world = World::new(core, &[(Name::Zero, body)]);

        let budget = StepBudget::from(10_000_u64);
        let settings = MachineSettings::new(
            SchedulingPolicy::default(),
            GranularityPolicy::default(),
            budget,
        );
        let report = world.run_under(
            settings,
            Sides::Computations(forced, returned),
            &mut NullSink,
        );
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Budget),
            report.verdict(),
            "forcing the definition runs Ω, which unfolds nothing the chain could catch"
        );
        assert!(
            u64::from(report.steps()) > u64::from(budget),
            "the evaluation slices were charged until they passed the budget"
        );
    }

    #[test]
    fn a_refutation_outranks_a_decline()
    {
        let mut core = CoreArena::new();
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let unit = core.value_unit();
        let units = core.value_pair(unit, unit);
        let cyclic = core.value_pair(zero, unit);
        let refuted = core.value_pair(unit, units);
        let world = World::new(core, &[(Name::Zero, one), (Name::One, zero)]);

        let (verdict, decisions) = world.traced(Sides::Values(cyclic, refuted));
        assert_eq!(
            MachineVerdict::NotConvertible,
            verdict,
            "the second components refute the pair whatever the first declines"
        );
        assert!(
            matches!(decisions.as_slice(), &[
                ConversionDecision::NegativeSubgoal { position },
                ConversionDecision::ComparedShared { .. },
            ] if position == SubgoalPosition::from(1_u32)),
            "{decisions:?}"
        );

        let (verdict, decisions) = world.traced(Sides::Values(cyclic, units));
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Cycle),
            verdict,
            "with the second components agreeing, the first one's decline is the answer"
        );
        assert!(decisions.is_empty(), "{decisions:?}");
    }

    #[test]
    fn recording_does_not_move_the_verdict()
    {
        let (world, cases) = catalogue();
        for (sides, expected) in cases {
            let unrecorded = world.run(sides, &mut NullSink);
            let mut log = TraceLog::new();
            let recorded = world.run(sides, &mut log);
            assert_eq!(expected, unrecorded.verdict(), "{sides:?}");
            assert_eq!(
                (unrecorded.verdict(), unrecorded.processes()),
                (recorded.verdict(), recorded.processes()),
                "recording changes what is kept, never what is run: {sides:?}"
            );
        }
    }

    #[test]
    fn the_sink_off_run_keeps_no_derivation()
    {
        let (world, cases) = catalogue();
        for (sides, _) in cases {
            let unrecorded = world.run(sides, &mut NullSink);
            let recorded = world.run(sides, &mut TraceLog::new());
            assert_eq!(
                0_usize,
                usize::from(unrecorded.derivations()),
                "the null sink keeps nothing, so the run allocates no derivation: {sides:?}"
            );
            assert_eq!(
                usize::from(recorded.processes()),
                usize::from(recorded.derivations()),
                "a recording run keeps one derivation per process: {sides:?}"
            );
        }
    }

    /// `thunk (return below to x. return (x, x))`: one evaluation of the
    /// constant `below`, paired with itself.
    ///
    /// # Specification
    /// - requires: nothing; below may denote a body or stand rigid.
    /// - ensures: a thunk binding return below once, then returning a pair of
    ///   the same innermost intuitionistic variable.
    /// - provides: one doubling rung whose repeated premise can be shared.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant reference is evaluated once beneath a bind
    ///   and its result is paired with itself. Exact memoized versus unrolled
    ///   process counts across successive ladder rungs, plus kernel replay,
    ///   distinguish duplicating evaluation, a wrong binder and naming the
    ///   wrong predecessor.
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
        ensures: |ret| core.value(ret).is_some_and(|value| match *value {
         Value::Thunk(body) => core.computation(body).is_some_and(|comp| match *comp {
         Computation::Bind(bound,body) => matches!(core.computation(bound),Some(&Computation::Return(value)) if core.value(value) == Some(&Value::Constant(below)))
          && core.computation(body).is_some_and(|comp| match *comp {
           Computation::Return(value) => core.value(value).is_some_and(|value| match *value {
            Value::Pair(left,right) => left == right && matches!(core.value(left),Some(Value::Variable{zone:Zone::Intuitionistic,index}) if u32::from(*index) == 0), _ => false,
           }), _ => false,
          }), _ => false,
         }), _ => false,
        })
    )]
    fn doubled(
        core: &mut CoreArena,
        below: ConstantIndex,
    ) -> ValueId
    {
        let reference = core.value_constant(below);
        let produced = core.computation_return(reference);
        let occurrence = innermost(core);
        let paired = core.value_pair(occurrence, occurrence);
        let returned = core.computation_return(paired);
        let bound = core.computation_bind(produced, returned);
        core.value_thunk(bound)
    }

    /// Admit `body` as the next constant, under a table entry of its own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the constant `body` is admitted as, at the next position.
    /// - provides: the admission order the ladder fixture builds in.
    /// - panics: past `u32::MAX` entries, which no fixture reaches.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finite body table below the index ceiling gains a
    ///   distinct entry at its next ordinal. Successive ladder comparisons
    ///   observe correct predecessor bodies and sharing growth, distinguishing
    ///   an off-by-one constant, reused table entry or wrong admitted body.
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
        captures: [position = bodies.len()],
        ensures: |ret| usize::from(ret) == position && position.checked_add(1) == Some(bodies.len())
         && bodies.last().is_some_and(|&(entry,stored)| usize::try_from(u32::from(entry)).ok() == Some(position) && stored == body)
    )]
    fn next_constant(
        bodies: &mut Vec<(GlobalIndex, ValueId)>,
        body: ValueId,
    ) -> ConstantIndex
    {
        let position = bodies.len();
        let entry = u32::try_from(position).expect("a fixture admits few constants");
        bodies.push((GlobalIndex::from(entry), body));
        ConstantIndex::from(position)
    }

    /// Two ladders of five rungs: rung zero of each is `unit`, and every rung
    /// above is [`doubled`] over the rung below it on its own ladder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the comparisons of rungs one through four across the two
    ///   ladders, in order, each convertible; a rung's comparison decomposes
    ///   into two premises naming one pair of the rung below.
    /// - provides: the family whose memoless run starts goals exponentially in
    ///   the rung and whose re-shared run starts them linearly.
    /// - panics: as [`World::admit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two five-rung ladders share only their structural
    ///   pattern, not admission identities. Exact linear memoized counts,
    ///   exponential null-memo counts and kernel certification distinguish a
    ///   skipped predecessor, same-side comparison, missing repeated premise or
    ///   wrong rung order.
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::edges_per_revision_grow_with_the_distinct_goals`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
        ensures: |ret| ret.0.bodies.len() == 10 && ret.1.len() == 4
         && ret.0.bodies.iter().take(2).all(|&body| ret.0.core.value(body) == Some(&Value::Unit))
         && ret.1.iter().enumerate().all(|(rung,&sides)| match sides {
         Sides::Values(left,right) => rung.checked_add(1).and_then(|rung| rung.checked_mul(2)).is_some_and(|position|
             ret.0.core.value(left) == Some(&Value::Constant(ConstantIndex::from(position)))
                 && position.checked_add(1).is_some_and(|position| ret.0.core.value(right) == Some(&Value::Constant(ConstantIndex::from(position))))),
         Sides::Computations(_,_) => false,
         })
    )]
    fn ladders() -> (World, Vec<Sides>)
    {
        let mut core = CoreArena::new();
        let mut bodies = Vec::new();
        let mut rungs = Vec::new();
        let mut below = None;
        for _rung in 0_u32 .. 5_u32 {
            let (left, right) = match below {
                | None => (core.value_unit(), core.value_unit()),
                | Some((left, right)) => (doubled(&mut core, left), doubled(&mut core, right)),
            };
            let left = next_constant(&mut bodies, left);
            let right = next_constant(&mut bodies, right);
            if below.is_some() {
                let left_rung = core.value_constant(left);
                let right_rung = core.value_constant(right);
                rungs.push(Sides::Values(left_rung, right_rung));
            }
            below = Some((left, right));
        }
        (World::admit(core, &bodies), rungs)
    }

    #[test]
    fn re_sharing_runs_one_goal_per_distinct_pair()
    {
        let (world, rungs) = ladders();
        let mut reshared = Vec::new();
        let mut memoless = Vec::new();
        for &sides in &rungs {
            let live = world.run(sides, &mut NullSink);
            let null =
                world.run_with::<_, NullMemo>(MachineSettings::default(), sides, &mut NullSink);
            assert_eq!(
                (MachineVerdict::Convertible, MachineVerdict::Convertible),
                (live.verdict(), null.verdict()),
                "{sides:?}"
            );
            reshared.push(usize::from(live.processes()));
            memoless.push(usize::from(null.processes()));
        }
        assert_eq!(
            Vec::from([13_usize, 21_usize, 29_usize, 37_usize]),
            reshared,
            "eight processes per rung over five at the bottom: the rung's goal, its two \
             alternatives, its pair's goal, two body channels and two entering channels, \
             with the pair's two premises meeting in one goal"
        );
        assert_eq!(
            Vec::from([16_usize, 34_usize, 66_usize, 126_usize]),
            memoless,
            "without re-sharing each rung's goals double beneath it, while its channels \
             are still shared"
        );
    }

    #[test]
    fn edges_per_revision_grow_with_the_distinct_goals()
    {
        let (world, rungs) = ladders();
        let edges: Vec<(usize, usize)> = rungs
            .iter()
            .map(|&sides| {
                let report = world.run(sides, &mut NullSink);
                (
                    usize::from(report.edges().acceptance()),
                    usize::from(report.edges().refusal()),
                )
            })
            .collect();
        assert_eq!(
            Vec::from([
                (6_usize, 0_usize),
                (10_usize, 0_usize),
                (14_usize, 0_usize),
                (18_usize, 0_usize),
            ]),
            edges,
            "four edges per rung over two at the bottom: a rung's goal holds its two \
             unfoldings and its pair's entry, the pair holds one edge to the shared rung \
             below, and the bottom holds its two unfoldings"
        );
    }

    #[test]
    fn an_acceptance_is_keyed_on_its_winning_derivation()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let returned = core.computation_return(unit);
        let lambda = core.computation_lambda(returned);
        let constant = core.value_thunk(lambda);
        let head = core.value_constant(Name::Zero.constant());
        let units = core.value_pair(unit, unit);
        let left = call(&mut core, head, &[unit]);
        let right = call(&mut core, head, &[units]);
        let world = World::new(core, &[(Name::Zero, constant)]);

        let report = world.run(Sides::Computations(left, right), &mut NullSink);
        assert_eq!(
            MachineVerdict::Convertible,
            report.verdict(),
            "a constant function meets itself at any two arguments"
        );
        assert_eq!(
            (1_usize, 0_usize),
            (
                usize::from(report.edges().acceptance()),
                usize::from(report.edges().refusal()),
            ),
            "the root rests on its unfolding branch alone, which closes the two results by \
             their one source term and holds one edge, to the definition; the shortcut's \
             edge to its refuted entry on the arguments is not the root's, and that entry \
             holds none"
        );
    }

    #[test]
    fn a_refusal_is_keyed_on_the_union_over_its_branches()
    {
        let mut core = CoreArena::new();
        let occurrence = innermost(&mut core);
        let unit = core.value_unit();
        let paired = core.value_pair(occurrence, unit);
        let returned = core.computation_return(paired);
        let lambda = core.computation_lambda(returned);
        let function = core.value_thunk(lambda);
        let head = core.value_constant(Name::Zero.constant());
        let units = core.value_pair(unit, unit);
        let left = call(&mut core, head, &[unit]);
        let right = call(&mut core, head, &[units]);
        let world = World::new(core, &[(Name::Zero, function)]);

        let report = world.run(Sides::Computations(left, right), &mut NullSink);
        assert_eq!(
            MachineVerdict::NotConvertible,
            report.verdict(),
            "the function keeps its argument, and the arguments differ"
        );
        assert_eq!(
            (0_usize, 2_usize),
            (
                usize::from(report.edges().acceptance()),
                usize::from(report.edges().refusal()),
            ),
            "the root holds the union over its three branches: the shortcut's edge to its \
             entry on the arguments, and the definition the other two unfolded before \
             refuting; the arguments' guard-separated entry holds none"
        );
    }

    #[test]
    fn a_goal_resting_on_itself_declines_on_the_cycle()
    {
        let mut core = CoreArena::new();
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let unit = core.value_unit();
        let left = core.value_pair(zero, unit);
        let right = core.value_pair(one, unit);
        let world = World::new(core, &[(Name::Zero, left), (Name::One, right)]);
        let sides = Sides::Values(zero, one);

        let reshared = world.run(sides, &mut NullSink);
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Cycle),
            reshared.verdict(),
            "each constant unfolds to a pair holding itself, so the goal on the first \
             components decomposes into itself and waits on itself"
        );
        let settings = MachineSettings::new(
            SchedulingPolicy::default(),
            GranularityPolicy::default(),
            StepBudget::from(10_000_u64),
        );
        let memoless = world.run_with::<_, NullMemo>(settings, sides, &mut NullSink);
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Budget),
            memoless.verdict(),
            "without re-sharing every lap starts a fresh goal, and only the budget ends them"
        );
    }

    #[test]
    fn the_memo_never_moves_a_verdict()
    {
        let (world, cases) = catalogue();
        for (sides, expected) in cases {
            let reshared = world.run(sides, &mut NullSink);
            let memoless =
                world.run_with::<_, NullMemo>(MachineSettings::default(), sides, &mut NullSink);
            assert_eq!(
                (expected, expected),
                (reshared.verdict(), memoless.verdict()),
                "{sides:?}"
            );
        }
    }

    #[test]
    fn the_kernel_certifies_every_catalogue_and_ladder_trace()
    {
        let (world, cases) = catalogue();
        for (sides, expected) in cases {
            let (verdict, decisions) = world.traced(sides);
            assert_eq!(expected, verdict, "{sides:?}");
            assert_eq!(
                certified(verdict),
                world.replayed(sides, verdict, &decisions),
                "{sides:?}: {decisions:?}"
            );
        }
        let (world, rungs) = ladders();
        for sides in rungs {
            let (verdict, decisions) = world.traced(sides);
            assert_eq!(MachineVerdict::Convertible, verdict, "{sides:?}");
            assert_eq!(
                KernelVerdict::Convertible,
                world.replayed(sides, verdict, &decisions),
                "{sides:?}: {decisions:?}"
            );
        }
    }

    #[test]
    fn the_kernel_certifies_every_spinal_catalogue_and_ladder_trace()
    {
        let (world, cases) = catalogue();
        for (sides, expected) in cases {
            let (report, decisions) = world.spinal(MachineSettings::default(), sides);
            assert_eq!(expected, report.verdict(), "{sides:?}");
            assert_eq!(
                certified(report.verdict()),
                world.replayed(sides, report.verdict(), &decisions),
                "{sides:?}: {decisions:?}"
            );
        }
        let (world, rungs) = ladders();
        for sides in rungs {
            let (report, decisions) = world.spinal(MachineSettings::default(), sides);
            assert_eq!(MachineVerdict::Convertible, report.verdict(), "{sides:?}");
            assert_eq!(
                KernelVerdict::Convertible,
                world.replayed(sides, report.verdict(), &decisions),
                "{sides:?}: {decisions:?}"
            );
        }
    }

    #[test]
    fn a_trace_naming_the_wrong_branch_is_refused()
    {
        let (world, cases) = catalogue();
        for (sides, _) in cases {
            let (verdict, decisions) = world.traced(sides);
            let opposite = match verdict {
                | MachineVerdict::Convertible => MachineVerdict::NotConvertible,
                | MachineVerdict::NotConvertible => MachineVerdict::Convertible,
                | MachineVerdict::Declined(reason) => MachineVerdict::Declined(reason),
            };
            assert!(
                matches!(
                    world.replayed(sides, opposite, &decisions),
                    KernelVerdict::Declined(ReplayDecline::Refused(_))
                ),
                "a derivation of one verdict never replays as the other: {sides:?}"
            );
        }

        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let world = World::new(core, &[(Name::Zero, first), (Name::One, second)]);
        let sides = Sides::Values(zero, one);
        let (verdict, mut decisions) = world.traced(sides);
        let position = decisions
            .iter()
            .position(|decision| {
                matches!(*decision,
            ConversionDecision::ReduceRight { redex } if redex == named(Name::One))
            })
            .expect("the right definition unfolds before the heads meet");
        decisions[position] = ConversionDecision::ReduceLeft {
            redex: named(Name::One),
        };
        assert_eq!(
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(position),
            })),
            world.replayed(sides, verdict, &decisions),
            "the right side's unfolding read on the left, where the head is already unit"
        );
    }

    /// The pair's first components diverge — the left one forces a
    /// definition that runs Ω, at height one — and its second components
    /// refute after sixteen forced unfoldings down a chain whose head starts
    /// at height seventeen. A fair schedule gives the refutation every other
    /// turn and answers well inside the budget; the height-weighted schedule
    /// gives the shallow divergence the turns, so the same budget runs out
    /// first. The machine's decline is the kernel's: it has no search of its
    /// own, so it replays nothing and certifies nothing, while the fair run's
    /// trace replays without ever entering the divergence.
    #[test]
    fn an_unlucky_schedule_declines_and_the_kernel_with_it()
    {
        let mut core = CoreArena::new();
        let occurrence = innermost(&mut core);
        let self_applied = call(&mut core, occurrence, &[occurrence]);
        let lambda = core.computation_lambda(self_applied);
        let omega = core.value_thunk(lambda);
        let looping = call(&mut core, omega, &[omega]);
        let diverging = core.value_thunk(looping);
        let mut bodies = Vec::new();
        let runaway = next_constant(&mut bodies, diverging);
        let unit = core.value_unit();
        let mut deep = next_constant(&mut bodies, unit);
        for _height in 0_u32 .. 15_u32 {
            let below = core.value_constant(deep);
            deep = next_constant(&mut bodies, below);
        }
        let runaway = core.value_constant(runaway);
        let forced = core.computation_force(runaway);
        let started = core.value_thunk(forced);
        let returned = core.computation_return(unit);
        let settled = core.value_thunk(returned);
        let deep = core.value_constant(deep);
        let units = core.value_pair(unit, unit);
        let left = core.value_pair(started, deep);
        let right = core.value_pair(settled, units);
        let world = World::stacked(core, &bodies);
        let sides = Sides::Values(left, right);

        let budget = StepBudget::from(2_000_u64);
        let under = |stance| {
            MachineSettings::new(
                SchedulingPolicy::new(stance),
                GranularityPolicy::default(),
                budget,
            )
        };
        let mut log = TraceLog::new();
        let fair = world.run_under(under(SchedulingStance::UniformFair), sides, &mut log);
        assert_eq!(
            MachineVerdict::NotConvertible,
            fair.verdict(),
            "the fair schedule reaches the refutation in {} steps",
            u64::from(fair.steps())
        );
        let decisions: Vec<_> = log.decisions().copied().collect();
        assert_eq!(
            KernelVerdict::NotConvertible,
            world.replayed(sides, fair.verdict(), &decisions),
            "{decisions:?}"
        );

        let mut log = TraceLog::new();
        let starved = world.run_under(under(SchedulingStance::HeightWeighted), sides, &mut log);
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Budget),
            starved.verdict(),
            "the weighted schedule spends the budget on the divergence"
        );
        let decisions: Vec<_> = log.decisions().copied().collect();
        assert!(
            decisions.is_empty(),
            "a decline emits no derivation: {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::Declined(ReplayDecline::EngineDeclined),
            world.replayed(sides, starved.verdict(), &decisions),
            "and the kernel declines with it, never reading the decline as a refutation"
        );
    }

    /// The unlucky schedule of
    /// [`an_unlucky_schedule_declines_and_the_kernel_with_it`],
    /// its sides evaluated under the spinal stance: the right side's unit is
    /// reached three times and shared.
    #[test]
    fn an_unlucky_spinal_schedule_declines_and_the_kernel_with_it()
    {
        let mut core = CoreArena::new();
        let occurrence = innermost(&mut core);
        let self_applied = call(&mut core, occurrence, &[occurrence]);
        let lambda = core.computation_lambda(self_applied);
        let omega = core.value_thunk(lambda);
        let looping = call(&mut core, omega, &[omega]);
        let diverging = core.value_thunk(looping);
        let mut bodies = Vec::new();
        let runaway = next_constant(&mut bodies, diverging);
        let unit = core.value_unit();
        let mut deep = next_constant(&mut bodies, unit);
        for _height in 0_u32 .. 15_u32 {
            let below = core.value_constant(deep);
            deep = next_constant(&mut bodies, below);
        }
        let runaway = core.value_constant(runaway);
        let forced = core.computation_force(runaway);
        let started = core.value_thunk(forced);
        let returned = core.computation_return(unit);
        let settled = core.value_thunk(returned);
        let deep = core.value_constant(deep);
        let units = core.value_pair(unit, unit);
        let left = core.value_pair(started, deep);
        let right = core.value_pair(settled, units);
        let world = World::stacked(core, &bodies);
        let sides = Sides::Values(left, right);
        assert!(
            world
                .shares(sides)
                .iter()
                .any(|&count| u64::from(count) > 0),
            "the right side reaches its unit three times"
        );

        let budget = StepBudget::from(2_000_u64);
        let under = |stance| {
            MachineSettings::new(
                SchedulingPolicy::new(stance),
                GranularityPolicy::default(),
                budget,
            )
        };
        let (fair, decisions) = world.spinal(under(SchedulingStance::UniformFair), sides);
        assert_eq!(
            MachineVerdict::NotConvertible,
            fair.verdict(),
            "the fair schedule reaches the refutation in {} steps",
            u64::from(fair.steps())
        );
        assert_eq!(
            KernelVerdict::NotConvertible,
            world.replayed(sides, fair.verdict(), &decisions),
            "{decisions:?}"
        );

        let (starved, decisions) = world.spinal(under(SchedulingStance::HeightWeighted), sides);
        assert_eq!(
            MachineVerdict::Declined(DeclineReason::Budget),
            starved.verdict(),
            "the weighted schedule spends the budget on the divergence"
        );
        assert!(
            decisions.is_empty(),
            "a decline emits no derivation: {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::Declined(ReplayDecline::EngineDeclined),
            world.replayed(sides, starved.verdict(), &decisions),
            "and the kernel declines with it, never reading the decline as a refutation"
        );
    }

    #[test]
    fn support_store_refusals_preserve_state_and_inactive_operations_do_nothing()
    {
        let missing = ProcessId(usize::MAX);
        let mut inactive =
            crate::resharing::Supports::new(gandr_kernel_check_memo::MemoActivity::Inactive);
        let untouched = inactive.clone();
        inactive
            .open(missing)
            .expect("inactive support stores no process");
        inactive
            .enter(missing)
            .expect("inactive support records no entry");
        inactive
            .unfolded(missing, ConstantIndex::from(0_usize))
            .expect("inactive support records no unfolding");
        inactive
            .settle(missing, crate::rules::Settled::Convertible, &[missing])
            .expect("inactive support records no basis");
        assert_eq!(untouched, inactive);
        assert_eq!(0, usize::from(inactive.totals().acceptance()));
        assert_eq!(0, usize::from(inactive.totals().refusal()));

        let mut active =
            crate::resharing::Supports::new(gandr_kernel_check_memo::MemoActivity::Active);
        let fault = Err(crate::ConversionFault::MachineInvariant);
        let empty = active.clone();
        assert_eq!(fault, active.open(ProcessId(1)));
        assert_eq!(empty, active);
        active.open(ProcessId(0)).expect("zero is the next id");
        let opened = active.clone();
        assert_eq!(fault, active.open(ProcessId(0)));
        assert_eq!(fault, active.open(ProcessId(2)));
        assert_eq!(fault, active.enter(ProcessId(1)));
        assert_eq!(
            fault,
            active.unfolded(ProcessId(1), ConstantIndex::from(0_usize))
        );
        assert_eq!(
            fault,
            active.settle(ProcessId(0), crate::rules::Settled::Convertible, &[
                ProcessId(1)
            ])
        );
        assert_eq!(
            fault,
            active.settle(ProcessId(1), crate::rules::Settled::Convertible, &[])
        );
        assert_eq!(opened, active, "every refusal preserves existing support");
        active.enter(ProcessId(0)).expect("the process is open");
        active
            .unfolded(ProcessId(0), ConstantIndex::from(0_usize))
            .expect("the process is open");
        active
            .unfolded(ProcessId(0), ConstantIndex::from(0_usize))
            .expect("an edge can be consulted again");
        active
            .settle(ProcessId(0), crate::rules::Settled::Convertible, &[])
            .expect("the process is open");
        assert_eq!(1, usize::from(active.totals().acceptance()));
        assert_eq!(0, usize::from(active.totals().refusal()));
    }

    #[test]
    fn support_entries_reference_entries_and_inherit_inner_edges()
    {
        let mut supports =
            crate::resharing::Supports::new(gandr_kernel_check_memo::MemoActivity::Active);
        let [root, inner, child, next] = [ProcessId(0), ProcessId(1), ProcessId(2), ProcessId(3)];
        for process in [root, inner, child, next] {
            supports.open(process).expect("process ids are consecutive");
        }
        for process in [root, child, next] {
            supports.enter(process).expect("each process is open");
        }
        supports
            .unfolded(root, ConstantIndex::from(0_usize))
            .expect("the root lives");
        for _ in 0_u32 .. 2_u32 {
            supports
                .unfolded(inner, ConstantIndex::from(0_usize))
                .expect("the inner process lives");
        }
        supports
            .unfolded(child, ConstantIndex::from(1_usize))
            .expect("the child lives");
        supports
            .settle(inner, crate::rules::Settled::Convertible, &[])
            .expect("the inner process lives");
        assert_eq!(
            0,
            usize::from(supports.totals().acceptance()),
            "inner support is not an entry total"
        );
        supports
            .settle(child, crate::rules::Settled::Convertible, &[])
            .expect("the child lives");
        assert_eq!(1, usize::from(supports.totals().acceptance()));
        supports
            .settle(root, crate::rules::Settled::NotConvertible, &[
                inner, child, inner, child,
            ])
            .expect("every basis process lives");
        assert_eq!(1, usize::from(supports.totals().acceptance()));
        assert_eq!(
            2,
            usize::from(supports.totals().refusal()),
            "one inherited unfolding and one referenced entry, without duplicates"
        );
        supports
            .settle(next, crate::rules::Settled::Convertible, &[root])
            .expect("the root entry lives");
        assert_eq!(
            2,
            usize::from(supports.totals().acceptance()),
            "the root contributes one reference, not its two edges"
        );
        assert_eq!(2, usize::from(supports.totals().refusal()));
    }

    #[test]
    fn derivation_refusals_preserve_state_and_inactive_recording_is_empty()
    {
        let core = CoreArena::new();
        let mut domain = DomainArena::new();
        let value = domain.value_unit(crate::TermFace::Reduced);
        let pair = (crate::Glued::Value(value), crate::Glued::Value(value));
        let marker = ConversionDecision::ComparedShared {
            left: TraceNode::Value(value),
            right: TraceNode::Value(value),
        };
        let missing = ProcessId(usize::MAX);
        let mut inactive = crate::derivation::Derivations::new(
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
        );
        let original = inactive.clone();
        inactive
            .open(missing)
            .expect("inactive recording stores no process");
        inactive
            .decide(missing, marker)
            .expect("inactive recording stores no decision");
        inactive
            .rest_on(missing, Vec::from([missing]))
            .expect("inactive recording stores no children");
        inactive
            .agree_on(missing, pair, Vec::from([missing]))
            .expect("inactive recording stores no pair");
        let mut log = TraceLog::new();
        log.record(marker);
        inactive
            .emit(&core, &domain, missing, &mut log)
            .expect("inactive recording traverses nothing");
        assert_eq!(original, inactive);
        assert_eq!(0, usize::from(inactive.count()));
        assert_eq!(
            Vec::from([marker]),
            log.decisions().copied().collect::<Vec<_>>()
        );

        let mut active = crate::derivation::Derivations::new(
            gandr_kernel_conversion_trace::SinkActivity::Active,
        );
        let empty = active.clone();
        let fault = Err(crate::ConversionFault::MachineInvariant);
        assert_eq!(fault, active.open(ProcessId(1)));
        assert_eq!(empty, active);
        active.open(ProcessId(0)).expect("zero is the next id");
        let opened = active.clone();
        assert_eq!(fault, active.open(ProcessId(0)));
        assert_eq!(fault, active.open(ProcessId(2)));
        assert_eq!(fault, active.decide(ProcessId(1), marker));
        assert_eq!(fault, active.rest_on(ProcessId(1), Vec::new()));
        assert_eq!(fault, active.agree_on(ProcessId(1), pair, Vec::new()));
        assert_eq!(fault, active.emit(&core, &domain, ProcessId(1), &mut log));
        assert_eq!(opened, active);
        assert_eq!(1, usize::from(active.count()));
        assert_eq!(
            Vec::from([marker]),
            log.decisions().copied().collect::<Vec<_>>()
        );
    }

    #[test]
    fn derivations_emit_preorder_and_repeat_shared_children()
    {
        let core = CoreArena::new();
        let mut domain = DomainArena::new();
        let [zero, one, two, three, four] =
            [0_u32, 1, 2, 3, 4].map(|_| domain.value_unit(crate::TermFace::Reduced));
        let [start, later, first, second, shared] =
            [zero, one, two, three, four].map(|value| ConversionDecision::ComparedShared {
                left: TraceNode::Value(value),
                right: TraceNode::Value(value),
            });
        let [root, left, right, leaf] = [ProcessId(0), ProcessId(1), ProcessId(2), ProcessId(3)];
        let mut derivations = crate::derivation::Derivations::new(
            gandr_kernel_conversion_trace::SinkActivity::Active,
        );
        for process in [root, left, right, leaf] {
            derivations.open(process).expect("ids are consecutive");
        }
        for (process, decision) in [
            (root, start),
            (root, later),
            (left, first),
            (right, second),
            (leaf, shared),
        ] {
            derivations
                .decide(process, decision)
                .expect("the process is open");
        }
        derivations
            .rest_on(left, Vec::from([leaf]))
            .expect("the left process is open");
        derivations
            .rest_on(right, Vec::from([leaf]))
            .expect("the right process is open");
        derivations
            .rest_on(root, Vec::from([left, right]))
            .expect("the root is open");
        let mut log = TraceLog::new();
        derivations
            .emit(&core, &domain, root, &mut log)
            .expect("the derivation graph is closed");
        assert_eq!(
            Vec::from([start, later, first, shared, second, shared]),
            log.decisions().copied().collect::<Vec<_>>()
        );
        assert_eq!(4, usize::from(derivations.count()));
        derivations
            .rest_on(right, Vec::from([ProcessId(4)]))
            .expect("the parent process is open");
        let mut broken = TraceLog::new();
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            derivations.emit(&core, &domain, root, &mut broken)
        );
        assert_eq!(
            Vec::from([start, later, first, shared, second]),
            broken.decisions().copied().collect::<Vec<_>>(),
            "a missing child refuses after the preceding preorder prefix"
        );
    }

    #[test]
    fn empty_choices_refuse_instead_of_producing_a_refutation()
    {
        let core = CoreArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(crate::TermFace::Reduced);
        let mut scheduler = super::Scheduler::<NullMemo>::new(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        for combination in [
            super::Combine::Biased(Vec::new()),
            super::Combine::Either(Vec::new()),
        ] {
            let mut goal = super::Goal {
                left: super::Slot::Ready(crate::Glued::Value(unit)),
                right: super::Slot::Ready(crate::Glued::Value(unit)),
                depth: crate::BinderLevel::from(0_u32),
                frozen: super::Frozen::default(),
                chain: super::Chain::default(),
                next: super::Next::Classify,
            };
            let root = scheduler
                .start_goal(goal.clone())
                .expect("the pending goal is admitted");
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                scheduler.combine(root, &mut goal, combination)
            );
            assert_eq!(Ok(super::Outcome::Pending), scheduler.outcome(root));
        }
        let mut goal = super::Goal {
            left: super::Slot::Ready(crate::Glued::Value(unit)),
            right: super::Slot::Ready(crate::Glued::Value(unit)),
            depth: crate::BinderLevel::from(0_u32),
            frozen: super::Frozen::default(),
            chain: super::Chain::default(),
            next: super::Next::Classify,
        };
        let root = scheduler
            .start_goal(goal.clone())
            .expect("the zero-premise goal is admitted");
        assert_eq!(
            Ok(super::Turn::Done),
            scheduler.combine(root, &mut goal, super::Combine::All {
                pair: (crate::Glued::Value(unit), crate::Glued::Value(unit)),
                children: Vec::new(),
                collapse: super::Collapse::Allowed,
            })
        );
        assert_eq!(
            Ok(super::Outcome::Settled(super::Settled::Convertible)),
            scheduler.outcome(root)
        );
    }

    #[test]
    fn step_counter_overflow_cannot_disable_the_budget_backstop()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let first_body = core.computation_return(unit);
        let second_body = core.computation_return(unit);
        let first = core.value_thunk(first_body);
        let second = core.value_thunk(second_body);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let left = eval_value(&core, &mut domain, definitions, Fuel::from(8_u32), first)
            .expect("the first thunk evaluates");
        let right = eval_value(&core, &mut domain, definitions, Fuel::from(8_u32), second)
            .expect("the second thunk evaluates");
        let settings = MachineSettings::new(
            SchedulingPolicy::default(),
            GranularityPolicy::default(),
            StepBudget::from(u64::MAX),
        );
        for (other, expected) in [
            (right, MachineVerdict::Declined(DeclineReason::Budget)),
            (left, MachineVerdict::Convertible),
        ] {
            let mut scheduler = super::Scheduler::<NullMemo>::new(
                &core,
                &mut domain,
                definitions,
                settings,
                gandr_kernel_conversion_trace::SinkActivity::Inactive,
                NullMemo,
            );
            let root = scheduler
                .start_fresh(
                    crate::resharing::SupportSides::Heads(
                        crate::Glued::Value(left),
                        crate::Glued::Value(other),
                    ),
                    crate::BinderLevel::from(0_u32),
                )
                .expect("the root goal is admitted");
            scheduler.spent = super::StepCount(u64::MAX);
            assert_eq!(
                Ok(expected),
                scheduler.run(root),
                "a pending root must not run past an overflow; an answer on the same turn still wins"
            );
        }
    }

    #[test]
    fn binder_ceiling_is_refused_before_opening_or_eta_allocation()
    {
        for eta in [false, true] {
            for memo in [false, true] {
                let mut core = CoreArena::new();
                let unit = core.value_unit();
                let returned = core.computation_return(unit);
                let left = core.computation_lambda(returned);
                let right = if eta {
                    let rigid = core.value_constant(Name::Rigid.constant());
                    core.computation_force(rigid)
                }
                else {
                    let pair = core.value_pair(unit, unit);
                    let returned = core.computation_return(pair);
                    core.computation_lambda(returned)
                };
                let chain = LoweredChain::new();
                let environment = DefinitionalEnvironment::new();
                let definitions = Definitions::new(&chain, &environment, environment.root());
                let mut domain = DomainArena::new();
                let left =
                    eval_computation(&core, &mut domain, definitions, Fuel::from(32_u32), left)
                        .expect("the lambda evaluates without entering its binder");
                let right =
                    eval_computation(&core, &mut domain, definitions, Fuel::from(32_u32), right)
                        .expect("the other head evaluates without entering its binder");
                let problem =
                    Problem::computations(left, right).under(crate::BinderLevel::from(u32::MAX));
                let mark = domain.watermark();
                let result = if memo {
                    decide::<_, ResharingMemo>(
                        &core,
                        &mut domain,
                        definitions,
                        MachineSettings::default(),
                        problem,
                        &mut NullSink,
                    )
                }
                else {
                    decide::<_, NullMemo>(
                        &core,
                        &mut domain,
                        definitions,
                        MachineSettings::default(),
                        problem,
                        &mut NullSink,
                    )
                };
                assert_eq!(
                    Err(crate::ConversionFault::MachineInvariant),
                    result,
                    "eta={eta}, memo={memo}"
                );
                assert_eq!(
                    mark,
                    domain.watermark(),
                    "an impossible deeper level mints no fresh variable"
                );
            }
        }
    }

    #[test]
    fn completed_premises_wake_a_later_decomposition()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let body = core.computation_return(unit);
        let first = core.value_thunk(body);
        let other_unit = core.value_unit();
        let other_body = core.computation_return(other_unit);
        let second = core.value_thunk(other_body);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let left = eval_value(&core, &mut domain, definitions, Fuel::from(32_u32), first)
            .expect("the first thunk evaluates");
        let right = eval_value(&core, &mut domain, definitions, Fuel::from(32_u32), second)
            .expect("the second thunk evaluates");
        let mut left_tail = domain.value_pair(left, left, crate::TermFace::Reduced);
        let mut right_tail = domain.value_pair(right, right, crate::TermFace::Reduced);
        let padding = domain.value_unit(crate::TermFace::Reduced);
        for _depth in 0_u32 .. 8_u32 {
            left_tail = domain.value_pair(padding, left_tail, crate::TermFace::Reduced);
            right_tail = domain.value_pair(padding, right_tail, crate::TermFace::Reduced);
        }
        let left_root = domain.value_pair(left, left_tail, crate::TermFace::Reduced);
        let right_root = domain.value_pair(right, right_tail, crate::TermFace::Reduced);
        let problem = Problem::values(left_root, right_root);
        let mut independent = domain.clone();
        let reshared = decide::<_, ResharingMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            problem,
            &mut NullSink,
        )
        .expect("the shared run remains well formed");
        let memoless = decide::<_, NullMemo>(
            &core,
            &mut independent,
            definitions,
            MachineSettings::default(),
            problem,
            &mut NullSink,
        )
        .expect("the independent run remains well formed");
        assert_eq!(MachineVerdict::Convertible, memoless.verdict());
        assert_eq!(
            MachineVerdict::Convertible,
            reshared.verdict(),
            "completed premises cannot send another wakeup and must not become a cycle"
        );
    }

    #[test]
    fn invalid_roots_refuse_before_identity_or_search()
    {
        let mut core = CoreArena::new();
        let source = core.value_unit();
        let returned = core.computation_return(source);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let mark = domain.watermark();
        let value = eval_value(&core, &mut domain, definitions, Fuel::from(8_u32), source)
            .expect("the value evaluates before truncation");
        let computation =
            eval_computation(&core, &mut domain, definitions, Fuel::from(8_u32), returned)
                .expect("the computation evaluates before truncation");
        domain.truncate_to(mark);
        for (problem, expected) in [
            (
                Problem::values(value, value),
                crate::ConversionFault::Domain(crate::DomainFault::Dangling),
            ),
            (
                Problem::computations(computation, computation),
                crate::ConversionFault::Domain(crate::DomainFault::Dangling),
            ),
            (
                Problem {
                    left: crate::Glued::Value(value),
                    right: crate::Glued::Computation(computation),
                    depth: crate::BinderLevel::FLOOR,
                },
                crate::ConversionFault::Polarity,
            ),
        ] {
            assert_eq!(
                Err(expected),
                decide::<_, ResharingMemo>(
                    &core,
                    &mut domain,
                    definitions,
                    MachineSettings::default(),
                    problem,
                    &mut NullSink
                )
            );
        }
    }

    #[test]
    fn missing_processes_refuse_without_creating_waits()
    {
        let core = CoreArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(crate::TermFace::Reduced);
        let mut scheduler = super::Scheduler::<NullMemo>::new(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        let missing = ProcessId(0);
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.resolve(super::Slot::Waiting(missing))
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.need(missing)
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.enqueue(missing)
        );
        assert!(
            scheduler.queue.is_empty(),
            "refused processes cannot acquire a queued wakeup"
        );
        let share = scheduler.share_at(super::DefinitionHeight::default());
        let answered = scheduler
            .start(
                super::Work::Spent,
                super::Outcome::Settled(super::Settled::Convertible),
                share,
            )
            .expect("a completed process is admitted");
        let missing = ProcessId(usize::MAX);
        assert_eq!(
            Ok(super::Outcome::Settled(super::Settled::Convertible)),
            scheduler.depend(missing, answered),
            "an answered dependency needs no waiter lookup or edge"
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.resolve(super::Slot::Waiting(answered)),
            "a goal verdict cannot be received as an evaluated head"
        );
        let pending = scheduler
            .start_goal(super::Goal {
                left: super::Slot::Ready(crate::Glued::Value(unit)),
                right: super::Slot::Ready(crate::Glued::Value(unit)),
                depth: crate::BinderLevel::FLOOR,
                frozen: super::Frozen::default(),
                chain: super::Chain::default(),
                next: super::Next::Classify,
            })
            .expect("a pending goal is admitted");
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.depend(missing, pending)
        );
        assert!(
            scheduler
                .process(pending)
                .expect("the dependency remains live")
                .waiters
                .is_empty(),
            "a missing waiter cannot leave a reciprocal edge"
        );
        scheduler
            .enqueue(pending)
            .expect("the first wakeup is queued");
        scheduler
            .enqueue(pending)
            .expect("a repeated wakeup coalesces");
        assert_eq!(
            alloc::collections::VecDeque::from([pending]),
            scheduler.queue
        );
    }

    #[test]
    fn combinators_preserve_answer_and_decline_precedence()
    {
        #[derive(Clone, Copy, Debug)]
        enum Combinator
        {
            All,
            Biased,
            Either,
        }
        let accepted = super::Outcome::Settled(super::Settled::Convertible);
        let refuted = super::Outcome::Settled(super::Settled::NotConvertible);
        let pending = super::Outcome::Pending;
        let cycle = super::Outcome::Declined(DeclineReason::Cycle);
        let budget = super::Outcome::Declined(DeclineReason::Budget);
        let cases: &[(Combinator, &[super::Outcome], super::Outcome)] = &[
            (Combinator::All, &[pending, refuted], refuted),
            (Combinator::All, &[cycle, refuted], refuted),
            (Combinator::All, &[accepted, pending], pending),
            (Combinator::All, &[cycle, pending], pending),
            (Combinator::All, &[accepted, accepted], accepted),
            (Combinator::All, &[cycle, budget], cycle),
            (Combinator::All, &[pending, refuted, pending], refuted),
            (Combinator::All, &[accepted, cycle, budget], cycle),
            (Combinator::Biased, &[accepted, pending], accepted),
            (Combinator::Biased, &[refuted, pending], pending),
            (Combinator::Biased, &[pending, refuted], refuted),
            (Combinator::Biased, &[pending, cycle], pending),
            (Combinator::Biased, &[cycle, budget], budget),
            (Combinator::Biased, &[pending, accepted, pending], accepted),
            (Combinator::Either, &[pending, accepted], accepted),
            (Combinator::Either, &[refuted, pending], pending),
            (Combinator::Either, &[cycle, pending], pending),
            (Combinator::Either, &[refuted, refuted], refuted),
            (Combinator::Either, &[cycle, budget], cycle),
            (Combinator::Either, &[pending, accepted, pending], accepted),
            (Combinator::Either, &[refuted, cycle, budget], cycle),
        ];
        for &(kind, inputs, expected) in cases {
            let core = CoreArena::new();
            let chain = LoweredChain::new();
            let environment = DefinitionalEnvironment::new();
            let definitions = Definitions::new(&chain, &environment, environment.root());
            let mut domain = DomainArena::new();
            let unit = domain.value_unit(crate::TermFace::Reduced);
            let pair = (crate::Glued::Value(unit), crate::Glued::Value(unit));
            let mut goal = super::Goal {
                left: super::Slot::Ready(pair.0),
                right: super::Slot::Ready(pair.1),
                depth: crate::BinderLevel::FLOOR,
                frozen: super::Frozen::default(),
                chain: super::Chain::default(),
                next: super::Next::Classify,
            };
            let mut scheduler = super::Scheduler::<NullMemo>::new(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                gandr_kernel_conversion_trace::SinkActivity::Inactive,
                NullMemo,
            );
            let root = scheduler
                .start_goal(goal.clone())
                .expect("the parent is admitted");
            let mut children = Vec::new();
            for &outcome in inputs {
                let work = if outcome == pending {
                    super::Work::Goal(goal.clone())
                }
                else {
                    super::Work::Spent
                };
                let share = scheduler.share_at(super::DefinitionHeight::default());
                children.push(
                    scheduler
                        .start(work, outcome, share)
                        .expect("the child state is admitted"),
                );
            }
            let combine = match kind {
                | Combinator::All => super::Combine::All {
                    pair,
                    children,
                    collapse: super::Collapse::Never,
                },
                | Combinator::Biased => super::Combine::Biased(children),
                | Combinator::Either => super::Combine::Either(children),
            };
            let expected_turn = if expected == pending {
                super::Turn::Wait
            }
            else {
                super::Turn::Done
            };
            assert_eq!(
                Ok(expected_turn),
                scheduler.combine(root, &mut goal, combine),
                "{kind:?}: {inputs:?}"
            );
            assert_eq!(
                Ok(expected),
                scheduler.outcome(root),
                "{kind:?}: {inputs:?}"
            );
        }
    }

    #[test]
    fn malformed_heads_and_channel_entries_are_refused()
    {
        let core = CoreArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(crate::TermFace::Reduced);
        let returned = domain.comp_return(unit, crate::CompTermFace::Reduced);
        let variable = domain
            .neutral_node(
                crate::NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: crate::BinderLevel::FLOOR,
                },
                Vec::new(),
                crate::Unfolding::Rigid,
            )
            .expect("a variable is rigid");
        let module = domain
            .neutral_node(
                crate::NeutralHead::Module(Name::Zero.constant()),
                Vec::new(),
                crate::Unfolding::Rigid,
            )
            .expect("a module is rigid");
        let rigid = domain
            .neutral_node(
                crate::NeutralHead::Constant(Name::Rigid.constant()),
                Vec::new(),
                crate::Unfolding::Rigid,
            )
            .expect("an opaque constant is rigid");
        let wrong_body = domain
            .neutral_node(
                crate::NeutralHead::Constant(Name::Zero.constant()),
                Vec::new(),
                crate::Unfolding::Forced(crate::Glued::Computation(returned)),
            )
            .expect("the domain can hold a computation unfolding");
        let mark = domain.watermark();
        let stale_value = domain.value_unit(crate::TermFace::Reduced);
        let stale_computation = domain.comp_return(unit, crate::CompTermFace::Reduced);
        let stale_neutral = domain
            .neutral_node(
                crate::NeutralHead::Constant(Name::One.constant()),
                Vec::new(),
                crate::Unfolding::Rigid,
            )
            .expect("the later neutral initially resolves");
        domain.truncate_to(mark);
        let mut scheduler = super::Scheduler::<NullMemo>::new(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        for head in [
            crate::Glued::Value(unit),
            crate::Glued::Computation(returned),
        ] {
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                scheduler.neutral_of(head)
            );
        }
        for head in [
            crate::Glued::Value(stale_value),
            crate::Glued::Computation(stale_computation),
        ] {
            assert_eq!(
                Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
                scheduler.neutral_of(head)
            );
        }
        for head in [variable, module] {
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                scheduler.head_constant(head)
            );
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                scheduler.unfold_channel(head)
            );
        }
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            scheduler.head_constant(stale_neutral)
        );
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            scheduler.unfold_channel(stale_neutral)
        );
        for head in [rigid, wrong_body] {
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                scheduler.unfold_channel(head)
            );
        }
        assert_eq!(
            Err(crate::ConversionFault::Evaluation(
                crate::EvalFault::DanglingTerm
            )),
            scheduler.body_channel(GlobalIndex::from(0_u32), super::DefinitionHeight::default())
        );
    }

    #[test]
    fn opened_channels_preserve_distinct_binder_levels()
    {
        let mut core = CoreArena::new();
        let variable = innermost(&mut core);
        let returned = core.computation_return(variable);
        let lambda = core.computation_lambda(returned);
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let lambda = eval_computation(&core, &mut domain, definitions, Fuel::from(16_u32), lambda)
            .expect("the lambda suspends its binder body");
        let Some(&crate::DomainComp::Lambda { body, .. }) = domain.computation(lambda)
        else {
            panic!("the evaluated head is a lambda");
        };
        let mut scheduler = super::Scheduler::<NullMemo>::new(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        for level in [0_u32, 1_u32, 0_u32] {
            let level = crate::BinderLevel::from(level);
            let channel = scheduler
                .open_channel(body, level)
                .expect("the closure opens at this level");
            if scheduler.outcome(channel) == Ok(super::Outcome::Pending) {
                assert_eq!(Ok(super::Turn::Done), scheduler.turn(channel));
            }
            let Ok(super::Outcome::Evaluated(crate::Glued::Computation(result))) =
                scheduler.outcome(channel)
            else {
                panic!("the opening channel returns a computation");
            };
            let Some(&crate::DomainComp::Return { value, .. }) =
                scheduler.domain.computation(result)
            else {
                panic!("the body returns its fresh variable");
            };
            let Some(&crate::DomainValue::Neutral { neutral, .. }) = scheduler.domain.value(value)
            else {
                panic!("the returned variable remains neutral");
            };
            assert_eq!(
                crate::NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level
                },
                scheduler
                    .domain
                    .neutral(neutral)
                    .expect("the fresh neutral resolves")
                    .head()
            );
        }
        assert_eq!(
            2_usize,
            scheduler.processes.len(),
            "a completed opening at the same level is reused"
        );
    }

    #[test]
    fn head_height_is_symmetric_and_nonconstants_stay_at_the_floor()
    {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let first = core.value_constant(Name::Zero.constant());
        let second = core.value_constant(Name::One.constant());
        let first_force = core.computation_force(first);
        let second_force = core.computation_force(second);
        let world = World::stacked(core, &[
            (GlobalIndex::from(0_u32), body),
            (GlobalIndex::from(1_u32), body),
        ]);
        let definitions =
            Definitions::new(&world.chain, &world.environment, world.environment.root());
        let mut domain = DomainArena::new();
        let first = eval_value(
            &world.core,
            &mut domain,
            definitions,
            Fuel::from(16_u32),
            first,
        )
        .expect("the first head evaluates");
        let second = eval_value(
            &world.core,
            &mut domain,
            definitions,
            Fuel::from(16_u32),
            second,
        )
        .expect("the second head evaluates");
        let first_force = eval_computation(
            &world.core,
            &mut domain,
            definitions,
            Fuel::from(16_u32),
            first_force,
        )
        .expect("the first force is neutral");
        let second_force = eval_computation(
            &world.core,
            &mut domain,
            definitions,
            Fuel::from(16_u32),
            second_force,
        )
        .expect("the second force is neutral");
        let unit = domain.value_unit(crate::TermFace::Reduced);
        let scheduler = super::Scheduler::<NullMemo>::new(
            &world.core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        for (left, right) in [
            (crate::Glued::Value(first), crate::Glued::Value(second)),
            (
                crate::Glued::Computation(first_force),
                crate::Glued::Computation(second_force),
            ),
        ] {
            for pair in [(left, right), (right, left)] {
                assert_eq!(
                    2_u32,
                    u32::from(scheduler.pair_height(pair).expect("both heads resolve"))
                );
            }
        }
        assert_eq!(
            0_u32,
            u32::from(
                scheduler
                    .pair_height((crate::Glued::Value(unit), crate::Glued::Value(unit)))
                    .expect("formers have floor height")
            )
        );
    }

    #[test]
    fn lifting_shares_equal_trees_without_reusing_occurrence_nodes()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let left = core.value_pair(first, second);
        let third = core.value_unit();
        let fourth = core.value_unit();
        let right = core.value_pair(third, fourth);
        let root = core.value_pair(left, right);
        let mut world = World::new(core, &[]);
        assert_eq!(
            [0_u64, 0_u64],
            world.shares(Sides::Values(first, second)).map(u64::from)
        );
        assert_eq!(
            [2_u64, 2_u64],
            world.shares(Sides::Values(root, root)).map(u64::from),
            "the repeated unit and repeated pair each have one shared leg"
        );
        let (overlay, lifted_root) = lifted(&world.core, CoreTerm::Value(root));
        assert_eq!(
            Ok(()),
            overlay.validate(lifted_root),
            "each occurrence is a distinct overlay node"
        );
        let OverlayId::Value(lifted_root) = lifted_root
        else {
            panic!("a value lifts to a value");
        };
        let erased = crate::overlay::erase_value(&overlay, lifted_root, &mut world.core)
            .expect("the lifted tree erases");
        let Some(&Value::Pair(first, second)) = world.core.value(erased)
        else {
            panic!("the root is still a pair");
        };
        assert_eq!(first, second, "erasure reuses the shared pair leg");
        let Some(&Value::Pair(first, second)) = world.core.value(first)
        else {
            panic!("each component is still a pair");
        };
        assert_eq!(first, second, "erasure reuses the shared unit leg");
        assert_eq!(Some(&Value::Unit), world.core.value(first));
    }

    #[test]
    fn closed_codes_are_certified_in_both_type_families()
    {
        let mut core = CoreArena::new();
        let first_unit = core.value_type_unit();
        let second_unit = core.value_type_unit();
        let first_returner = core.comp_type_returner(first_unit);
        let second_returner = core.comp_type_returner(second_unit);
        let first_arrow = core.comp_type_arrow(first_unit, first_returner);
        let second_arrow = core.comp_type_arrow(second_unit, second_returner);
        let first_thunk = core.value_type_thunk(first_returner);
        let second_thunk = core.value_type_thunk(second_returner);
        let first_value_code = core.value_quote(first_thunk);
        let second_value_code = core.value_quote(second_thunk);
        let first_comp_code = core.value_quote_computation(first_arrow);
        let second_comp_code = core.value_quote_computation(second_arrow);
        let different_comp_code = core.value_quote_computation(first_returner);
        let first = core.computation_return(first_comp_code);
        let second = core.computation_return(second_comp_code);
        let world = World::new(core, &[]);
        for (sides, expected) in [
            (
                Sides::Values(first_value_code, second_value_code),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Values(first_comp_code, second_comp_code),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Values(first_comp_code, different_comp_code),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Computations(first, second),
                MachineVerdict::Convertible,
            ),
        ] {
            let (verdict, decisions) = world.traced(sides);
            assert_eq!(expected, verdict, "{sides:?}");
            assert_eq!(
                certified(expected),
                world.replayed(sides, verdict, &decisions),
                "{sides:?}: {decisions:?}"
            );
        }
    }

    #[test]
    fn native_records_cases_and_traces_agree()
    {
        use alloc::string::String;

        use gandr_core_term::ConstructorTag;
        use gandr_core_term::FieldLabel;
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let other_unit = core.value_unit();
        let x = FieldLabel::from(String::from("x"));
        let y = FieldLabel::from(String::from("y"));
        let record = core.value_record(BTreeMap::from([(x.clone(), unit), (y.clone(), unit)]));
        let repeated_record = core.value_record(BTreeMap::from([
            (x.clone(), other_unit),
            (y.clone(), other_unit),
        ]));
        let narrow = core.value_record(BTreeMap::from([(x.clone(), unit)]));
        let data = core.value_type_data(ConstantIndex::from(2_usize), Vec::from([unit]));
        let repeated_type =
            core.value_type_data(ConstantIndex::from(2_usize), Vec::from([other_unit]));
        let other_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([unit]));
        let constructor =
            core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([record]));
        let repeated_constructor = core.value_constructor(
            repeated_type,
            ConstructorTag::from(0_usize),
            Vec::from([repeated_record]),
        );
        let other_tag =
            core.value_constructor(data, ConstructorTag::from(1_usize), Vec::from([record]));
        let other_constructor = core.value_constructor(
            other_type,
            ConstructorTag::from(0_usize),
            Vec::from([record]),
        );
        let bound = innermost(&mut core);
        let identity = core.computation_return(bound);
        let branch = core.computation_lambda(identity);
        let unit_type = core.value_type_unit();
        let record_type = core.value_type_record(BTreeMap::from([
            (x.clone(), unit_type),
            (y.clone(), unit_type),
        ]));
        let motive = core.comp_type_returner(record_type);
        let named_data = core.value_constant(Name::Zero.constant());
        let named_record = core.value_constant(Name::One.constant());
        let fired = core.computation_data_case(named_data, motive, Vec::from([branch]));
        let expected_record = core.computation_return(record);
        let projection = core.computation_record_projection(named_record, x.clone());
        let expected_unit = core.computation_return(unit);
        let rigid = core.value_constant(Name::Rigid.constant());
        let motive_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([bound]));
        let dependent_motive = core.comp_type_returner(motive_type);
        let reconstructed =
            core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([bound]));
        let result_type =
            core.value_type_data(ConstantIndex::from(3_usize), Vec::from([reconstructed]));
        let result = core.value_constructor(
            result_type,
            ConstructorTag::from(0_usize),
            Vec::from([unit]),
        );
        let different_result = core.value_constructor(
            result_type,
            ConstructorTag::from(1_usize),
            Vec::from([unit]),
        );
        let result = core.computation_return(result);
        let different_result = core.computation_return(different_result);
        let result = core.computation_lambda(result);
        let different_result = core.computation_lambda(different_result);
        let first_case = core.computation_data_case(rigid, dependent_motive, Vec::from([result]));
        let repeated_case =
            core.computation_data_case(rigid, dependent_motive, Vec::from([result]));
        let changed_case =
            core.computation_data_case(rigid, dependent_motive, Vec::from([different_result]));
        let empty_case = core.computation_data_case(rigid, dependent_motive, Vec::new());
        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let outer_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([outer]));
        let outer_motive = core.comp_type_returner(outer_type);
        let outer_case = core.computation_data_case(rigid, outer_motive, Vec::from([result]));
        let under_binder = core.computation_lambda(first_case);
        let capturing_motive = core.computation_lambda(outer_case);
        let rigid_projection = core.computation_record_projection(rigid, x.clone());
        let repeated_projection = core.computation_record_projection(rigid, x);
        let other_projection = core.computation_record_projection(rigid, y);
        let world = World::new(core, &[(Name::Zero, constructor), (Name::One, record)]);
        for (sides, expected) in [
            (
                Sides::Values(record, repeated_record),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Values(record, narrow),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Values(constructor, repeated_constructor),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Values(constructor, other_tag),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Values(constructor, other_constructor),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Computations(fired, expected_record),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Computations(projection, expected_unit),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Computations(first_case, repeated_case),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Computations(first_case, changed_case),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Computations(first_case, empty_case),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Computations(under_binder, capturing_motive),
                MachineVerdict::NotConvertible,
            ),
            (
                Sides::Computations(rigid_projection, repeated_projection),
                MachineVerdict::Convertible,
            ),
            (
                Sides::Computations(rigid_projection, other_projection),
                MachineVerdict::NotConvertible,
            ),
        ] {
            let (verdict, decisions) = world.traced(sides);
            assert_eq!(verdict, expected, "{sides:?}");
            assert_eq!(
                world.replayed(sides, verdict, &decisions),
                certified(expected),
                "{sides:?}: {decisions:?}"
            );
        }
    }
}
