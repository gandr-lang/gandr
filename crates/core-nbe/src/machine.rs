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
/// - requires: both sides live in `domain`, were evaluated under `definitions`,
///   and mention no intuitionistic binder level at or past `problem`'s depth;
///   `core` is the arena their literal payloads and every lowered body live in.
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
///   disagrees with itself.
/// - panics: none.
/// - intension: one rule per goal turn and one evaluation slice per channel
///   turn, round-robin over the run queue under the default scheduling stance.
///
/// # Errors
/// Every variant of [`ConversionFault`]; see its documentation.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the root fast path, the
///   machine's rule arms, its two declines and the memo's hit; each rule arm is
///   separated by a conversion answered through it, both verdicts and both
///   declines are exercised, recording is pinned against the null sink and the
///   live memo against the null memo verdict for verdict, and re-sharing is
///   pinned by exact process and edge counts. Every recorded derivation is
///   replayed by the kernel to the same verdict, a tampered one is refused, and
///   a decline under a starving schedule stays a decline through the kernel.
/// - witness: `machine::tests::the_search_free_steps_answer_before_any_process`
/// - witness: `machine::tests::a_forced_unfolding_meets_a_former`
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
#[inline]
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
}

impl<'run, M> Scheduler<'run, M>
where
    M: CheckMemo<GoalSupport, ProcessId>,
{
    /// An empty run over an empty `memo`.
    ///
    /// # Specification
    /// trivial.
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
            | SupportSides::Heads(left, right) => Goal {
                left: Slot::Ready(left),
                right: Slot::Ready(right),
                depth: level,
                frozen: Frozen::default(),
                chain: Chain::default(),
                next: Next::Classify,
            },
            | SupportSides::Opened(left, right) => {
                let left = self.open_channel(left, level)?;
                let right = self.open_channel(right, level)?;
                let deeper = deeper(level)?;
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
    ///   left alone.
    /// - provides: the one place an edge of the wait map is drawn.
    /// - fails: [`ConversionFault::MachineInvariant`] for an id the arena does
    ///   not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — an id the arena does not hold.
    fn depend(
        &mut self,
        waiter: ProcessId,
        dependency: ProcessId,
    ) -> Result<(), ConversionFault>
    {
        let outcome = self.outcome(dependency)?;
        if outcome != Outcome::Pending {
            return Ok(());
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
        Ok(())
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
    /// trivial.
    const fn charge(
        &mut self,
        steps: StepCount,
    )
    {
        self.spent = StepCount(self.spent.0.saturating_add(steps.0));
    }

    /// Run until the root answers, the needed goals deadlock, or the budget is
    /// spent.
    ///
    /// # Specification
    /// - requires: `root` is a pending goal.
    /// - ensures: the root's answer, reached by turns taken round-robin over
    ///   the run queue, each process passed over until its credit reaches its
    ///   share; [`DeclineReason::Budget`] once the steps charged pass the
    ///   settings' budget with the root unanswered; [`DeclineReason::Cycle`]
    ///   when the queue empties with the root unanswered under an active memo,
    ///   because every needed process then waits on a pending one and, the
    ///   arena being finite, the waits close into a cycle through a re-shared
    ///   goal.
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
    ///   every evaluation slice charges the steps it ran, at least one; the
    ///   loop returns once the charged steps pass the budget.
    /// - boundedness: the turns that charge nothing are bounded by the ones
    ///   that do. A goal that waits or combines was queued by a dependency
    ///   finishing, at most once per wait edge, and every edge was drawn when a
    ///   charged turn started a process; a channel's re-application turn runs
    ///   once per channel; a process passed over for credit re-queues at most
    ///   its share less one times per turn it takes; a process popped answered
    ///   or unneeded is dropped, once per queuing.
    /// - input recursion: none.
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
            if self.spent.0 > budget {
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
    ///   defined heads it compares.
    /// - provides: the table read once per goal turn.
    /// - fails: every fault the table or the rule raises.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the table or the rule raises.
    fn classify(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
    ) -> Result<Turn, ConversionFault>
    {
        self.charge(StepCount::ONE);
        let planned = plan(self.core, self.domain, &goal.frozen, pair.0, pair.1)?;
        let height = self.pair_height(pair)?;
        let share = self.share_at(height);
        self.process_mut(id)?.share = share;
        match planned {
            | Plan::Shared(settled) => {
                self.derivations
                    .decide(id, ConversionDecision::ComparedShared {
                        left: TraceNode::of(pair.0),
                        right: TraceNode::of(pair.1),
                    })?;
                self.answer(id, settled, &[])?;
                Ok(Turn::Done)
            },
            | Plan::Leaf(settled) => {
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

    /// Start a decomposition's children and wait on all of them.
    ///
    /// # Specification
    /// - requires: `subgoals` are the decomposition's premises in subgoal
    ///   order.
    /// - ensures: an empty decomposition answers convertible at once; otherwise
    ///   one child per subgoal, started fresh or re-shared by
    ///   [`Scheduler::start_fresh`] — a value pair as it stands, an opened pair
    ///   at this depth — and the goal waits on all of them, one premise per
    ///   position even where two positions name one process.
    /// - provides: every rule with premises compared child by child.
    /// - fails: as [`Scheduler::start_fresh`] and [`Scheduler::depend`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::start_fresh`] and [`Scheduler::depend`].
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
            self.answer(id, Settled::Convertible, &[])?;
            return Ok(Turn::Done);
        }
        let mut children = Vec::with_capacity(subgoals.len());
        for subgoal in subgoals {
            let sides = match subgoal {
                | Subgoal::Values(left, right) => {
                    SupportSides::Heads(Glued::Value(left), Glued::Value(right))
                },
                | Subgoal::Opened(left, right) => SupportSides::Opened(left, right),
            };
            let child = self.start_fresh(sides, goal.depth)?;
            self.depend(id, child)?;
            children.push(child);
        }
        goal.next = Next::Combine(Combine::All {
            pair,
            children,
            collapse,
        });
        Ok(Turn::Wait)
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
                | DomainValue::Unit { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Pair { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Lift { .. } => return Err(ConversionFault::MachineInvariant),
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
    fn eta(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Result<(), ConversionFault>
    {
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
        goal.depth = deeper(goal.depth)?;
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
                let spines = spine_subgoals(self.domain, left, right)?;
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
    ///   agreed and one declined. Each takes the first decline's reason in
    ///   child order. Otherwise the goal waits. The children an answer rests on
    ///   are recorded as its derivation's continuation, and the others lose
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
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::vec::Vec;

    use gandr_core_term::Computation;
    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Transparency;
    use gandr_core_term::Value;
    use gandr_core_term::ValueId;
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
    fn core_children(
        core: &CoreArena,
        node: CoreTerm,
    ) -> Vec<CoreTerm>
    {
        match node {
            | CoreTerm::Value(id) => match *core.value(id).expect("a reached value resolves") {
                | Value::Variable { .. } | Value::Constant(_) | Value::Unit | Value::Literal(_) => {
                    Vec::new()
                },
                | Value::Pair(first, second) => {
                    Vec::from([CoreTerm::Value(first), CoreTerm::Value(second)])
                },
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
    /// - ensures: a representative per reached node, equal to it as a tree,
    ///   with two nodes of equal tree sharing one.
    /// - provides: the hash-consing the lifter shares repeated subterms by.
    /// - panics: when a reached node does not resolve.
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
                                    | Value::Pair(first, second) => {
                                        Value::Pair(value(first), value(second))
                                    },
                                    | Value::Injection(side, body) => {
                                        Value::Injection(side, value(body))
                                    },
                                    | Value::Thunk(body) => Value::Thunk(computation(body)),
                                    | Value::Lift { target, body } => Value::Lift {
                                        target,
                                        body: value(body),
                                    },
                                    | leaf @ (Value::Variable { .. }
                                    | Value::Constant(_)
                                    | Value::Unit
                                    | Value::Literal(_)) => leaf,
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
    /// - requires: `root` resolves in `core`.
    /// - ensures: an overlay that validates from the returned root and erases
    ///   to a term equal to `root` as a tree; a node reached once is grafted
    ///   where it stands.
    /// - provides: the spinal side of every certification test.
    /// - panics: when a mint is refused, which no fixture provokes.
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
    ///   `depth`.
    /// - ensures: the grafted node; `taken` counts each share's occurrences
    ///   minted so far, left to right, which is preorder.
    /// - provides: the one minting walk [`lifted`] runs per leg and for the
    ///   body.
    /// - panics: when a mint is refused, which no fixture provokes.
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

    /// The kernel's copy of a world's terms, each core node translated once.
    #[derive(Default)]
    struct Kernel
    {
        /// The kernel's terms.
        arena: TermArena,
        /// The kernel node of every core value translated.
        values: BTreeMap<ValueId, gandr_kernel_term::ValueId>,
        /// The kernel node of every core computation translated.
        computations: BTreeMap<ComputationId, gandr_kernel_term::ComputationId>,
    }

    /// A core node awaiting translation.
    #[derive(Clone, Copy, Debug)]
    enum Node
    {
        /// A value.
        Value(ValueId),
        /// A computation.
        Computation(ComputationId),
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
        /// - requires: every node beneath `root` resolves, and every variable
        ///   is intuitionistic.
        /// - ensures: `root` and every node beneath it have a kernel copy of
        ///   the same shape, constants at the same positions.
        /// - provides: the one translation the replay tests share.
        /// - panics: on a dangling node or a linear variable, which no fixture
        ///   builds.
        ///
        /// # Termination
        /// - reason: the `while let Some(&node) = stack.last()` loop over an
        ///   explicit stack, not recursion.
        /// - measure: the reachable nodes without a copy, then the stack's
        ///   length: a node is pushed only while it has no copy, beneath a
        ///   parent minted after it, and popped once it has one.
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
        /// trivial.
        fn translated(
            &self,
            node: Node,
        ) -> Translated
        {
            let made = match node {
                | Node::Value(value) => self.values.contains_key(&value),
                | Node::Computation(computation) => self.computations.contains_key(&computation),
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
        /// trivial.
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
                    match core.value(value).expect("a fixture value resolves") {
                        | &Value::Pair(first, second) => {
                            Vec::from([Node::Value(first), Node::Value(second)])
                        },
                        | &(Value::Injection(_, body) | Value::Lift { body, .. }) => {
                            Vec::from([Node::Value(body)])
                        },
                        | &Value::Thunk(body) => Vec::from([Node::Computation(body)]),
                        | &(Value::Variable { .. }
                        | Value::Constant(_)
                        | Value::Unit
                        | Value::Literal(_)) => Vec::new(),
                    }
                },
                | Node::Computation(computation) => {
                    match core
                        .computation(computation)
                        .expect("a fixture computation resolves")
                    {
                        | &Computation::Lambda(body) => Vec::from([Node::Computation(body)]),
                        | &Computation::Application(head, argument) => {
                            Vec::from([Node::Computation(head), Node::Value(argument)])
                        },
                        | &(Computation::Return(value) | Computation::Force(value)) => {
                            Vec::from([Node::Value(value)])
                        },
                        | &Computation::Bind(bound, body) => {
                            Vec::from([Node::Computation(bound), Node::Computation(body)])
                        },
                        | &Computation::Case {
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
            }
        }

        /// Mint the kernel copy of `node`, whose children have theirs.
        ///
        /// # Specification
        /// trivial.
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
                    let copy = match core.value(id).expect("a fixture value resolves") {
                        | &Value::Variable {
                            zone: Zone::Intuitionistic,
                            index,
                        } => self.arena.value_variable(index),
                        | &Value::Variable {
                            zone: Zone::Linear, ..
                        } => {
                            panic!("the kernel's terms have no linear zone")
                        },
                        | &Value::Constant(constant) => self.arena.value_constant(constant),
                        | &Value::Unit => self.arena.value_unit(),
                        | &Value::Literal(ref literal) => self.arena.value_literal(literal.clone()),
                        | &Value::Pair(first, second) => {
                            let (first, second) = (value(self, first), value(self, second));
                            self.arena.value_pair(first, second)
                        },
                        | &Value::Injection(side, body) => {
                            let body = value(self, body);
                            self.arena.value_injection(side, body)
                        },
                        | &Value::Thunk(body) => {
                            let body = computation(self, body);
                            self.arena.value_thunk(body)
                        },
                        | &Value::Lift { ref target, body } => {
                            let body = value(self, body);
                            self.arena.value_lift(target.clone(), body)
                        },
                    };
                    self.values.insert(id, copy);
                },
                | Node::Computation(id) => {
                    let copy = match *core
                        .computation(id)
                        .expect("a fixture computation resolves")
                    {
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
            }
        }
    }

    /// The decision the kernel reads for the machine's `decision`: a constant
    /// keeps its position, and every other node is opaque to the replay.
    ///
    /// # Specification
    /// trivial.
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
        }
    }

    /// The certified kernel verdict a machine verdict corresponds to.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    fn a_forced_unfolding_meets_a_former()
    {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let reference = core.value_constant(Name::Zero.constant());
        let unit = core.value_unit();
        let paired = core.value_pair(unit, unit);
        let world = World::new(core, &[(Name::Zero, body)]);
        let unfolded = [
            ConversionDecision::Unfold {
                constant: named(Name::Zero),
            },
            ConversionDecision::ReduceLeft {
                redex: named(Name::Zero),
            },
        ];

        let (verdict, decisions) = world.traced(Sides::Values(reference, unit));
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert_eq!(
            Vec::from(unfolded),
            decisions,
            "a defined head against a former has one rule: unfold it"
        );

        let (verdict, decisions) = world.traced(Sides::Values(reference, paired));
        assert_eq!(
            MachineVerdict::NotConvertible,
            verdict,
            "and the unfolding is forced, so the refutation after it is authoritative"
        );
        assert!(
            matches!(decisions.as_slice(), &[
                ConversionDecision::Unfold { constant },
                ConversionDecision::ReduceLeft { redex },
                ConversionDecision::ComparedShared { .. },
            ] if constant == named(Name::Zero) && redex == named(Name::Zero)),
            "and the unit and the pair it meets are refuted by their guards: {decisions:?}"
        );
    }

    #[test]
    fn two_defined_heads_meet_by_unfolding()
    {
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_unit();
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let world = World::new(core, &[(Name::Zero, first), (Name::One, second)]);

        let (verdict, decisions) = world.traced(Sides::Values(zero, one));
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert_eq!(
            Vec::from([
                ConversionDecision::Postpone {
                    constant: named(Name::One),
                },
                ConversionDecision::Unfold {
                    constant: named(Name::Zero),
                },
                ConversionDecision::ReduceLeft {
                    redex: named(Name::Zero),
                },
                ConversionDecision::Unfold {
                    constant: named(Name::One),
                },
                ConversionDecision::ReduceRight {
                    redex: named(Name::One),
                },
            ]),
            decisions,
            "the branch freezing the left constant refutes, which is not authoritative, \
             so the answer is the left unfolding's"
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
    fn the_const_shortcut_wins_without_unfolding()
    {
        let mut core = CoreArena::new();
        let function = identity(&mut core);
        let argument = core.value_unit();
        let head = core.value_constant(Name::Zero.constant());
        let defined = core.value_constant(Name::One.constant());
        let unit = core.value_unit();
        let left = call(&mut core, head, &[defined]);
        let right = call(&mut core, head, &[unit]);
        let world = World::new(core, &[(Name::Zero, function), (Name::One, argument)]);

        let (verdict, decisions) = world.traced(Sides::Computations(left, right));
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert_eq!(
            Vec::from([
                ConversionDecision::ConstShortcut {
                    constant: named(Name::Zero),
                },
                ConversionDecision::Unfold {
                    constant: named(Name::One),
                },
                ConversionDecision::ReduceLeft {
                    redex: named(Name::One),
                },
            ]),
            decisions,
            "one head over arguments that agree after unfolding them: the head itself \
             never unfolds in the winning derivation"
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
    fn thunks_meet_by_forcing()
    {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let reference = core.value_constant(Name::Zero.constant());
        let unit = core.value_unit();
        let returned = core.computation_return(reference);
        let left = core.value_thunk(returned);
        let returned = core.computation_return(unit);
        let right = core.value_thunk(returned);
        let world = World::new(core, &[(Name::Zero, body)]);

        let (verdict, decisions) = world.traced(Sides::Values(left, right));
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert!(
            matches!(decisions.as_slice(), [
                ConversionDecision::Force { thunk: TraceNode::Value(_) },
                ConversionDecision::Force { thunk: TraceNode::Value(_) },
                ConversionDecision::Unfold { constant },
                ConversionDecision::ReduceLeft { redex },
            ] if *constant == named(Name::Zero) && *redex == named(Name::Zero)),
            "both thunks are entered, then the returned values compared: {decisions:?}"
        );
    }

    #[test]
    fn identity_closes_a_goal_on_shared_nodes()
    {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let reference = core.value_constant(Name::Zero.constant());
        let unit = core.value_unit();
        let shared = core.value_unit();
        let left = core.value_pair(reference, shared);
        let right = core.value_pair(unit, shared);
        let world = World::new(core, &[(Name::Zero, body)]);

        let (verdict, decisions) = world.traced(Sides::Values(left, right));
        assert_eq!(MachineVerdict::Convertible, verdict);
        assert!(
            matches!(decisions.as_slice(), [
                ConversionDecision::Unfold { .. },
                ConversionDecision::ReduceLeft { .. },
                ConversionDecision::ComparedShared {
                    left: TraceNode::Value(_),
                    right: TraceNode::Value(_),
                },
            ]),
            "the second components are one source term, so identity closes their goal \
             with no rule: {decisions:?}"
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
            assert!(
                log.decisions().next().is_some(),
                "every answer rests on at least one decision: {sides:?}"
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
    /// trivial.
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
        let mut sharing = 0_usize;
        for (sides, expected) in cases {
            let (report, decisions) = world.spinal(MachineSettings::default(), sides);
            assert_eq!(expected, report.verdict(), "{sides:?}");
            assert_eq!(
                certified(report.verdict()),
                world.replayed(sides, report.verdict(), &decisions),
                "{sides:?}: {decisions:?}"
            );
            if world
                .shares(sides)
                .iter()
                .any(|&count| u64::from(count) > 0)
            {
                sharing = sharing.saturating_add(1);
            }
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
            if world
                .shares(sides)
                .iter()
                .any(|&count| u64::from(count) > 0)
            {
                sharing = sharing.saturating_add(1);
            }
        }
        assert!(
            sharing > 0,
            "some fixture reaches a node twice, so the spinal runs evaluate a shared leg"
        );
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
        let Some(last) = decisions.last_mut()
        else {
            panic!("two defined heads unfold before they meet");
        };
        assert_eq!(
            ConversionDecision::ReduceRight {
                redex: named(Name::One)
            },
            *last
        );
        *last = ConversionDecision::ReduceLeft {
            redex: named(Name::One),
        };
        assert_eq!(
            KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(4_usize),
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
}
