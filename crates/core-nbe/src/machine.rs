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

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::mem;

use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionHeight;
use gandr_core_term::Zone;
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
    /// own chain: the same definition over the same spine.
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
}

/// Decide whether the two sides of `problem` are convertible.
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
///   with [`DeclineReason::Cycle`]; a run past its budget declines with
///   [`DeclineReason::Budget`]. A recording `sink` receives the winning
///   derivation in preorder, and nothing for a decline; the null sink receives
///   nothing, and the report counts zero derivations kept.
/// - provides: step 4 of the conversion pipeline: the search the first three
///   steps defer to.
/// - fails: [`ConversionFault::Polarity`] for a value against a computation
///   anywhere in the search, [`ConversionFault::Evaluation`] when an evaluation
///   a goal demanded is refused, [`ConversionFault::Domain`] and
///   [`ConversionFault::LiteralPayload`] for nodes that do not resolve, and
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
///   machine's rule arms and its two declines; each rule arm is separated by a
///   conversion answered through it, both verdicts and both declines are
///   exercised, and recording is pinned against the null sink verdict for
///   verdict.
/// - witness: `machine::tests::the_search_free_steps_answer_before_any_process`
/// - witness: `machine::tests::a_forced_unfolding_meets_a_former`
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
/// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
/// - witness: `machine::tests::recording_does_not_move_the_verdict`
/// - witness: `machine::tests::the_sink_off_run_keeps_no_derivation`
#[inline]
pub fn decide<S>(
    core: &CoreArena,
    domain: &mut DomainArena,
    definitions: Definitions<'_>,
    settings: MachineSettings,
    problem: Problem,
    sink: &mut S,
) -> Result<MachineReport, ConversionFault>
where
    S: TraceSink<TraceNode>,
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
        });
    }
    let mut scheduler = Scheduler::new(core, domain, definitions, settings, S::ACTIVITY);
    let root = scheduler.start_goal(Goal {
        left: Slot::Ready(problem.left),
        right: Slot::Ready(problem.right),
        depth: problem.depth,
        frozen: Frozen::default(),
        chain: Chain::default(),
        next: Next::Classify,
    })?;
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

/// The id of one process in a run's arena.
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

/// One run of the machine: `⟨P, W, Q⟩` and the channel tables.
struct Scheduler<'run>
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
    /// The rule instances and evaluation steps spent so far.
    spent: StepCount,
}

impl<'run> Scheduler<'run>
{
    /// An empty run.
    ///
    /// # Specification
    /// trivial.
    fn new(
        core: &'run CoreArena,
        domain: &'run mut DomainArena,
        definitions: Definitions<'run>,
        settings: MachineSettings,
        activity: SinkActivity,
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
    ///   dependency and no waiter, and the derivation store one more slot when
    ///   recording.
    /// - provides: the one place a process id is minted.
    /// - fails: [`ConversionFault::MachineInvariant`] when the derivation store
    ///   and the arena disagree.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the store and the arena
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
        Ok(id)
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

    /// Run until the root answers or the budget is spent.
    ///
    /// # Specification
    /// - requires: `root` is a pending goal no process waits on.
    /// - ensures: the root's answer, reached by turns taken round-robin over
    ///   the run queue, each process passed over until its credit reaches its
    ///   share; [`DeclineReason::Budget`] once the steps charged pass the
    ///   settings' budget with the root unanswered.
    /// - provides: the machine's one loop, and the backstop every comparison
    ///   the cycle key does not catch reaches.
    /// - fails: every fault a turn raises, and
    ///   [`ConversionFault::MachineInvariant`] when the queue empties with the
    ///   root unanswered.
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
        Err(ConversionFault::MachineInvariant)
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
                self.finish(id, Outcome::Settled(settled))?;
                Ok(Turn::Done)
            },
            | Plan::Leaf(settled) => {
                self.finish(id, Outcome::Settled(settled))?;
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
    ///   one fresh goal per subgoal — no frozen constant and an empty chain, a
    ///   value pair as it stands, an opened pair one binder deeper on two
    ///   opening channels at this depth — and the goal waits on all of them.
    /// - provides: every rule with premises compared child by child.
    /// - fails: [`ConversionFault::MachineInvariant`] at the binder-level
    ///   ceiling, and every fault a channel raises.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::MachineInvariant`] — the binder levels ran out.
    /// - [`ConversionFault`] — as a channel raises.
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
            self.finish(id, Outcome::Settled(Settled::Convertible))?;
            return Ok(Turn::Done);
        }
        let mut children = Vec::with_capacity(subgoals.len());
        for subgoal in subgoals {
            let child = match subgoal {
                | Subgoal::Values(left, right) => self.start_goal(Goal {
                    left: Slot::Ready(Glued::Value(left)),
                    right: Slot::Ready(Glued::Value(right)),
                    depth: goal.depth,
                    frozen: Frozen::default(),
                    chain: Chain::default(),
                    next: Next::Classify,
                })?,
                | Subgoal::Opened(left, right) => {
                    let left = self.open_channel(left, goal.depth)?;
                    let right = self.open_channel(right, goal.depth)?;
                    let deeper = deeper(goal.depth)?;
                    self.start_goal(Goal {
                        left: Slot::Waiting(left),
                        right: Slot::Waiting(right),
                        depth: deeper,
                        frozen: Frozen::default(),
                        chain: Chain::default(),
                        next: Next::Classify,
                    })?
                },
            };
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
    ///   reduction, the side waits on the neutral's unfolding, and the answer
    ///   is [`Advance::Unfolding`].
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
                        self.finish(id, Outcome::Settled(Settled::NotConvertible))?;
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
    ///   this goal's need.
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
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            self.finish(id, Outcome::Settled(Settled::NotConvertible))?;
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
                match collapse {
                    | Collapse::Allowed => self.derivations.agree_on(id, pair, children)?,
                    | Collapse::Never => self.derivations.rest_on(id, children)?,
                }
                self.finish(id, Outcome::Settled(Settled::Convertible))?;
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
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            self.finish(id, answered)?;
                            return Ok(Turn::Done);
                        },
                        | Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        | Outcome::Settled(Settled::NotConvertible) | Outcome::Declined(_) => {},
                        | Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                    }
                }
                let authoritative = self.outcome(last)?;
                match authoritative {
                    | Outcome::Settled(_) => {
                        self.derivations.rest_on(id, Vec::from([last]))?;
                        self.finish(id, authoritative)?;
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
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            self.finish(id, answered)?;
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
                    self.derivations.rest_on(id, children)?;
                    self.finish(id, Outcome::Settled(Settled::NotConvertible))?;
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
    use alloc::vec::Vec;

    use gandr_core_term::ComputationId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::DefinitionChain;
    use gandr_core_term::DefinitionalEnvironment;
    use gandr_core_term::Transparency;
    use gandr_core_term::ValueId;
    use gandr_core_term::Zone;
    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    use gandr_kernel_conversion_trace::NullSink;
    use gandr_kernel_conversion_trace::SubgoalPosition;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_conversion_trace::TraceSink;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GlobalIndex;

    use super::DeclineReason;
    use super::MachineReport;
    use super::MachineSettings;
    use super::MachineVerdict;
    use super::Problem;
    use super::StepBudget;
    use super::TraceNode;
    use super::decide;
    use crate::arena::DomainArena;
    use crate::eval::Definitions;
    use crate::eval::Fuel;
    use crate::eval::LoweredChain;
    use crate::eval::eval_computation;
    use crate::eval::eval_value;
    use crate::policy::GranularityPolicy;
    use crate::policy::SchedulingPolicy;

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
    }

    impl World
    {
        /// Admit one manifest definition per `(entry, body)`, in order: the
        /// `n`th is the constant [`Name`] `n` names, its body stored under the
        /// table entry `entry` names.
        ///
        /// # Specification
        /// - requires: two definitions naming one entry name one body.
        /// - ensures: every constant admitted unfolds to its body; every other
        ///   constant is rigid.
        /// - provides: the fixture every machine test runs in.
        /// - panics: when the chain refuses a definition, which no fixture
        ///   provokes.
        fn new(
            core: CoreArena,
            bodies: &[(Name, ValueId)],
        ) -> Self
        {
            let mut chain = DefinitionChain::new();
            for (position, &(entry, _)) in bodies.iter().enumerate() {
                let defined = chain.define(
                    ConstantIndex::from(position),
                    entry.entry(),
                    Transparency::Manifest,
                    &[],
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
        /// `settings`.
        ///
        /// # Specification
        /// - requires: both sides are closed.
        /// - ensures: the machine's report.
        /// - provides: the one entry every machine test goes through.
        /// - panics: when evaluation or the machine refuses, which no fixture
        ///   provokes.
        fn run_under<S>(
            &self,
            settings: MachineSettings,
            sides: Sides,
            sink: &mut S,
        ) -> MachineReport
        where
            S: TraceSink<TraceNode>,
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
            decide(
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
}
