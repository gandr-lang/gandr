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
//!
//! # Conversion machine
//!
//! `decide` is step 4: the lazy concurrent search of Courant and Leroy, as a
//! flat arena of processes, a wait map and a duplicate-free run queue. A
//! **goal** compares two weak heads and applies one rule per turn; a
//! **channel** evaluates one weak head, one slice of a resumable evaluation per
//! turn, so a diverging evaluation yields to the comparisons beside it. A goal
//! names the channels and children it waits on by id, and each process lists
//! its waiters; nothing recurses and nothing holds a reference to another
//! process. A process runs only while something needs it: when a combinator
//! answers early, the processes it no longer waits on lose that need,
//! transitively, and stop being scheduled.
//!
//! The root first runs steps 1 to 3. An identical or structurally equal pair is
//! convertible and a guard-separated pair is not, each emitted as one
//! `ComparedShared` with no process started. A structural separation and a
//! deferral start the machine, because a separation found deep in the
//! structural walk is one the replay would have to find again, while the
//! machine's derivation names the premise it rests on.
//!
//! The rule table reads the two heads. A defined head the goal has not frozen
//! against a former unfolds: `Unfold` and the side's `ReduceLeft` or
//! `ReduceRight`, then the unfolding channel's answer stands where the head
//! stood. Two defined heads are a choice point, run as concurrent goals and
//! combined as §6.1 says. The same constant over spines of one length runs the
//! shortcut — `ConstShortcut`, then the arguments compared pairwise — beside
//! the unfolding of the right with the left constant frozen and the unfolding
//! of the left, biased: a convertible answer from any alternative wins, and
//! otherwise the last, authoritative alternative decides. Two different
//! constants drop the shortcut. A constant frozen on one side against itself
//! unfrozen runs the shortcut or the unfolding of the unfrozen side, either
//! answering. A frozen constant may no longer unfold in that branch, so each
//! later unfolding of it happens in one branch only; a frozen branch can refute
//! two convertible terms, which is why its refutation is never authoritative.
//! Rigid heads decompose: one head over spines of one shape compares the
//! arguments, and anything else refutes. Before they do, two computations over
//! one head are brought to one bind normal form by the commuting conversions
//! of `F`: the first two binds in a row on a side become one (`Reassociate`,
//! the left side first), then a side one bind short of the other is bound into
//! `return` (`ReturnEta`). Each rewrite is forced by the spines and recorded
//! where the kernel's replay meets it, so a positional refutation is never
//! read off a pair the laws still relate.
//!
//! η applies only in the two cases §6.2 shows safe and profitable. A lambda
//! against a rigid or frozen neutral expands the neutral: `EtaExpand` names the
//! fresh variable at the goal's depth, the neutral is applied to it and the
//! lambda's body opened under it. A lambda against a defined neutral is a
//! choice: freeze the constant and expand, beside the authoritative unfolding.
//! A thunk against a thunk or a stuck value forces both sides. Alternatives: η
//! at every lambda against any neutral, which expands before an unfolding that
//! would have answered and duplicates work the choice shares; and no η, which
//! refutes two η-convertible functions. Reversal: a measured family where the
//! frozen expansion consistently loses to the unfolding beside it, which would
//! drop the second case.
//!
//! A refuted decomposition records `NegativeSubgoal` with the position of the
//! first premise in subgoal order that refuted, and its derivation is that
//! premise’s alone. An agreeing decomposition records `Decompose` followed by
//! its premises in order, unless the search-free structural comparison can
//! close the entire parent with one `ComparedShared`. The explicit delimiter
//! prevents a child’s shared comparison from being consumed as the parent’s
//! answer. A `ConstShortcut` already names its decomposition. The winning
//! derivation is emitted in preorder, once under each occurrence of a shared
//! derivation. `machine::tests::native_records_cases_and_traces_agree`
//! exercises multi-field positive and negative dialogues through independent
//! kernel replay.
//!
//! # Native universe paths
//!
//! Closed reflexivity and equivalence certificates retain their raw source
//! syntax. Product paths evaluate their children and keep a source face only
//! when both children still denote the original children. Certificate
//! conversion erases evidence but does not normalize maps. Transport applies
//! the forward map, returns its input for reflexivity, or sequences component
//! transports for a pair. Neutral paths and neutral product inputs remain
//! eliminations on a spine.
//!
//! Readback reconstructs suspended product sequencing with the correct binder
//! depth in both modes. `native_transport_sequences_product_components`
//! distinguishes all four canonical/neutral component combinations;
//! `native_certificate_conversion_retains_map_syntax` distinguishes
//! computational map equality from certificate identity. The engine supplies
//! CBPV dialogues to the kernel’s identity-by-code, higher-field, funext and
//! `Flow_U` consumers; it grants none of those rule languages an admission
//! receipt. Evaluation and readback exhaust `Fuel`; conversion exhausts
//! `StepBudget`. Exhaustion declines rather than proving either equality or
//! inequality.
//!
//! **Choice.** Ordinary CBPV evaluation and explicit continuations, not Rust
//! translator closures or a second evaluator. Certificate evidence is excluded
//! from conversion, while raw classifier and translator syntax remains
//! observable. **Reversal.** A larger code or elimination fragment must first
//! define the kernel rules that replay these computations.
//!
//! # Termination
//!
//! No termination result covers the machine: a definition may unfold to itself,
//! and an evaluation may run Ω. The unbounded loop is the run queue's driver,
//! not any one evaluation — each slice of an evaluation is bounded by its fuel,
//! while the driver issues unfoldings, slices and alternatives without end — so
//! the driver is what the two mechanisms bound, and each `# Termination` block
//! in the machine names the loop it audits.
//!
//! **Cycle detection** comes first. Every goal carries, per side, the chain of
//! unfoldings that side has made since the goal's last decomposition: a
//! choice's alternatives inherit it, and a decomposition's premises start
//! empty. An unfolding records its definition and the spine it unfolds under,
//! compared by the ids the spine's eliminations name; a goal about to make an
//! unfolding its side's chain already holds declines with
//! `DeclineReason::Cycle`, because unfolding again can only return to where it
//! stands. The channel tables make the key meaningful: one body is evaluated
//! once per run, so a definition that unfolds back to itself meets the very
//! neutral it started from rather than a freshly minted copy. Alternatives: the
//! definition's name alone, which declines a terminating comparison that
//! unfolds one function twice at different arguments, such as `id (id x)`
//! against `x`; and the neutral's node id, which is fresh whenever a side is
//! re-evaluated. Reversal: a cycle that reaches the budget in practice because
//! its spine is re-minted every round would add a structural spine key; a
//! terminating comparison the key declines would narrow it.
//!
//! **The step budget** is the backstop. A run charges one step per table read
//! and per move, one per alternative a choice starts, and every evaluation step
//! a channel runs: the reductions, forced steps and branchings of Courant and
//! Leroy's `r + f + b` proof-size decomposition, over which their bound on the
//! machine's running time is stated. A still-pending root declines with
//! `DeclineReason::Budget` when charged steps exceed `StepBudget` or the
//! representable counter ceiling. A root answer obtained on that turn takes
//! precedence; the reported `StepCount` saturates without disabling the
//! backstop. Witness:
//! `machine::tests::step_counter_overflow_cannot_disable_the_budget_backstop`.
//! Alternatives: a budget alone, which turns every terminating comparison
//! longer than the budget into a refusal and catches a one-step cycle only
//! after spending all of it; and a budget over evaluation fuel only, which
//! never stops a run whose goals branch without evaluating. Reversal: a
//! measured family whose cost is dominated by something these steps do not
//! count.
//!
//! A decline is the third value of Kleene's logic in every combinator: a
//! refutation outranks it in a decomposition, an agreement outranks it in a
//! choice, and a choice whose authoritative alternative declined still waits
//! for the others before declining. A decline is never a verdict on the terms:
//! the caller may retry with a larger budget or a different schedule, and the
//! kernel never certifies one. A decomposition with no premises agrees; an
//! empty choice is instead `ConversionFault::MachineInvariant`, never a vacuous
//! refutation. Witness:
//! `machine::tests::empty_choices_refuse_instead_of_producing_a_refutation`.

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
use gandr_kernel_term::RewriteFuel;

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
use crate::presented::NormalForm;
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
            Glued::Value(value) => Self::Value(value),
            Glued::Computation(comp) => Self::Computation(comp),
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
    /// A side stands on a typed hole or a mark: a fill may still make the two
    /// agree or differ, so no verdict is the machine's to give.
    Indeterminate,
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
        Settlement::Identical | Settlement::StructurallyEqual => {
            RootFastPath::Answered(MachineVerdict::Convertible)
        },
        Settlement::GuardedApart => RootFastPath::Answered(MachineVerdict::NotConvertible),
        Settlement::StructurallyApart | Settlement::Deferred(_) => RootFastPath::Search,
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
        (Glued::Value(left), Glued::Value(right)) => convert_values(core, domain, left, right),
        (Glued::Computation(left), Glued::Computation(right)) => {
            convert_computations(core, domain, left, right)
        },
        (Glued::Value(_), Glued::Computation(_)) | (Glued::Computation(_), Glued::Value(_)) => {
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
            ConversionSide::Left => &mut self.left,
            ConversionSide::Right => &mut self.right,
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

/// What a forced reading of a pair's sides did: a value pair's presented
/// sides read by their normal forms, or a computation pair's cong chains
/// fused to their paths.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Presenting
{
    /// Each side is its own reading.
    Normal,
    /// A side was replaced by its reading.
    Rewritten,
    /// The run's budget ran out first.
    Exhausted,
}

/// Number of fresh variables a computation closure binds.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Opening
{
    /// A lambda or ordinary elimination branch.
    One,
    /// A List fold cell branch or a split body, under this many variables.
    Many(gandr_core_term::ComponentCount),
}

/// A channel: one evaluation goals demand.
#[expect(
    clippy::large_enum_variant,
    reason = "one per demanded evaluation, which runs in place; boxing the running evaluation \
              would allocate once per channel to shrink the brief wait for a body"
)]
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
    /// One opening channel per closure, binder level and arity.
    openings: BTreeMap<(CompClosureId, BinderLevel, Opening), ProcessId>,
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
            && (!matches!(sides, SupportSides::Opened(_, _) | SupportSides::OpenedUnder(..))
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
            SupportSides::Closed(left, right) => Goal {
                left: Slot::Waiting(self.enter_channel(left)?),
                right: Slot::Waiting(self.enter_channel(right)?),
                depth: level,
                frozen: Frozen::default(),
                chain: Chain::default(),
                next: Next::Classify,
            },
            SupportSides::Heads(left, right) => Goal {
                left: Slot::Ready(left),
                right: Slot::Ready(right),
                depth: level,
                frozen: Frozen::default(),
                chain: Chain::default(),
                next: Next::Classify,
            },
            SupportSides::OpenedUnder(left, right, count) => Goal {
                left: Slot::Waiting(self.open_channel(left, level, Opening::Many(count))?),
                right: Slot::Waiting(self.open_channel(right, level, Opening::Many(count))?),
                depth: (0_usize .. usize::from(count)).try_fold(level, |at, _| deeper(at))?,
                frozen: Frozen::default(),
                chain: Chain::default(),
                next: Next::Classify,
            },
            SupportSides::Opened(left, right) => {
                let deeper = deeper(level)?;
                let left = self.open_channel(left, level, Opening::One)?;
                let right = self.open_channel(right, level, Opening::One)?;
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
    ///   membership, duplicate scheduling and a lost wakeup. The predicate
    ///   observes membership, the queue's length and its new tail; that the
    ///   queue holds `id` once follows from the membership flag guarding the
    ///   push, so it reads no other queue entry.
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
            && (ret.is_err() || self.queued.get(id.0) == Some(&Queued::Present))
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
                        DeclineReason::UndecidedCodes | DeclineReason::Indeterminate => false,
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
                Outcome::Settled(Settled::Convertible) => {
                    return Ok(MachineVerdict::Convertible);
                },
                Outcome::Settled(Settled::NotConvertible) => {
                    return Ok(MachineVerdict::NotConvertible);
                },
                Outcome::Declined(reason) => return Ok(MachineVerdict::Declined(reason)),
                Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                Outcome::Pending => {},
            }
            if self.spent_overflowed || self.spent.0 > budget {
                return Ok(MachineVerdict::Declined(DeclineReason::Budget));
            }
        }
        match M::ACTIVITY {
            MemoActivity::Active => Ok(MachineVerdict::Declined(DeclineReason::Cycle)),
            MemoActivity::Inactive => Err(ConversionFault::MachineInvariant),
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
            Work::Goal(mut goal) => {
                let turn = self.goal_turn(id, &mut goal)?;
                if turn != Turn::Done {
                    let process = self.process_mut(id)?;
                    process.work = Work::Goal(goal);
                }
                Ok(turn)
            },
            Work::Channel(mut channel) => {
                let turn = self.channel_turn(id, &mut channel)?;
                if turn != Turn::Done {
                    let process = self.process_mut(id)?;
                    process.work = Work::Channel(channel);
                }
                Ok(turn)
            },
            Work::Spent => Err(ConversionFault::MachineInvariant),
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
            Channel::Reapply { body, neutral } => {
                let answered = self.outcome(body)?;
                match answered {
                    Outcome::Pending => Ok(Turn::Wait),
                    Outcome::Evaluated(Glued::Value(head)) => {
                        let evaluation = self.reapplication(neutral, head)?;
                        *channel = Channel::Running(evaluation);
                        Ok(Turn::Again)
                    },
                    Outcome::Evaluated(Glued::Computation(_))
                    | Outcome::Settled(_)
                    | Outcome::Declined(_) => Err(ConversionFault::MachineInvariant),
                }
            },
            Channel::Running(ref mut evaluation) => {
                let sliced = evaluation.resume(self.core, self.domain, Fuel::from(SLICE));
                let (progress, spent) = sliced.map_err(ConversionFault::Evaluation)?;
                self.charge(StepCount(u64::from(u32::from(spent))));
                match progress {
                    Progress::Paused => Ok(Turn::Again),
                    Progress::Finished(glued) => {
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
            Next::Classify => self.classify(id, goal, (left, right)),
            Next::Move(chosen) => self.take(id, goal, (left, right), chosen),
            Next::Combine(combine) => self.combine(id, goal, combine),
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
            Outcome::Pending => Ok(slot),
            Outcome::Evaluated(glued) => Ok(Slot::Ready(glued)),
            Outcome::Settled(_) | Outcome::Declined(_) => Err(ConversionFault::MachineInvariant),
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
        // A presented type's terms compare by their normal forms, taken here
        // as the kernel's replay takes them after weak head reduction: a
        // forced step, recording nothing.
        if let (Glued::Value(left), Glued::Value(right)) = pair
            && left != right
        {
            match self.present(goal, (left, right))? {
                Presenting::Normal => {},
                Presenting::Rewritten => return Ok(Turn::Again),
                Presenting::Exhausted => {
                    self.finish(id, Outcome::Declined(DeclineReason::Budget))?;
                    return Ok(Turn::Done);
                },
            }
        }
        // A cong chain whose functions compose to the identity is its path,
        // read here as the kernel's replay reads it after weak head
        // reduction: a forced step, recording nothing.
        if pair.0 != pair.1 {
            match self.fuse(goal, pair)? {
                Presenting::Normal => {},
                Presenting::Rewritten => return Ok(Turn::Again),
                Presenting::Exhausted => {
                    self.finish(id, Outcome::Declined(DeclineReason::Budget))?;
                    return Ok(Turn::Done);
                },
            }
        }
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
            Plan::Shared(settled) | Plan::Leaf(settled) => {
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

            Plan::Decompose(subgoals) => {
                self.decompose(id, goal, pair, subgoals, Collapse::Allowed)
            },
            Plan::Step(Step::Unfold(side)) => {
                let advance = self.unfold(id, goal, pair, side)?;
                self.advanced(id, advance)
            },
            Plan::Step(Step::Force) => {
                self.force(id, goal, pair)?;
                Ok(Turn::Again)
            },
            Plan::Step(Step::Eta(side)) => {
                self.eta(id, goal, pair, side)?;
                Ok(Turn::Again)
            },
            Plan::Step(Step::ReturnEta(side)) => {
                self.return_eta(id, goal, pair, side)?;
                Ok(Turn::Again)
            },
            Plan::Step(Step::Reassociate(side)) => {
                self.reassociate(id, goal, pair, side)?;
                Ok(Turn::Again)
            },
            Plan::Step(Step::Returned) => {
                self.open_returned(goal, pair)?;
                Ok(Turn::Again)
            },
            Plan::Choose(choice) => self.choose(id, goal, choice),
            Plan::Decline(reason) => {
                self.finish(id, Outcome::Declined(reason))?;
                Ok(Turn::Done)
            },
        }
    }

    /// Read the presented sides of a value pair by their normal forms.
    ///
    /// # Specification
    /// - requires: `left` and `right` are the goal's ready sides.
    /// - ensures: [`Presenting::Normal`] with the goal unchanged when each side
    ///   is its own normal form; [`Presenting::Rewritten`] with each side that
    ///   is not replaced by its normal form, the depth unchanged;
    ///   [`Presenting::Exhausted`] when the run's budget ran out first. The
    ///   nodes the rewriting compared or copied are charged to the run.
    /// - provides: conversion modulo a presented type's rules.
    /// - fails: every fault [`crate::presented::normal_form`] raises.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a circle word converts with its reduced word, the
    ///   kernel replaying the derivation, and not without the circle's rules.
    /// - witness: `presented::tests::a_circle_word_reads_as_its_reduced_word`
    #[spec(
        captures: [spent = self.spent.0, depth = goal.depth],
        ensures: |ret| self.spent.0 >= spent && goal.depth == depth,
    )]
    fn present(
        &mut self,
        goal: &mut Goal,
        (left, right): (DomainValueId, DomainValueId),
    ) -> Result<Presenting, ConversionFault>
    {
        let budget = u64::from(self.settings.budget());
        let mut fuel = RewriteFuel::from(budget.saturating_sub(self.spent.0));
        let before = u64::from(fuel);
        let mut presenting = Presenting::Normal;
        for (side, value) in [(ConversionSide::Left, left), (ConversionSide::Right, right)] {
            match crate::presented::normal_form(
                self.core,
                self.domain,
                self.definitions,
                value,
                &mut fuel,
            )? {
                NormalForm::Kept => {},
                NormalForm::Rewritten(normal) => {
                    Self::set_side(goal, side, Slot::Ready(Glued::Value(normal)));
                    presenting = Presenting::Rewritten;
                },
                NormalForm::Exhausted => {
                    presenting = Presenting::Exhausted;
                    break;
                },
            }
        }
        self.charge(StepCount(before.saturating_sub(u64::from(fuel))));
        Ok(presenting)
    }

    /// Read the sides of a pair as cong chains, each one whose functions
    /// compose to the identity replaced by its path: a computation by the
    /// `return` of the path, a returned endpoint over one by the path itself.
    ///
    /// # Specification
    /// - requires: `pair` holds the goal's ready sides.
    /// - ensures: [`Presenting::Normal`] with the goal unchanged when neither
    ///   side fuses; [`Presenting::Rewritten`] with each side that fuses
    ///   replaced as above, the depth unchanged; [`Presenting::Exhausted`] when
    ///   the run's budget ran out first. Each step the reading took is charged
    ///   to the run.
    /// - provides: conversion modulo cong fusion to the identity, the reading
    ///   [`crate::fusion::fused`] decides at a variable past the goal's depth;
    ///   the kernel's replay reads a returned endpoint as its computation
    ///   before it fuses, so the two engines fuse one chain.
    /// - fails: every fault [`crate::fusion::fused`] raises;
    ///   [`ConversionFault::Domain`] for a side that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `run q <- cong(unlooped, p); cong(looped, q)`
    ///   converts with `return p` over the presented circle under a rigid run,
    ///   and a chain composing to `looped ∘ looped` does not.
    /// - witness: `fusion::tests::a_cong_chain_composing_to_the_identity_is_its_path`
    #[spec(
        captures: [spent = self.spent.0, depth = goal.depth],
        ensures: |ret| self.spent.0 >= spent && goal.depth == depth,
    )]
    fn fuse(
        &mut self,
        goal: &mut Goal,
        (left, right): (Glued, Glued),
    ) -> Result<Presenting, ConversionFault>
    {
        let budget = u64::from(self.settings.budget());
        let mut fuel = RewriteFuel::from(budget.saturating_sub(self.spent.0));
        let before = u64::from(fuel);
        let mut fusing = Presenting::Normal;
        for (side, glued) in [(ConversionSide::Left, left), (ConversionSide::Right, right)] {
            let computation = match glued {
                Glued::Computation(computation) => computation,
                Glued::Value(value) => {
                    let Some(&DomainValue::Neutral { neutral, .. }) = self.domain.value(value)
                    else {
                        continue;
                    };
                    let held = self
                        .domain
                        .neutral(neutral)
                        .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
                    match held.head() {
                        NeutralHead::Returned(computation) if held.spine().is_empty() => {
                            computation
                        },
                        NeutralHead::Variable { .. }
                        | NeutralHead::Constant(_)
                        | NeutralHead::Module(_)
                        | NeutralHead::Hole { .. }
                        | NeutralHead::Mark { .. }
                        | NeutralHead::Returned(_) => continue,
                    }
                },
            };
            match crate::fusion::fused(
                self.core,
                self.domain,
                self.definitions,
                (computation, goal.depth),
                &mut fuel,
            )? {
                crate::fusion::Fusion::Kept => {},
                crate::fusion::Fusion::Fused(path) => {
                    let fused = match glued {
                        Glued::Computation(_) => {
                            Glued::Computation(self.domain.comp_return(path, CompTermFace::Reduced))
                        },
                        Glued::Value(_) => Glued::Value(path),
                    };
                    Self::set_side(goal, side, Slot::Ready(fused));
                    fusing = Presenting::Rewritten;
                },
                crate::fusion::Fusion::Exhausted => {
                    fusing = Presenting::Exhausted;
                    break;
                },
            }
        }
        self.charge(StepCount(before.saturating_sub(u64::from(fuel))));
        Ok(fusing)
    }

    /// Read each side of a value pair that is a returned endpoint as the
    /// computation it holds, recording nothing.
    ///
    /// # Specification
    /// - requires: `pair` holds the goal's ready sides.
    /// - ensures: each value side that [`crate::rules::returned`] reads as a
    ///   computation is replaced by it; every other side, and the depth,
    ///   unchanged.
    /// - provides: [`Step::Returned`]: the kernel's replay reads a returned
    ///   endpoint as its computation before any rule, so the two engines
    ///   compare one pair and the trace needs no decision for the step.
    /// - fails: [`ConversionFault::Domain`] for a side that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two endpoints over transports whose motives close
    ///   over different environments convert once read as their computations,
    ///   and the kernel replays the trace.
    /// - witness: `machine::tests::two_held_transports_convert_by_their_computations`
    #[spec(
        captures: depth = goal.depth,
        ensures: |ret| goal.depth == depth,
    )]
    fn open_returned(
        &self,
        goal: &mut Goal,
        (left, right): (Glued, Glued),
    ) -> Result<(), ConversionFault>
    {
        for (side, glued) in [(ConversionSide::Left, left), (ConversionSide::Right, right)] {
            let Glued::Value(value) = glued
            else {
                continue;
            };
            if let Some(computation) = crate::rules::returned(self.domain, value)? {
                Self::set_side(goal, side, Slot::Ready(Glued::Computation(computation)));
            }
        }
        Ok(())
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
            Advance::Unfolding => Ok(Turn::Again),
            Advance::Cycle => {
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
                            NeutralHead::Variable { .. } | NeutralHead::Module(_) | NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_) => DefinitionHeight::default(),
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
                Glued::Value(value) => match self.domain.value(value) {
                    Some(&DomainValue::Neutral { neutral, .. }) => neutral,
                    Some(_) => continue,
                    None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
                },
                Glued::Computation(comp) => match self.domain.computation(comp) {
                    Some(&DomainComp::Neutral { neutral, .. }) => neutral,
                    Some(_) => continue,
                    None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
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
                Next::Classify | Next::Move(_) | Next::Combine(_) => false,
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
                Subgoal::Values(left, right) => (
                    SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                    goal.depth,
                ),
                Subgoal::Opened(left, right) => (SupportSides::Opened(left, right), goal.depth),
                Subgoal::Classifiers(left, right) => {
                    let left = self.domain.value_code(left, TermFace::Reduced);
                    let right = self.domain.value_code(right, TermFace::Reduced);
                    (
                        SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                        goal.depth,
                    )
                },
                Subgoal::CaseMotives(left, right) => {
                    let depth = deeper(goal.depth)?;
                    let variable = self.variable(goal.depth)?;
                    let left = self.case_motive(left, variable)?;
                    let right = self.case_motive(right, variable)?;
                    (
                        SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                        depth,
                    )
                },
                Subgoal::Motives(left, right) => {
                    let depth = deeper(goal.depth)?;
                    let variable = self.variable(goal.depth)?;
                    let left = self.transport_motive(left, variable)?;
                    let right = self.transport_motive(right, variable)?;
                    (
                        SupportSides::Heads(Glued::Value(left), Glued::Value(right)),
                        depth,
                    )
                },
                Subgoal::CaseBranch { left, right, tag } => {
                    let left = self.case_branch(left, tag)?;
                    let right = self.case_branch(right, tag)?;
                    (SupportSides::Closed(left, right), goal.depth)
                },
                Subgoal::Fixpoints(left, right) | Subgoal::Entered(left, right) => {
                    (SupportSides::Closed(left, right), goal.depth)
                },
                Subgoal::FixpointBodies(left, right) => {
                    let left = self.fixpoint_body(left)?;
                    let right = self.fixpoint_body(right)?;
                    (SupportSides::Opened(left, right), goal.depth)
                },
                Subgoal::SplitBodies(left, right) => {
                    let (arity, left) = self.split_body(left)?;
                    let (_, right) = self.split_body(right)?;
                    (SupportSides::OpenedUnder(left, right, arity), goal.depth)
                },
                Subgoal::OpenedUnder(left, right, count) => {
                    (SupportSides::OpenedUnder(left, right, count), goal.depth)
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

    /// Quote a transport motive under the same fresh endpoint on both sides.
    ///
    /// # Specification
    /// - requires: the supplied variable is fresh at the parent goal's depth.
    /// - ensures: a code whose type is the motive, reading that variable at
    ///   index zero and its capture beyond it.
    /// - fails: a dangling motive closure.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two stuck transports along one path compare by their
    ///   motives under the fresh endpoint; a motive read without the binder
    ///   would name the capture's innermost entry instead and change the
    ///   verdict.
    /// - witness: `identity::tests::stuck_transports_compare_by_motive_and_operand`
    #[spec(ensures:|ret| ret.is_err() || ret.as_ref().is_ok_and(|value| matches!(self.domain.value(*value),Some(DomainValue::Code { .. }))))]
    fn transport_motive(
        &mut self,
        motive: crate::arena::ValueClosureId,
        variable: DomainValueId,
    ) -> Result<DomainValueId, ConversionFault>
    {
        let closure = self
            .domain
            .value_closure(motive)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let body = closure.body();
        let mut environment = closure.environment().clone();
        environment.extend(Zone::Intuitionistic, variable);
        let quoted = self.domain.value_closure_node(body, environment);
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

    /// Capture a fixpoint's body over the fixpoint's own environment, to be
    /// opened under a fresh self variable.
    ///
    /// # Specification
    /// - requires: nothing; a capture over anything but a source fixpoint is
    ///   refused.
    /// - ensures: returns the body over the capture's environment, with no
    ///   binding added.
    /// - fails: dangling or malformed fixpoint captures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two fixpoints whose bodies differ only in a bound
    ///   name are one, and two that call themselves differently are not.
    /// - witness: `machine::tests::stuck_fixpoints_compare_by_their_bodies`
    #[spec(ensures:|ret| ret.is_err() || ret.as_ref().is_ok_and(|closure| self.domain.comp_closure(*closure).is_some()))]
    fn fixpoint_body(
        &mut self,
        recursive: CompClosureId,
    ) -> Result<CompClosureId, ConversionFault>
    {
        let body = crate::rules::fixpoint_source(self.core, self.domain, recursive)?;
        let closure = self
            .domain
            .comp_closure(recursive)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let environment = closure.environment().clone();
        Ok(self.domain.comp_closure_node(body, environment))
    }

    /// Capture a split's body over the split's own environment, to be opened
    /// under one fresh variable per component.
    ///
    /// # Specification
    /// - requires: nothing; a capture over anything but a source split is
    ///   refused.
    /// - ensures: returns the split's arity and its body over the capture's
    ///   environment, with no binding added.
    /// - fails: dangling or malformed split captures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two stuck splits whose bodies read their components
    ///   alike are one, and two that read different components are not.
    /// - witness: `machine::tests::stuck_splits_compare_by_arity_and_body`
    #[spec(ensures:|ret| ret.is_err() || ret.as_ref().is_ok_and(|&(_, closure)| self.domain.comp_closure(closure).is_some()))]
    fn split_body(
        &mut self,
        split: CompClosureId,
    ) -> Result<(gandr_core_term::ComponentCount, CompClosureId), ConversionFault>
    {
        let (arity, body) = crate::rules::split_source(self.core, self.domain, split)?;
        let closure = self
            .domain
            .comp_closure(split)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let environment = closure.environment().clone();
        Ok((arity, self.domain.comp_closure_node(body, environment)))
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
                NeutralHead::Variable { .. } | NeutralHead::Module(_) | NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_) => Err(ConversionFault::MachineInvariant),
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
            NeutralHead::Constant(constant) => Ok(constant),
            NeutralHead::Variable { .. }
            | NeutralHead::Module(_)
            | NeutralHead::Hole { .. }
            | NeutralHead::Mark { .. }
            | NeutralHead::Returned(_) => Err(ConversionFault::MachineInvariant),
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
            ConversionSide::Left => pair.0,
            ConversionSide::Right => pair.1,
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
            ConversionSide::Left => goal.left = slot,
            ConversionSide::Right => goal.right = slot,
        }
    }

    /// Unfold the defined head on `side`: record the decision and wait on the
    /// neutral's unfolding channel.
    ///
    /// # Specification
    /// - requires: `side` holds a neutral headed by a defined constant, or a
    ///   held endpoint whose computation is.
    /// - ensures: [`Advance::Cycle`] with nothing recorded when the side's
    ///   chain already holds this definition over this spine; otherwise the
    ///   chain holds it, the derivation records `Unfold` and the side's
    ///   reduction, the goal's support holds the definition, the side waits on
    ///   the neutral's unfolding, and the answer is [`Advance::Unfolding`]. For
    ///   a held endpoint, the definition and spine are those of the computation
    ///   it holds.
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
    ///   constant-only cycle key. A held endpoint's step names the definition
    ///   its computation waits on, which the kernel's replay unfolds.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::unfolding_one_function_twice_is_not_a_cycle`
    /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
    /// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
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
        let defined = self.unfolded_neutral(neutral)?;
        let constant = self.head_constant(defined)?;
        let held = self
            .domain
            .neutral(defined)
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
            ConversionSide::Left => ConversionDecision::ReduceLeft { redex: named },
            ConversionSide::Right => ConversionDecision::ReduceRight { redex: named },
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
                DomainValue::Thunk { body, .. } => {
                    let channel = self.enter_channel(body)?;
                    Self::set_side(goal, side, Slot::Waiting(channel));
                    self.depend(id, channel)?;
                },
                DomainValue::Neutral { neutral, .. } => {
                    let grown = extend_spine(self.domain, neutral, Elimination::Force)
                        .map_err(ConversionFault::Evaluation)?;
                    let forced = self.domain.comp_neutral(grown, CompTermFace::Reduced);
                    Self::set_side(goal, side, Slot::Ready(Glued::Computation(forced)));
                },
                DomainValue::PathCertificate { .. }
                | DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::Literal { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. }
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
            Some(&DomainComp::Lambda { body, .. }) => body,
            Some(_) => return Err(ConversionFault::MachineInvariant),
            None => return Err(ConversionFault::Domain(DomainFault::Dangling)),
        };
        let channel = self.open_channel(body, goal.depth, Opening::One)?;
        Self::set_side(goal, lambda_side, Slot::Waiting(channel));
        self.depend(id, channel)?;
        goal.depth = opened_depth;
        Ok(())
    }

    /// Bind the neutral on `side`, one bind short of the other, into `return`.
    ///
    /// # Specification
    /// - requires: `side` holds a neutral computation whose spine is one
    ///   elimination shorter than the other side's, which ends in a bind.
    /// - ensures: the derivation records `ReturnEta` naming `side`, and that
    ///   side becomes its neutral grown by a bind into the identity
    ///   continuation; the other side and the depth are unchanged.
    /// - provides: the η law of `F`, `M ≡ M to x. return x`.
    /// - fails: every fault the domain raises, and
    ///   [`ConversionFault::MachineInvariant`] when `side` is not a neutral.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the domain raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stuck computation against its own bind into
    ///   `return`, on either side, converts only through this step, and the
    ///   kernel replays the recorded side; growing the wrong side or recording
    ///   none refuses there.
    /// - witness: `machine::tests::the_laws_of_bind_convert_by_their_decisions`
    #[spec(
        captures: [depth = goal.depth, left = goal.left, right = goal.right],
        ensures: |ret| ret.is_err() || (goal.depth == depth && match side {
            ConversionSide::Left => goal.right == right && matches!(goal.left, Slot::Ready(Glued::Computation(_))),
            ConversionSide::Right => goal.left == left && matches!(goal.right, Slot::Ready(Glued::Computation(_))),
        }),
    )]
    fn return_eta(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Result<(), ConversionFault>
    {
        self.derivations
            .decide(id, ConversionDecision::ReturnEta { side })?;
        let neutral = self.neutral_of(Self::side_of(pair, side))?;
        let identity = self
            .domain
            .native_continuation(crate::closure::CompBody::Returned);
        let grown = extend_spine(self.domain, neutral, Elimination::Bind(identity))
            .map_err(ConversionFault::Evaluation)?;
        let bound = self.domain.comp_neutral(grown, CompTermFace::Reduced);
        Self::set_side(goal, side, Slot::Ready(Glued::Computation(bound)));
        Ok(())
    }

    /// Make the two binds in a row nearest the head of `side` one.
    ///
    /// # Specification
    /// - requires: `side` holds a neutral computation whose spine stacks two
    ///   binds in a row.
    /// - ensures: the derivation records `Reassociate` naming `side`, and the
    ///   first such pair, `(M to x. N) to y. P`, becomes one bind into the
    ///   continuation that enters `x. N` and binds its result into `y. P`, so
    ///   `M to x. (N to y. P)`; every other elimination keeps its place, the
    ///   other side and the depth are unchanged.
    /// - provides: bind associativity.
    /// - fails: every fault the domain raises, and
    ///   [`ConversionFault::MachineInvariant`] when `side` is not a neutral or
    ///   stacks no two binds.
    /// - panics: none.
    ///
    /// # Errors
    /// Every fault the domain raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a left-nested pair of binds against its right-nested
    ///   twin, on either side, converts only through this step, and an outer
    ///   continuation reading the outer binder separates fusing the two
    ///   closures from dropping either; the kernel replays the recorded side.
    /// - witness: `machine::tests::the_laws_of_bind_convert_by_their_decisions`
    #[spec(
        captures: [depth = goal.depth, left = goal.left, right = goal.right],
        ensures: |ret| ret.is_err() || (goal.depth == depth && match side {
            ConversionSide::Left => goal.right == right && matches!(goal.left, Slot::Ready(Glued::Computation(_))),
            ConversionSide::Right => goal.left == left && matches!(goal.right, Slot::Ready(Glued::Computation(_))),
        }),
    )]
    fn reassociate(
        &mut self,
        id: ProcessId,
        goal: &mut Goal,
        pair: (Glued, Glued),
        side: ConversionSide,
    ) -> Result<(), ConversionFault>
    {
        let neutral = self.neutral_of(Self::side_of(pair, side))?;
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let (head, unfolding) = (held.head(), held.unfolding());
        let mut spine = Vec::from(held.spine());
        let at = spine
            .windows(2)
            .position(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]))
            .ok_or(ConversionFault::MachineInvariant)?;
        let (Some(&Elimination::Bind(first)), Some(&Elimination::Bind(then))) =
            (spine.get(at), spine.get(at.saturating_add(1)))
        else {
            return Err(ConversionFault::MachineInvariant);
        };
        self.derivations
            .decide(id, ConversionDecision::Reassociate { side })?;
        let fused = self
            .domain
            .native_continuation(crate::closure::CompBody::Then { first, then });
        spine.splice(at ..= at.saturating_add(1), [Elimination::Bind(fused)]);
        let rebuilt = self
            .domain
            .neutral_node(head, spine, unfolding)
            .map_err(ConversionFault::Domain)?;
        let bound = self.domain.comp_neutral(rebuilt, CompTermFace::Reduced);
        Self::set_side(goal, side, Slot::Ready(Glued::Computation(bound)));
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body clones the goal's frozen constants and chain into every alternative; the check compares each clone once"
        )
    )]
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
                Next::Classify | Next::Move(_) | Next::Combine(_) => None,
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
            Combination::Biased => Combine::Biased(children),
            Combination::Either => Combine::Either(children),
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
            Move::Shortcut => {
                let left = self.neutral_of(pair.0)?;
                let right = self.neutral_of(pair.1)?;
                let constant = self.head_constant(left)?;
                self.derivations
                    .decide(id, ConversionDecision::ConstShortcut {
                        constant: TraceNode::Constant(constant),
                    })?;
                let spines = spine_subgoals(self.core, self.domain, left, right)?;
                match spines {
                    Spines::Agree(subgoals) => {
                        self.decompose(id, goal, pair, subgoals, Collapse::Never)
                    },
                    Spines::Disagree => {
                        self.answer(id, Settled::NotConvertible, &[])?;
                        Ok(Turn::Done)
                    },
                }
            },
            Move::Unfold(side) => {
                let advance = self.unfold(id, goal, pair, side)?;
                self.advanced(id, advance)
            },
            Move::FreezeUnfold(side) => {
                let constant = self.side_constant(pair, side)?;
                self.derivations.decide(id, ConversionDecision::Freeze {
                    constant: TraceNode::Constant(constant),
                    side,
                })?;
                goal.frozen.freeze(side, constant);
                let advance = self.unfold(id, goal, pair, other(side))?;
                self.advanced(id, advance)
            },
            Move::PostponeUnfold(side) => {
                let postponed = self.side_constant(pair, other(side))?;
                self.derivations.decide(id, ConversionDecision::Postpone {
                    constant: TraceNode::Constant(postponed),
                })?;
                let advance = self.unfold(id, goal, pair, side)?;
                self.advanced(id, advance)
            },
            Move::FreezeEta(side) => {
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
                        Next::Classify | Next::Move(_) => false,
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
            Combine::All {
                pair,
                children,
                collapse,
            } => {
                let mut waiting = 0_usize;
                let mut declined = None;
                for (position, &child) in children.iter().enumerate() {
                    let answered = self.outcome(child)?;
                    match answered {
                        Outcome::Settled(Settled::NotConvertible) => {
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
                        Outcome::Settled(Settled::Convertible) => {},
                        Outcome::Declined(reason) => {
                            declined.get_or_insert(reason);
                        },
                        Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
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
                    Collapse::Allowed => self.derivations.agree_on(id, pair, children)?,
                    Collapse::Never => self.derivations.rest_on(id, children)?,
                }
                Ok(Turn::Done)
            },
            Combine::Biased(children) => {
                let Some((&last, rest)) = children.split_last()
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let mut waiting = 0_usize;
                for &child in rest {
                    let answered = self.outcome(child)?;
                    match answered {
                        Outcome::Settled(Settled::Convertible) => {
                            self.answer(id, Settled::Convertible, &[child])?;
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            return Ok(Turn::Done);
                        },
                        Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        Outcome::Settled(Settled::NotConvertible) | Outcome::Declined(_) => {},
                        Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
                    }
                }
                let authoritative = self.outcome(last)?;
                match authoritative {
                    Outcome::Settled(settled) => {
                        // An acceptance rests on the winning branch; a refusal
                        // on every branch, each of which had to fail.
                        let winner = [last];
                        let basis: &[ProcessId] = match settled {
                            Settled::Convertible => &winner,
                            Settled::NotConvertible => &children,
                        };
                        self.answer(id, settled, basis)?;
                        self.derivations.rest_on(id, Vec::from([last]))?;
                        Ok(Turn::Done)
                    },
                    Outcome::Declined(_) if waiting == 0_usize => {
                        self.finish(id, authoritative)?;
                        Ok(Turn::Done)
                    },
                    Outcome::Pending | Outcome::Declined(_) => {
                        goal.next = Next::Combine(Combine::Biased(children));
                        Ok(Turn::Wait)
                    },
                    Outcome::Evaluated(_) => Err(ConversionFault::MachineInvariant),
                }
            },
            Combine::Either(children) => {
                if children.is_empty() {
                    return Err(ConversionFault::MachineInvariant);
                }
                let mut refuted = 0_usize;
                let mut waiting = 0_usize;
                let mut declined = None;
                for &child in &children {
                    let answered = self.outcome(child)?;
                    match answered {
                        Outcome::Settled(Settled::Convertible) => {
                            self.answer(id, Settled::Convertible, &[child])?;
                            self.derivations.rest_on(id, Vec::from([child]))?;
                            return Ok(Turn::Done);
                        },
                        Outcome::Settled(Settled::NotConvertible) => {
                            refuted = refuted.saturating_add(1_usize);
                        },
                        Outcome::Declined(reason) => {
                            declined.get_or_insert(reason);
                        },
                        Outcome::Pending => waiting = waiting.saturating_add(1_usize),
                        Outcome::Evaluated(_) => return Err(ConversionFault::MachineInvariant),
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
            GranularityStance::Skeleton => {},
            // The policy's constructor refuses this stance, so no installed
            // policy holds it; the arm answers a typed refusal rather than
            // standing in for a stance it does not implement.
            GranularityStance::Spinal => return Err(ConversionFault::MachineInvariant),
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
    /// - requires: `neutral` is headed by a constant with a body here, or is a
    ///   held endpoint whose computation is stuck on one.
    /// - ensures: for a constant over an empty spine, the body's own channel —
    ///   or a channel already answered with a forced body; otherwise a channel
    ///   re-applying the spine to the body once the body's channel answers, a
    ///   held endpoint's re-application running as [`Scheduler::reapplication`]
    ///   builds it. The same channel for every request naming `neutral`.
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
    ///   channel mistaken for a reapplied one. A held endpoint over a bare
    ///   definition still re-applies, since its computation's spine and its own
    ///   follow the body.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::unfolding_one_function_twice_is_not_a_cycle`
    /// - witness: `machine::tests::malformed_heads_and_channel_entries_are_refused`
    /// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
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
        let defined = self.unfolded_neutral(neutral)?;
        let held = self
            .domain
            .neutral(defined)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let unfolding = held.unfolding();
        let bare = defined == neutral && held.spine().is_empty();
        let height = match held.head() {
            NeutralHead::Constant(constant) => self.definitions.height(constant),
            NeutralHead::Variable { .. }
            | NeutralHead::Module(_)
            | NeutralHead::Hole { .. }
            | NeutralHead::Mark { .. }
            | NeutralHead::Returned(_) => {
                return Err(ConversionFault::MachineInvariant);
            },
        };
        let share = self.share_at(height);
        let channel = match (unfolding, bare) {
            (Unfolding::Rigid | Unfolding::Forced(Glued::Computation(_)), _) => {
                return Err(ConversionFault::MachineInvariant);
            },
            (Unfolding::Forced(Glued::Value(body)), true) => {
                self.start(Work::Spent, Outcome::Evaluated(Glued::Value(body)), share)?
            },
            (Unfolding::Forced(Glued::Value(body)), false) => {
                let evaluation = self.reapplication(neutral, body)?;
                self.start(
                    Work::Channel(Channel::Running(evaluation)),
                    Outcome::Pending,
                    share,
                )?
            },
            (Unfolding::Unforced(entry), true) => self.body_channel(entry, height)?,
            (Unfolding::Unforced(entry), false) => {
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

    /// The neutral whose head unfolding `neutral` unfolds: `neutral` itself,
    /// or the neutral computation a held endpoint's computation is stuck on,
    /// read inward through every held endpoint it eliminates.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `neutral` for every head but a returned endpoint's; for a
    ///   returned endpoint, the neutral [`crate::rules::held_call`] reaches
    ///   from its computation.
    /// - provides: the one place an endpoint's unfolding is read through to the
    ///   definition it waits on, so the cycle key, the recorded constant and
    ///   the channel all name that definition.
    /// - fails: [`ConversionFault::Domain`] for a dangling node;
    ///   [`ConversionFault::MachineInvariant`] for an endpoint whose walk meets
    ///   a computation that is not neutral.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held endpoint unfolds the definition its
    ///   computation waits on, also through an elimination of another held
    ///   endpoint, and the kernel replays that unfolding at the same head;
    ///   reading the endpoint's own head, or stopping at the first returned
    ///   head, refuses the unfolding.
    /// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
    /// - witness: `machine::tests::a_held_endpoint_under_an_elimination_unfolds_the_call_it_waits_on`
    #[spec(ensures: |ret| match self.domain.neutral(neutral) {
        | None => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        | Some(node) => match node.head() {
            | NeutralHead::Returned(computation) => match crate::rules::held_call(&*self.domain, computation) {
                | Ok(Some(inner)) => ret == Ok(inner),
                | Ok(None) => ret == Err(ConversionFault::MachineInvariant),
                | Err(fault) => ret == Err(fault),
            },
            | _ => ret == Ok(neutral),
        },
    })]
    fn unfolded_neutral(
        &self,
        neutral: NeutralId,
    ) -> Result<NeutralId, ConversionFault>
    {
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        let NeutralHead::Returned(computation) = held.head()
        else {
            return Ok(neutral);
        };
        crate::rules::held_call(&*self.domain, computation)?
            .ok_or(ConversionFault::MachineInvariant)
    }

    /// The evaluation re-applying `neutral`'s spine to `head`, the body of the
    /// definition its unfolding unfolds.
    ///
    /// # Specification
    /// - requires: `head` is the body of the constant heading
    ///   [`Scheduler::unfolded_neutral`] of `neutral`.
    /// - ensures: for a constant-headed neutral, [`Evaluation::eliminate`] over
    ///   its spine; for a held endpoint, [`Evaluation::endpoint`] over the
    ///   spine of the call it waits on, then the spine of each endpoint between
    ///   that call and `neutral`, `neutral`'s own last.
    /// - provides: the second half of δ for both kinds of unfoldable neutral.
    /// - fails: as [`Scheduler::unfolded_neutral`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Scheduler::unfolded_neutral`].
    ///
    /// # Termination
    /// - reason: the `while` loop collecting the endpoints' spines, which walks
    ///   the chain [`crate::rules::held_call`] walks and stops where it
    ///   stopped, not recursion.
    /// - measure: as [`crate::rules::held_call`]'s.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held endpoint under a force runs its definition,
    ///   delivers the returned value and forces it, and one under an
    ///   elimination of another held endpoint runs the inner call, delivers its
    ///   value to the elimination and delivers that in turn, so the conversion
    ///   meets what the kernel's replay meets; re-applying only the endpoint's
    ///   own spine refuses in evaluation.
    /// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
    /// - witness: `machine::tests::a_held_endpoint_under_an_elimination_unfolds_the_call_it_waits_on`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(ensures: |ret| ret.is_ok() == self.unfolded_neutral(neutral).is_ok())]
    fn reapplication(
        &self,
        neutral: NeutralId,
        head: DomainValueId,
    ) -> Result<Evaluation<'run>, ConversionFault>
    {
        let defined = self.unfolded_neutral(neutral)?;
        let held = self
            .domain
            .neutral(neutral)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        if defined == neutral {
            return Ok(Evaluation::eliminate(self.definitions, head, held.spine()));
        }
        let mut enclosing = Vec::from([held.spine()]);
        let mut focus = held;
        while let NeutralHead::Returned(computation) = focus.head()
            && let Some(&DomainComp::Neutral { neutral: inner, .. }) =
                self.domain.computation(computation)
            && inner != defined
        {
            focus = self
                .domain
                .neutral(inner)
                .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
            enclosing.push(focus.spine());
        }
        let inner = self
            .domain
            .neutral(defined)
            .ok_or(ConversionFault::Domain(DomainFault::Dangling))?;
        Ok(Evaluation::endpoint(
            self.definitions,
            head,
            inner.spine(),
            &enclosing,
        ))
    }

    /// The channel opening a closure at `level` under `arity` fresh variables,
    /// minted once per closure, level and arity.
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
        ensures: |ret| ret.as_ref().map_or(true, |channel| self.openings.get(&(closure, level, arity)) == Some(channel)
            && self.processes.get(channel.0).is_some()
            && if self.openings.len() == entries { self.processes.len() == processes }
                else { self.openings.len() == entries.saturating_add(1) && self.processes.len() == processes.saturating_add(1) })
    )]
    fn open_channel(
        &mut self,
        closure: CompClosureId,
        level: BinderLevel,
        arity: Opening,
    ) -> Result<ProcessId, ConversionFault>
    {
        if let Some(&channel) = self.openings.get(&(closure, level, arity)) {
            return Ok(channel);
        }
        let evaluation = match arity {
            Opening::One => {
                let variable = self.variable(level)?;
                Evaluation::enter(
                    self.definitions,
                    self.domain,
                    closure,
                    Bound::Variable(variable),
                )
            },
            Opening::Many(count) => {
                let mut variables = Vec::with_capacity(usize::from(count));
                let mut at = level;
                for _ in 0_usize .. usize::from(count) {
                    variables.push(self.variable(at)?);
                    at = deeper(at)?;
                }
                Evaluation::enter(
                    self.definitions,
                    self.domain,
                    closure,
                    Bound::Variables(&variables),
                )
            },
        }
        .map_err(ConversionFault::Evaluation)?;
        let share = self.share_at(DefinitionHeight::default());
        let channel = self.start(
            Work::Channel(Channel::Running(evaluation)),
            Outcome::Pending,
            share,
        )?;
        self.openings.insert((closure, level, arity), channel);
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
mod tests;
