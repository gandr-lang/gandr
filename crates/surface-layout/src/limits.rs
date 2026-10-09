//! Build- and render-phase budgets and their meters.
//!
//! Resource use in this crate is explicit rather than emergent. A caller
//! states the ceilings, the meter counts what is actually spent, and every
//! store checks its ceiling and then reserves fallibly, so exhaustion is
//! reported at the API rather than felt as allocator pressure somewhere below
//! it.
//!
//! Build accounting and render accounting are disjoint, and this is load
//! bearing: a document that is expensive to construct cannot quietly consume
//! the budget the renderer was promised, and a limit crossed during
//! finalization can never be reported as a render limit.
//!
//! # The binding defaults
//!
//! | limit                                           | default    |
//! | ----------------------------------------------- | ---------- |
//! | stored document nodes, including flatten images | 1,000,000  |
//! | uniquely stored text and verbatim bytes         | 64 MiB     |
//! | stored verbatim physical fragments              | 1,000,000  |
//! | constructor and finalization build steps        | 20,000,000 |
//!
//! # The meters
//!
//! [`BuildMeter`] and [`RenderMeter`] are neither `Clone` nor `Default`, their
//! fields stay private, and neither exposes a way to reset or decrement a
//! cumulative counter. A standing client creates one meter per document; a
//! client that emits a document in segments reuses the same meter across every
//! segment, which is what stops a long run from resetting its own accounting
//! between pieces.

use crate::error::BuildError;
use crate::error::RenderError;
use crate::error::RenderLimitKind;
use crate::units::BuildStepsUsed;
use crate::units::DocNodesUsed;
use crate::units::FrontierEntriesUsed;
use crate::units::LayoutStepsUsed;
use crate::units::MaxBuildSteps;
use crate::units::MaxDocNodes;
use crate::units::MaxFrontierEntries;
use crate::units::MaxLayoutSteps;
use crate::units::MaxLivePlanNodes;
use crate::units::MaxMemoStates;
use crate::units::MaxOutputBytes;
use crate::units::MaxPlanNodesCreated;
use crate::units::MaxResolverStack;
use crate::units::MaxResolverWorkEntries;
use crate::units::MaxTextBytes;
use crate::units::MaxVerbatimLines;
use crate::units::MaxVmStack;
use crate::units::MaxVmSteps;
use crate::units::MemoStatesUsed;
use crate::units::OutputBytesUsed;
use crate::units::PeakLivePlanNodes;
use crate::units::PeakResolverStack;
use crate::units::PeakVmStack;
use crate::units::PlanNodesCreated;
use crate::units::ResolverWorkEntriesUsed;
use crate::units::TextBytesUsed;
use crate::units::VerbatimLinesUsed;
use crate::units::VmStepsUsed;

/// The ceilings a caller sets for one document build.
///
/// # Specification
/// - requires: each ceiling is the caller's chosen value; the defaults in the
///   module table are what a caller gets by asking for none.
/// - ensures: a builder refuses rather than exceeding any of the four.
/// - provides: the complete build-phase budget, stated once.
/// - panics: none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BuildLimits
{
    /// The ceiling on stored document nodes, flatten images included.
    pub max_doc_nodes: MaxDocNodes,
    /// The ceiling on uniquely stored text and verbatim bytes.
    pub max_text_bytes: MaxTextBytes,
    /// The ceiling on stored verbatim physical fragments.
    pub max_verbatim_lines: MaxVerbatimLines,
    /// The ceiling on constructor and finalization steps.
    pub max_build_steps: MaxBuildSteps,
}

/// What one document build actually spent.
///
/// # Specification
/// - requires: the record is read from a meter that owns the counters.
/// - ensures: every field is monotone for the meter's whole lifetime.
/// - provides: an observation of build cost a caller can log, assert on, or
///   compare across runs.
/// - panics: none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BuildUsage
{
    /// Document nodes stored, flatten images included.
    pub doc_nodes: DocNodesUsed,
    /// Uniquely stored text and verbatim bytes.
    pub text_bytes: TextBytesUsed,
    /// Stored verbatim physical fragments.
    pub verbatim_lines: VerbatimLinesUsed,
    /// Constructor and finalization steps consumed.
    pub build_steps: BuildStepsUsed,
}

/// The build-phase meter: ceilings and cumulative usage for one document.
///
/// One builder borrows one meter exclusively for its whole life, so there is
/// exactly one place a build charge can be recorded.
///
/// # Specification
/// - requires: the meter is constructed from a limit record and is borrowed by
///   at most one builder at a time.
/// - ensures: a charge is checked against its ceiling before the store grows,
///   and a refused charge leaves the counter unchanged.
/// - provides: the enforcement point for every build limit in the crate.
/// - panics: none.
#[derive(Debug)]
pub struct BuildMeter
{
    /// The ceilings this meter enforces.
    limits: BuildLimits,
    /// What has been spent against them.
    used: BuildUsage,
}

impl Default for BuildLimits
{
    /// The binding defaults of the module table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            max_doc_nodes: MaxDocNodes::from(1_000_000u32),
            max_text_bytes: MaxTextBytes::from(0x0400_0000_usize),
            max_verbatim_lines: MaxVerbatimLines::from(1_000_000u32),
            max_build_steps: MaxBuildSteps::from(20_000_000u64),
        }
    }
}

impl BuildMeter
{
    /// Creates a meter with zero usage under `limits`.
    ///
    /// # Specification
    /// - requires: `limits` contains the caller's four build ceilings.
    /// - ensures: all usage counters start at zero and remain cumulative.
    /// - provides: an exclusive accounting authority for one document build.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a new meter starts all four cumulative counters at
    ///   zero and accepts the builder's singleton baseline.
    /// - witness: `algebra::tests::empty_emits_nothing_and_moves_no_column`
    #[inline]
    #[must_use = "a build meter must be retained for the document build"]
    pub fn new(limits: BuildLimits) -> Self
    {
        Self {
            limits,
            used: BuildUsage {
                doc_nodes: DocNodesUsed::from(0u64),
                text_bytes: TextBytesUsed::from(0u64),
                verbatim_lines: VerbatimLinesUsed::from(0u64),
                build_steps: BuildStepsUsed::from(0u64),
            },
        }
    }

    /// Returns the cumulative usage observed by this meter.
    ///
    /// # Specification
    /// - requires: the meter remains alive and exclusively owned by its build.
    /// - ensures: the returned snapshot is a copy and does not reset usage.
    /// - provides: monotone node, byte, fragment, and step observations.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — usage snapshots are cumulative and do not reset the
    ///   meter between observations.
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[inline]
    #[must_use]
    pub fn usage(&self) -> BuildUsage
    {
        self.used
    }

    /// Checks whether one document node can be charged without changing usage.
    ///
    /// # Specification
    /// - requires: the caller is about to store one document node.
    /// - ensures: success proves the next node charge fits its counter and
    ///   ceiling.
    /// - provides: an atomic preflight for compound builder operations.
    /// - fails: reports counter overflow or the node ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for counter overflow or `LimitExceeded` at
    /// the configured node ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the node preflight accepts the exact node boundary
    ///   and leaves usage unchanged when the next charge is refused.
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    /// - witness: `algebra::tests::a_refused_charge_leaves_the_counter_unchanged`
    #[inline]
    pub(crate) fn check_doc_node(&self) -> Result<(), BuildError>
    {
        self.used
            .doc_nodes
            .checked_charge(self.limits.max_doc_nodes)
            .map(|_| ())
    }

    /// Checks whether new text bytes can be charged without changing usage.
    ///
    /// # Specification
    /// - requires: `amount` is the byte count of a new stored identity.
    /// - ensures: success proves the byte charge fits its counter and ceiling.
    /// - provides: an atomic preflight for text and verbatim insertion.
    /// - fails: reports conversion, counter, or configured-limit overflow.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` when the amount or counter is not
    /// representable, or `LimitExceeded` at the configured byte ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text preflight accepts the exact byte boundary and
    ///   leaves usage unchanged after refusal.
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    /// - witness: `algebra::tests::a_refused_charge_leaves_the_counter_unchanged`
    #[inline]
    pub(crate) fn check_text_bytes(
        &self,
        amount: TextBytesUsed,
    ) -> Result<(), BuildError>
    {
        self.used
            .text_bytes
            .checked_charge(amount, self.limits.max_text_bytes)
            .map(|_| ())
    }

    /// Checks whether new verbatim fragments can be charged without changing
    /// usage.
    ///
    /// # Specification
    /// - requires: `amount` is the complete scan count for one new verbatim.
    /// - ensures: success proves the fragment charge fits its counter and
    ///   ceiling.
    /// - provides: an atomic preflight for verbatim insertion.
    /// - fails: reports counter overflow or the configured fragment ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for cumulative overflow or `LimitExceeded`
    /// at the configured fragment ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — verbatim preflight counts the complete scan and
    ///   refuses only the charge beyond its exact fragment ceiling.
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    /// - witness: `algebra::tests::verbatim_with_a_trailing_ending_stores_an_empty_final_fragment`
    #[inline]
    pub(crate) fn check_verbatim_lines(
        &self,
        amount: VerbatimLinesUsed,
    ) -> Result<(), BuildError>
    {
        self.used
            .verbatim_lines
            .checked_charge(amount, self.limits.max_verbatim_lines)
            .map(|_| ())
    }

    /// Checks whether one build step can be charged without changing usage.
    ///
    /// # Specification
    /// - requires: the caller has identified one checked constructor or
    ///   finalization operation.
    /// - ensures: success proves the next step fits its counter and ceiling.
    /// - provides: an atomic preflight for compound builder operations.
    /// - fails: reports counter overflow or the configured step ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for cumulative overflow or `LimitExceeded`
    /// at the configured step ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — step preflight accepts the exact work ceiling and
    ///   refuses only the next checked operation.
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    #[inline]
    pub(crate) fn check_step(&self) -> Result<(), BuildError>
    {
        self.used
            .build_steps
            .checked_charge(self.limits.max_build_steps)
            .map(|_| ())
    }

    /// Charges one stored document node after a successful preflight.
    ///
    /// # Specification
    /// - requires: [`Self::check_doc_node`] succeeded without an intervening
    ///   charge.
    /// - ensures: usage increases exactly once.
    /// - provides: node-limit accounting for original and flattened images.
    /// - fails: reports the same typed errors as the preflight if state
    ///   changed.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` if the precondition was
    /// not maintained.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a successful node preflight is consumed exactly once
    ///   and a refused charge does not mutate usage.
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_node`
    /// - witness: `algebra::tests::a_refused_charge_leaves_the_counter_unchanged`
    #[inline]
    pub(crate) fn charge_doc_node(&mut self) -> Result<(), BuildError>
    {
        self.used.doc_nodes = self
            .used
            .doc_nodes
            .checked_charge(self.limits.max_doc_nodes)?;
        Ok(())
    }

    /// Charges new text and verbatim bytes after a successful preflight.
    ///
    /// # Specification
    /// - requires: [`Self::check_text_bytes`] succeeded without an intervening
    ///   charge.
    /// - ensures: usage increases exactly by `amount`.
    /// - provides: cumulative byte accounting.
    /// - fails: reports the same typed errors as the preflight if state
    ///   changed.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` if the precondition was
    /// not maintained.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a successful byte preflight consumes exactly the
    ///   requested amount and a refusal preserves the previous usage.
    /// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
    /// - witness: `algebra::tests::a_refused_charge_leaves_the_counter_unchanged`
    #[inline]
    pub(crate) fn charge_text_bytes(
        &mut self,
        amount: TextBytesUsed,
    ) -> Result<(), BuildError>
    {
        self.used.text_bytes = self
            .used
            .text_bytes
            .checked_charge(amount, self.limits.max_text_bytes)?;
        Ok(())
    }

    /// Charges scanned verbatim fragments after a successful preflight.
    ///
    /// # Specification
    /// - requires: [`Self::check_verbatim_lines`] succeeded without an
    ///   intervening charge.
    /// - ensures: usage increases exactly by `amount`.
    /// - provides: cumulative physical-fragment accounting.
    /// - fails: reports the same typed errors as the preflight if state
    ///   changed.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` if the precondition was
    /// not maintained.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a successful fragment preflight consumes exactly the
    ///   scan count, including its final fragment.
    /// - witness: `algebra::tests::verbatim_with_a_trailing_ending_stores_an_empty_final_fragment`
    /// - witness: `algebra::tests::a_refused_charge_leaves_the_counter_unchanged`
    #[inline]
    pub(crate) fn charge_verbatim_lines(
        &mut self,
        amount: VerbatimLinesUsed,
    ) -> Result<(), BuildError>
    {
        self.used.verbatim_lines = self
            .used
            .verbatim_lines
            .checked_charge(amount, self.limits.max_verbatim_lines)?;
        Ok(())
    }

    /// Charges one checked constructor or finalization step after preflight.
    ///
    /// # Specification
    /// - requires: [`Self::check_step`] succeeded without an intervening
    ///   charge.
    /// - ensures: usage increases exactly once.
    /// - provides: cumulative build-work accounting.
    /// - fails: reports the same typed errors as the preflight if state
    ///   changed.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` if the precondition was
    /// not maintained.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a successful step preflight consumes exactly one
    ///   unit, including finalization work.
    /// - witness: `algebra::tests::every_finalization_visit_edge_and_probe_charges_a_build_step`
    /// - witness: `algebra::tests::a_refused_charge_leaves_the_counter_unchanged`
    #[inline]
    pub(crate) fn charge_step(&mut self) -> Result<(), BuildError>
    {
        self.used.build_steps = self
            .used
            .build_steps
            .checked_charge(self.limits.max_build_steps)?;
        Ok(())
    }
}
/// The ceilings a resolution or render operation enforces.
///
/// # Specification
/// - requires: every field is the caller's chosen cumulative or peak ceiling.
/// - ensures: the resolver cannot spend beyond any named resource bound.
/// - provides: one closed render-phase budget record.
/// - panics: none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RenderLimits
{
    /// In-bound memo states.
    pub max_memo_states: MaxMemoStates,
    /// Retained frontier entries.
    pub max_frontier_entries: MaxFrontierEntries,
    /// Plan nodes ever created.
    pub max_plan_nodes_created: MaxPlanNodesCreated,
    /// Simultaneously live plan nodes.
    pub max_live_plan_nodes: MaxLivePlanNodes,
    /// Output bytes accounted for.
    pub max_output_bytes: MaxOutputBytes,
    /// Layout transitions and comparisons.
    pub max_layout_steps: MaxLayoutSteps,
    /// Resolver work entries pushed.
    pub max_resolver_work_entries: MaxResolverWorkEntries,
    /// Peak resolver work-vector length.
    pub max_resolver_stack: MaxResolverStack,
    /// Virtual-machine steps.
    pub max_vm_steps: MaxVmSteps,
    /// Peak virtual-machine stack length.
    pub max_vm_stack: MaxVmStack,
}

impl Default for RenderLimits
{
    /// The binding render defaults.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            max_memo_states: MaxMemoStates::from(1_000_000u64),
            max_frontier_entries: MaxFrontierEntries::from(4_000_000u64),
            max_plan_nodes_created: MaxPlanNodesCreated::from(16_000_000u64),
            max_live_plan_nodes: MaxLivePlanNodes::from(8_000_000u64),
            max_output_bytes: MaxOutputBytes::from(0x0400_0000u64),
            max_layout_steps: MaxLayoutSteps::from(100_000_000u64),
            max_resolver_work_entries: MaxResolverWorkEntries::from(100_000_000u64),
            max_resolver_stack: MaxResolverStack::from(1_000_000u64),
            max_vm_steps: MaxVmSteps::from(100_000_000u64),
            max_vm_stack: MaxVmStack::from(1_000_000u64),
        }
    }
}

/// What one render or resolution operation spent.
///
/// # Specification
/// - requires: the record came from its owning meter.
/// - ensures: cumulative fields never decrease and peak fields retain maxima.
/// - provides: observable budget usage for diagnostics and tests.
/// - panics: none.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RenderUsage
{
    /// Memo states created.
    pub memo_states: MemoStatesUsed,
    /// Frontier entries retained.
    pub frontier_entries: FrontierEntriesUsed,
    /// Plan nodes created.
    pub plan_nodes_created: PlanNodesCreated,
    /// Peak simultaneous live plan nodes.
    pub peak_live_plan_nodes: PeakLivePlanNodes,
    /// Output bytes charged.
    pub output_bytes: OutputBytesUsed,
    /// Layout steps charged.
    pub layout_steps: LayoutStepsUsed,
    /// Resolver work entries pushed.
    pub resolver_work_entries: ResolverWorkEntriesUsed,
    /// Peak resolver stack length.
    pub peak_resolver_stack: PeakResolverStack,
    /// Virtual-machine steps charged.
    pub vm_steps: VmStepsUsed,
    /// Peak virtual-machine stack length.
    pub peak_vm_stack: PeakVmStack,
}

/// The render-phase meter shared by resolution and the render machine.
///
/// # Specification
/// - requires: one meter is mutably borrowed by each operation.
/// - ensures: every cumulative charge is checked before work or storage grows.
/// - provides: the shared accounting authority for resolution and rendering.
/// - fails: returns a typed error at the first refused charge.
/// - panics: none.
#[derive(Debug)]
pub struct RenderMeter
{
    /// The ceilings this meter enforces.
    limits: RenderLimits,
    /// The cumulative and peak usage observed so far.
    used: RenderUsage,
    /// Current live plan nodes.
    live_plan_nodes: u64,
}

impl RenderMeter
{
    /// Creates a zeroed render meter under `limits`.
    ///
    /// # Specification
    /// - requires: `limits` contains finite caller-selected ceilings.
    /// - ensures: every usage counter starts at zero.
    /// - provides: the shared render accounting authority.
    /// - panics: none.
    #[inline]
    #[must_use = "the render meter must be retained for resolution"]
    pub fn new(limits: RenderLimits) -> Self
    {
        Self {
            limits,
            used: RenderUsage {
                memo_states: MemoStatesUsed::from(0u64),
                frontier_entries: FrontierEntriesUsed::from(0u64),
                plan_nodes_created: PlanNodesCreated::from(0u64),
                peak_live_plan_nodes: PeakLivePlanNodes::from(0u64),
                output_bytes: OutputBytesUsed::from(0u64),
                layout_steps: LayoutStepsUsed::from(0u64),
                resolver_work_entries: ResolverWorkEntriesUsed::from(0u64),
                peak_resolver_stack: PeakResolverStack::from(0u64),
                vm_steps: VmStepsUsed::from(0u64),
                peak_vm_stack: PeakVmStack::from(0u64),
            },
            live_plan_nodes: 0u64,
        }
    }

    /// Returns the cumulative and peak usage without resetting the meter.
    ///
    /// # Specification
    /// - requires: the meter remains alive.
    /// - ensures: the snapshot is independent and does not alter usage.
    /// - provides: the current render accounting projection.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn usage(&self) -> RenderUsage
    {
        self.used
    }

    /// Charges one memo state.
    ///
    /// # Specification
    /// - requires: a new in-bound context is about to enter the memo table.
    /// - ensures: the state is charged before table insertion.
    /// - provides: memo-state accounting.
    /// - fails: returns the memo-state limit or arithmetic error.
    /// - panics: none.
    pub(crate) fn charge_memo_state(&mut self) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.memo_states);
        let next = current
            .checked_add(1u64)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::StepCounter,
            })?;
        let limit = u64::from(self.limits.max_memo_states);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::MemoStates,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        self.used.memo_states = MemoStatesUsed::from(next);
        Ok(())
    }

    /// Charges one retained frontier entry.
    ///
    /// # Specification
    /// - requires: the entry is about to be retained by a frontier.
    /// - ensures: the cumulative frontier ceiling is checked first.
    /// - provides: frontier accounting.
    /// - fails: returns the frontier-entry limit or arithmetic error.
    /// - panics: none.
    pub(crate) fn charge_frontier_entry(&mut self) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.frontier_entries);
        let next = current
            .checked_add(1u64)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::StepCounter,
            })?;
        let limit = u64::from(self.limits.max_frontier_entries);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::FrontierEntries,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        self.used.frontier_entries = FrontierEntriesUsed::from(next);
        Ok(())
    }

    /// Charges one plan allocation and one live node.
    ///
    /// # Specification
    /// - requires: the plan node is about to enter the plan arena.
    /// - ensures: both cumulative and simultaneous ceilings are checked first.
    /// - provides: plan-storage accounting.
    /// - fails: returns the first exceeded plan limit or allocation error.
    /// - panics: none.
    pub(crate) fn charge_plan_node(&mut self) -> Result<(), RenderError>
    {
        let created = u64::from(self.used.plan_nodes_created);
        let next_created = created
            .checked_add(1u64)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::PlanRefcount,
            })?;
        let created_limit = u64::from(self.limits.max_plan_nodes_created);
        if next_created > created_limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::PlanNodesCreated,
                limit: crate::units::LimitBound::from(created_limit),
            });
        }
        let next_live =
            self.live_plan_nodes
                .checked_add(1u64)
                .ok_or(RenderError::ArithmeticOverflow {
                    operation: crate::error::RenderArithmetic::PlanRefcount,
                })?;
        let live_limit = u64::from(self.limits.max_live_plan_nodes);
        if next_live > live_limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::LivePlanNodes,
                limit: crate::units::LimitBound::from(live_limit),
            });
        }
        self.used.plan_nodes_created = PlanNodesCreated::from(next_created);
        self.live_plan_nodes = next_live;
        if next_live > u64::from(self.used.peak_live_plan_nodes) {
            self.used.peak_live_plan_nodes = PeakLivePlanNodes::from(next_live);
        }
        Ok(())
    }

    /// Releases one live plan node after its final reference disappears.
    ///
    /// # Specification
    /// - requires: `charge_plan_node` established a live node first.
    /// - ensures: the live gauge decreases without changing cumulative usage.
    /// - provides: peak-versus-live plan accounting.
    /// - panics: none.
    #[inline]
    pub(crate) fn release_plan_node(&mut self)
    {
        self.live_plan_nodes = self.live_plan_nodes.saturating_sub(1u64);
    }

    /// Charges output bytes before output storage grows.
    ///
    /// # Specification
    /// - requires: `amount` is the exact append size.
    /// - ensures: the cumulative output ceiling is checked before appending.
    /// - provides: output accounting for both the resolver and VM.
    /// - fails: returns the output limit or checked arithmetic error.
    /// - panics: none.
    pub(crate) fn charge_output_bytes(
        &mut self,
        amount: crate::units::OutputBytes,
    ) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.output_bytes);
        let next =
            current
                .checked_add(u64::from(amount))
                .ok_or(RenderError::ArithmeticOverflow {
                    operation: crate::error::RenderArithmetic::OutputBytes,
                })?;
        let limit = u64::from(self.limits.max_output_bytes);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::OutputBytes,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        self.used.output_bytes = OutputBytesUsed::from(next);
        Ok(())
    }
    /// Checks output bytes without changing the cumulative counter.
    ///
    /// # Specification
    /// - requires: `amount` is the selected measure's exact output size.
    /// - ensures: success proves the next append sequence fits its ceiling.
    /// - provides: a preflight boundary before the one output reservation.
    /// - fails: returns the output limit or checked arithmetic error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` when the cumulative count cannot advance,
    /// or `LimitExceeded` when the output ceiling would be crossed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the selected output preflight rejects an over-limit
    ///   measure without mutating cumulative output usage.
    /// - witness: `algebra::tests::render_limits_fail_without_partial_output`
    pub(crate) fn check_output_bytes(
        &self,
        amount: crate::units::OutputBytes,
    ) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.output_bytes);
        let next =
            current
                .checked_add(u64::from(amount))
                .ok_or(RenderError::ArithmeticOverflow {
                    operation: crate::error::RenderArithmetic::OutputBytes,
                })?;
        let limit = u64::from(self.limits.max_output_bytes);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::OutputBytes,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        Ok(())
    }

    /// Charges one resolver transition, comparison, or edge.
    ///
    /// # Specification
    /// - requires: one layout operation is about to execute.
    /// - ensures: cumulative layout work is checked before execution.
    /// - provides: the resolver's work bound.
    /// - fails: returns the layout-step limit or arithmetic error.
    /// - panics: none.
    pub(crate) fn charge_layout_step(&mut self) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.layout_steps);
        let next = current
            .checked_add(1u64)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::StepCounter,
            })?;
        let limit = u64::from(self.limits.max_layout_steps);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::LayoutSteps,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        self.used.layout_steps = LayoutStepsUsed::from(next);
        Ok(())
    }

    /// Charges a resolver-work push and updates its peak stack gauge.
    ///
    /// # Specification
    /// - requires: `depth` is the resulting live work-vector length.
    /// - ensures: cumulative and peak resolver-stack ceilings are checked.
    /// - provides: one metered push boundary for the iterative resolver.
    /// - fails: returns a cumulative, peak, or arithmetic render error.
    /// - panics: none.
    pub(crate) fn push_resolver_work(
        &mut self,
        depth: crate::units::PeakResolverStack,
    ) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.resolver_work_entries);
        let next = current
            .checked_add(1u64)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::ResolverWorkCounter,
            })?;
        let limit = u64::from(self.limits.max_resolver_work_entries);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::ResolverWorkEntries,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        let depth_value = u64::from(depth);
        let stack_limit = u64::from(self.limits.max_resolver_stack);
        if depth_value > stack_limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::ResolverStack,
                limit: crate::units::LimitBound::from(stack_limit),
            });
        }
        self.used.resolver_work_entries = ResolverWorkEntriesUsed::from(next);
        if depth_value > u64::from(self.used.peak_resolver_stack) {
            self.used.peak_resolver_stack = PeakResolverStack::from(depth_value);
        }
        Ok(())
    }

    /// Charges one render-machine step.
    ///
    /// # Specification
    /// - requires: one plan identity is about to be popped.
    /// - ensures: the cumulative machine ceiling is checked before execution.
    /// - provides: machine-step accounting.
    /// - fails: returns the machine-step limit or arithmetic error.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::LimitExceeded`] when the machine-step ceiling is
    /// reached, or [`RenderError::ArithmeticOverflow`] if the counter cannot
    /// advance.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — machine steps reject the first over-limit pop before
    ///   usage changes.
    /// - witness: `vm::tests::vm_step_limit_is_checked_before_usage_changes`
    #[inline]
    pub(crate) fn charge_vm_step(&mut self) -> Result<(), RenderError>
    {
        let current = u64::from(self.used.vm_steps);
        let next = current
            .checked_add(1u64)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: crate::error::RenderArithmetic::StepCounter,
            })?;
        let limit = u64::from(self.limits.max_vm_steps);
        if next > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::VmSteps,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        self.used.vm_steps = VmStepsUsed::from(next);
        Ok(())
    }

    /// Checks and records a render-machine stack peak.
    ///
    /// # Specification
    /// - requires: `depth` is the resulting live machine-stack length.
    /// - ensures: the configured peak is checked before a push.
    /// - provides: machine-stack accounting.
    /// - fails: returns the machine-stack limit when exceeded.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::LimitExceeded`] when `depth` exceeds the
    /// configured machine-stack ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — machine-stack peaks reject the first over-limit depth
    ///   before the recorded peak changes.
    /// - witness: `vm::tests::vm_stack_limit_is_checked_before_peak_changes`
    #[inline]
    pub(crate) fn observe_vm_stack(
        &mut self,
        depth: PeakVmStack,
    ) -> Result<(), RenderError>
    {
        let value = u64::from(depth);
        let limit = u64::from(self.limits.max_vm_stack);
        if value > limit {
            return Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::VmStack,
                limit: crate::units::LimitBound::from(limit),
            });
        }
        if value > u64::from(self.used.peak_vm_stack) {
            self.used.peak_vm_stack = PeakVmStack::from(value);
        }
        Ok(())
    }
}
