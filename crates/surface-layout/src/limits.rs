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

use anodized::spec;

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
/// - executable: none — this configuration declaration has no invocation
///   boundary; constructors and checked meter transitions carry its executable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — distinct counters are charged through exact ceilings,
///   followed by refusals and seeded u64 overflow. Exact snapshots and typed
///   errors distinguish off-by-one admission, double charging, changes to
///   unrelated counters and mutation before refusal. Preflights must leave the
///   complete snapshot unchanged.
/// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
/// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
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
/// - executable: none — this snapshot declaration has no invocation boundary;
///   constructors and checked meter transitions carry its executable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — distinct counters are charged through exact ceilings,
///   followed by refusals and seeded u64 overflow. Exact snapshots and typed
///   errors distinguish off-by-one admission, double charging, changes to
///   unrelated counters and mutation before refusal. Preflights must leave the
///   complete snapshot unchanged.
/// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
/// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
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
/// - executable: none — this state declaration has no invocation boundary;
///   constructors and checked meter transitions carry its executable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — distinct counters are charged through exact ceilings,
///   followed by refusals and seeded u64 overflow. Exact snapshots and typed
///   errors distinguish off-by-one admission, double charging, changes to
///   unrelated counters and mutation before refusal. Preflights must leave the
///   complete snapshot unchanged.
/// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
/// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
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
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| ret.limits == limits
                && u64::from(ret.used.doc_nodes) == 0
                && u64::from(ret.used.text_bytes) == 0
                && u64::from(ret.used.verbatim_lines) == 0
                && u64::from(ret.used.build_steps) == 0
    )]
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
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| ret == self.used
    )]
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
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| { let next = u128::from(u64::from(self.used.doc_nodes)).saturating_add(u128::from(1_u64));
            let ceiling = Some(u64::from(u32::from(self.limits.max_doc_nodes)));
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::NodeCount } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::DocNodes, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))) }
    )]
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
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| { let next = u128::from(u64::from(self.used.text_bytes)).saturating_add(u128::from(u64::from(amount)));
            let ceiling = u64::try_from(usize::from(self.limits.max_text_bytes)).ok();
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::TextBytes } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::TextBytes, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))) }
    )]
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
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| { let next = u128::from(u64::from(self.used.verbatim_lines)).saturating_add(u128::from(u64::from(amount)));
            let ceiling = Some(u64::from(u32::from(self.limits.max_verbatim_lines)));
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::VerbatimLines } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::VerbatimLines, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))) }
    )]
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
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        ensures: |ret| { let next = u128::from(u64::from(self.used.build_steps)).saturating_add(u128::from(1_u64));
            let ceiling = Some(u64::from(self.limits.max_build_steps));
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::BuildSteps } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::BuildSteps, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))) }
    )]
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
    /// - requires: the caller attempts one checked unit of this resource;
    ///   exhausted budgets remain in the domain.
    /// - ensures: success adds the requested amount exactly once; refusal
    ///   leaves every usage counter unchanged.
    /// - provides: cumulative build accounting consistent with the
    ///   corresponding preflight.
    /// - fails: reports arithmetic overflow before the resource ceiling,
    ///   without a partial charge.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` when the requested
    /// charge cannot fit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        captures: before = self.used,
        ensures: |ret| { let next = u128::from(u64::from(before.doc_nodes)).saturating_add(u128::from(1_u64));
            let ceiling = Some(u64::from(u32::from(self.limits.max_doc_nodes)));
            ret.as_ref().map_or_else(|error| self.used == before
                && { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::NodeCount } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::DocNodes, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))
                && u128::from(u64::from(self.used.doc_nodes)) == next
                && self.used == BuildUsage { doc_nodes: self.used.doc_nodes, ..before }) }
    )]
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
    /// - requires: `amount` describes the new stored identity; exhausted
    ///   budgets remain in the domain.
    /// - ensures: success adds the requested amount exactly once; refusal
    ///   leaves every usage counter unchanged.
    /// - provides: cumulative build accounting consistent with the
    ///   corresponding preflight.
    /// - fails: reports arithmetic overflow before the resource ceiling,
    ///   without a partial charge.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` when the requested
    /// charge cannot fit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        captures: before = self.used,
        ensures: |ret| { let next = u128::from(u64::from(before.text_bytes)).saturating_add(u128::from(u64::from(amount)));
            let ceiling = u64::try_from(usize::from(self.limits.max_text_bytes)).ok();
            ret.as_ref().map_or_else(|error| self.used == before
                && { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::TextBytes } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::TextBytes, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))
                && u128::from(u64::from(self.used.text_bytes)) == next
                && self.used == BuildUsage { text_bytes: self.used.text_bytes, ..before }) }
    )]
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
    /// - requires: `amount` describes the new stored identity; exhausted
    ///   budgets remain in the domain.
    /// - ensures: success adds the requested amount exactly once; refusal
    ///   leaves every usage counter unchanged.
    /// - provides: cumulative build accounting consistent with the
    ///   corresponding preflight.
    /// - fails: reports arithmetic overflow before the resource ceiling,
    ///   without a partial charge.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` when the requested
    /// charge cannot fit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        captures: before = self.used,
        ensures: |ret| { let next = u128::from(u64::from(before.verbatim_lines)).saturating_add(u128::from(u64::from(amount)));
            let ceiling = Some(u64::from(u32::from(self.limits.max_verbatim_lines)));
            ret.as_ref().map_or_else(|error| self.used == before
                && { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::VerbatimLines } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::VerbatimLines, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))
                && u128::from(u64::from(self.used.verbatim_lines)) == next
                && self.used == BuildUsage { verbatim_lines: self.used.verbatim_lines, ..before }) }
    )]
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
    /// - requires: the caller attempts one checked unit of this resource;
    ///   exhausted budgets remain in the domain.
    /// - ensures: success adds the requested amount exactly once; refusal
    ///   leaves every usage counter unchanged.
    /// - provides: cumulative build accounting consistent with the
    ///   corresponding preflight.
    /// - fails: reports arithmetic overflow before the resource ceiling,
    ///   without a partial charge.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` or `LimitExceeded` when the requested
    /// charge cannot fit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct counters are charged through exact ceilings,
    ///   followed by refusals and seeded u64 overflow. Exact snapshots and
    ///   typed errors distinguish off-by-one admission, double charging,
    ///   changes to unrelated counters and mutation before refusal. Preflights
    ///   must leave the complete snapshot unchanged.
    /// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
    /// - witness: `algebra::tests::build_usage_is_monotone_across_a_whole_document`
    #[spec(
        captures: before = self.used,
        ensures: |ret| { let next = u128::from(u64::from(before.build_steps)).saturating_add(u128::from(1_u64));
            let ceiling = Some(u64::from(self.limits.max_build_steps));
            ret.as_ref().map_or_else(|error| self.used == before
                && { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: crate::error::BuildArithmetic::BuildSteps } }
            else { ceiling.is_some_and(|limit| next > u128::from(limit)
                && *error == BuildError::LimitExceeded { kind: crate::error::BuildLimitKind::BuildSteps, limit: crate::units::LimitBound::from(limit) }) } },
            |&()| next <= u128::from(u64::MAX)
                && ceiling.is_some_and(|limit| next <= u128::from(limit))
                && u128::from(u64::from(self.used.build_steps)) == next
                && self.used == BuildUsage { build_steps: self.used.build_steps, ..before }) }
    )]
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
/// - executable: none — this configuration declaration has no invocation
///   boundary; constructors and checked meter transitions carry its executable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — exact ceilings, the first excess and seeded u64 overflow
///   are observed as complete usage snapshots and typed refusals. Wrong
///   increments, shifted boundaries, changes to unrelated counters and mutation
///   before refusal change those observations; peak counters must retain their
///   maximum.
/// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
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
/// - executable: none — this snapshot declaration has no invocation boundary;
///   constructors and checked meter transitions carry its executable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — exact ceilings, the first excess and seeded u64 overflow
///   are observed as complete usage snapshots and typed refusals. Wrong
///   increments, shifted boundaries, changes to unrelated counters and mutation
///   before refusal change those observations; peak counters must retain their
///   maximum.
/// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
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
/// - executable: none — this state declaration has no invocation boundary;
///   constructors and checked meter transitions carry its executable
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — exact ceilings, the first excess and seeded u64 overflow
///   are observed as complete usage snapshots and typed refusals. Wrong
///   increments, shifted boundaries, changes to unrelated counters and mutation
///   before refusal change those observations; peak counters must retain their
///   maximum.
/// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        ensures: |ret| ret.limits == limits
                && ret.live_plan_nodes == 0
                && u64::from(ret.used.memo_states) == 0
                && u64::from(ret.used.frontier_entries) == 0
                && u64::from(ret.used.plan_nodes_created) == 0
                && u64::from(ret.used.peak_live_plan_nodes) == 0
                && u64::from(ret.used.output_bytes) == 0
                && u64::from(ret.used.layout_steps) == 0
                && u64::from(ret.used.resolver_work_entries) == 0
                && u64::from(ret.used.peak_resolver_stack) == 0
                && u64::from(ret.used.vm_steps) == 0
                && u64::from(ret.used.peak_vm_stack) == 0
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        ensures: |ret| ret == self.used
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let next = u128::from(u64::from(before.0.memo_states)).saturating_add(u128::from(1_u64));
            let limit = u64::from(self.limits.max_memo_states);
            self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::StepCounter } }
            else { next > u128::from(limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::MemoStates, limit: crate::units::LimitBound::from(limit) } },
            |&()| next <= u128::from(limit)
                && u128::from(u64::from(self.used.memo_states)) == next
                && self.used == RenderUsage { memo_states: self.used.memo_states, ..before.0 }) }
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let next = u128::from(u64::from(before.0.frontier_entries)).saturating_add(u128::from(1_u64));
            let limit = u64::from(self.limits.max_frontier_entries);
            self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::StepCounter } }
            else { next > u128::from(limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::FrontierEntries, limit: crate::units::LimitBound::from(limit) } },
            |&()| next <= u128::from(limit)
                && u128::from(u64::from(self.used.frontier_entries)) == next
                && self.used == RenderUsage { frontier_entries: self.used.frontier_entries, ..before.0 }) }
    )]
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
    /// - fails: returns the first exceeded plan limit or arithmetic error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — coupled cumulative/live limits and cumulative/depth
    ///   limits are crossed independently and together, with u64 overflow,
    ///   releases and lower later depths. Complete snapshots, exact refusal
    ///   kinds and retained peaks distinguish partial updates, reversed refusal
    ///   precedence and confusing a live gauge with a cumulative or peak
    ///   counter.
    /// - witness: `limits::tests::compound_plan_and_work_charges_refuse_before_any_counter_changes`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let created = u128::from(u64::from(before.0.plan_nodes_created)).saturating_add(1);
            let live = u128::from(before.1).saturating_add(1);
            let created_limit = u64::from(self.limits.max_plan_nodes_created);
            let live_limit = u64::from(self.limits.max_live_plan_nodes);
            ret.as_ref().map_or_else(|error| self.used == before.0
                && self.live_plan_nodes == before.1
                && if created > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::PlanRefcount } }
            else if created > u128::from(created_limit) { *error == RenderError::LimitExceeded { kind: RenderLimitKind::PlanNodesCreated, limit: crate::units::LimitBound::from(created_limit) } }
            else if live > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::PlanRefcount } }
            else { live > u128::from(live_limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::LivePlanNodes, limit: crate::units::LimitBound::from(live_limit) } },
            |&()| created <= u128::from(created_limit)
                && live <= u128::from(live_limit)
                && u128::from(u64::from(self.used.plan_nodes_created)) == created
                && u128::from(self.live_plan_nodes) == live
                && u64::from(self.used.peak_live_plan_nodes) == u64::from(before.0.peak_live_plan_nodes).max(self.live_plan_nodes)
                && self.used == RenderUsage { plan_nodes_created: self.used.plan_nodes_created, peak_live_plan_nodes: self.used.peak_live_plan_nodes, ..before.0 }) }
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — coupled cumulative/live limits and cumulative/depth
    ///   limits are crossed independently and together, with u64 overflow,
    ///   releases and lower later depths. Complete snapshots, exact refusal
    ///   kinds and retained peaks distinguish partial updates, reversed refusal
    ///   precedence and confusing a live gauge with a cumulative or peak
    ///   counter.
    /// - witness: `limits::tests::compound_plan_and_work_charges_refuse_before_any_counter_changes`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |_| self.used == before.0
                && self.live_plan_nodes == before.1.saturating_sub(1)
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let next = u128::from(u64::from(before.0.output_bytes)).saturating_add(u128::from(u64::from(amount)));
            let limit = u64::from(self.limits.max_output_bytes);
            self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::OutputBytes } }
            else { next > u128::from(limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::OutputBytes, limit: crate::units::LimitBound::from(limit) } },
            |&()| next <= u128::from(limit)
                && u128::from(u64::from(self.used.output_bytes)) == next
                && self.used == RenderUsage { output_bytes: self.used.output_bytes, ..before.0 }) }
    )]
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
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        ensures: |ret| { let next = u128::from(u64::from(self.used.output_bytes)).saturating_add(u128::from(u64::from(amount)));
            let limit = u64::from(self.limits.max_output_bytes);
            ret.as_ref().map_or_else(|error| if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::OutputBytes } }
            else { next > u128::from(limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::OutputBytes, limit: crate::units::LimitBound::from(limit) } },
            |&()| next <= u128::from(limit)) }
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let next = u128::from(u64::from(before.0.layout_steps)).saturating_add(u128::from(1_u64));
            let limit = u64::from(self.limits.max_layout_steps);
            self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::StepCounter } }
            else { next > u128::from(limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::LayoutSteps, limit: crate::units::LimitBound::from(limit) } },
            |&()| next <= u128::from(limit)
                && u128::from(u64::from(self.used.layout_steps)) == next
                && self.used == RenderUsage { layout_steps: self.used.layout_steps, ..before.0 }) }
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — coupled cumulative/live limits and cumulative/depth
    ///   limits are crossed independently and together, with u64 overflow,
    ///   releases and lower later depths. Complete snapshots, exact refusal
    ///   kinds and retained peaks distinguish partial updates, reversed refusal
    ///   precedence and confusing a live gauge with a cumulative or peak
    ///   counter.
    /// - witness: `limits::tests::compound_plan_and_work_charges_refuse_before_any_counter_changes`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let next = u128::from(u64::from(before.0.resolver_work_entries)).saturating_add(1);
            let limit = u64::from(self.limits.max_resolver_work_entries);
            let stack_limit = u64::from(self.limits.max_resolver_stack);
            self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::ResolverWorkCounter } }
            else if next > u128::from(limit) { *error == RenderError::LimitExceeded { kind: RenderLimitKind::ResolverWorkEntries, limit: crate::units::LimitBound::from(limit) } }
            else { u64::from(depth) > stack_limit
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::ResolverStack, limit: crate::units::LimitBound::from(stack_limit) } },
            |&()| next <= u128::from(limit)
                && u64::from(depth) <= stack_limit
                && u128::from(u64::from(self.used.resolver_work_entries)) == next
                && u64::from(self.used.peak_resolver_stack) == u64::from(before.0.peak_resolver_stack).max(u64::from(depth))
                && self.used == RenderUsage { resolver_work_entries: self.used.resolver_work_entries, peak_resolver_stack: self.used.peak_resolver_stack, ..before.0 }) }
    )]
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
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| { let next = u128::from(u64::from(before.0.vm_steps)).saturating_add(u128::from(1_u64));
            let limit = u64::from(self.limits.max_vm_steps);
            self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && if next > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: crate::error::RenderArithmetic::StepCounter } }
            else { next > u128::from(limit)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::VmSteps, limit: crate::units::LimitBound::from(limit) } },
            |&()| next <= u128::from(limit)
                && u128::from(u64::from(self.used.vm_steps)) == next
                && self.used == RenderUsage { vm_steps: self.used.vm_steps, ..before.0 }) }
    )]
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
    /// - hypothesis: L3 — exact ceilings, the first excess and seeded u64
    ///   overflow are observed as complete usage snapshots and typed refusals.
    ///   Wrong increments, shifted boundaries, changes to unrelated counters
    ///   and mutation before refusal change those observations; peak counters
    ///   must retain their maximum.
    /// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
    #[spec(
        captures: before = (self.used, self.live_plan_nodes),
        ensures: |ret| self.live_plan_nodes == before.1
                && ret.as_ref().map_or_else(|error| self.used == before.0
                && u64::from(depth) > u64::from(self.limits.max_vm_stack)
                && *error == RenderError::LimitExceeded { kind: RenderLimitKind::VmStack, limit: crate::units::LimitBound::from(u64::from(self.limits.max_vm_stack)) },
            |&()| u64::from(depth) <= u64::from(self.limits.max_vm_stack)
                && u64::from(self.used.peak_vm_stack) == u64::from(before.0.peak_vm_stack).max(u64::from(depth))
                && self.used == RenderUsage { peak_vm_stack: self.used.peak_vm_stack, ..before.0 })
    )]
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

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::error::BuildArithmetic;
    use crate::error::BuildLimitKind;
    use crate::error::RenderArithmetic;
    use crate::units::LimitBound;
    use crate::units::OutputBytes;

    /// Preflight and refusal preserve all counters; successful charges change
    /// only their resource.
    #[test]
    fn build_meter_charges_are_atomic_and_preflights_do_not_spend()
    {
        let limits = BuildLimits {
            max_doc_nodes: MaxDocNodes::from(13_u32),
            max_text_bytes: MaxTextBytes::from(17_usize),
            max_verbatim_lines: MaxVerbatimLines::from(19_u32),
            max_build_steps: MaxBuildSteps::from(23_u64),
        };
        let empty = BuildMeter::new(limits).usage();
        assert_eq!(
            [
                u64::from(empty.doc_nodes),
                u64::from(empty.text_bytes),
                u64::from(empty.verbatim_lines),
                u64::from(empty.build_steps)
            ],
            [0_u64; 4]
        );
        let seed = BuildUsage {
            doc_nodes: DocNodesUsed::from(3_u64),
            text_bytes: TextBytesUsed::from(5_u64),
            verbatim_lines: VerbatimLinesUsed::from(7_u64),
            build_steps: BuildStepsUsed::from(11_u64),
        };
        {
            let limits = BuildLimits {
                max_doc_nodes: MaxDocNodes::from(3_u32),
                ..limits
            };
            for current in [0_u64, 2, 3] {
                let mut meter = BuildMeter::new(limits);
                meter.used = BuildUsage {
                    doc_nodes: DocNodesUsed::from(current),
                    ..seed
                };
                let before = meter.usage();
                let expected = if current < 3 {
                    Ok(())
                }
                else {
                    Err(BuildError::LimitExceeded {
                        kind: BuildLimitKind::DocNodes,
                        limit: LimitBound::from(3_u64),
                    })
                };
                assert_eq!(meter.check_doc_node(), expected);
                assert_eq!(meter.usage(), before);
                assert_eq!(meter.charge_doc_node(), expected);
                let after = if expected.is_ok() {
                    BuildUsage {
                        doc_nodes: DocNodesUsed::from(current.saturating_add(1)),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
            }
        }
        {
            let limits = BuildLimits {
                max_text_bytes: MaxTextBytes::from(3_usize),
                ..limits
            };
            for current in [0_u64, 2, 3] {
                let mut meter = BuildMeter::new(limits);
                meter.used = BuildUsage {
                    text_bytes: TextBytesUsed::from(current),
                    ..seed
                };
                let before = meter.usage();
                let expected = if current < 3 {
                    Ok(())
                }
                else {
                    Err(BuildError::LimitExceeded {
                        kind: BuildLimitKind::TextBytes,
                        limit: LimitBound::from(3_u64),
                    })
                };
                assert_eq!(meter.check_text_bytes(TextBytesUsed::from(1_u64)), expected);
                assert_eq!(meter.usage(), before);
                assert_eq!(
                    meter.charge_text_bytes(TextBytesUsed::from(1_u64)),
                    expected
                );
                let after = if expected.is_ok() {
                    BuildUsage {
                        text_bytes: TextBytesUsed::from(current.saturating_add(1)),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
            }
        }
        {
            let limits = BuildLimits {
                max_verbatim_lines: MaxVerbatimLines::from(3_u32),
                ..limits
            };
            for current in [0_u64, 2, 3] {
                let mut meter = BuildMeter::new(limits);
                meter.used = BuildUsage {
                    verbatim_lines: VerbatimLinesUsed::from(current),
                    ..seed
                };
                let before = meter.usage();
                let expected = if current < 3 {
                    Ok(())
                }
                else {
                    Err(BuildError::LimitExceeded {
                        kind: BuildLimitKind::VerbatimLines,
                        limit: LimitBound::from(3_u64),
                    })
                };
                assert_eq!(
                    meter.check_verbatim_lines(VerbatimLinesUsed::from(1_u64)),
                    expected
                );
                assert_eq!(meter.usage(), before);
                assert_eq!(
                    meter.charge_verbatim_lines(VerbatimLinesUsed::from(1_u64)),
                    expected
                );
                let after = if expected.is_ok() {
                    BuildUsage {
                        verbatim_lines: VerbatimLinesUsed::from(current.saturating_add(1)),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
            }
        }
        {
            let limits = BuildLimits {
                max_build_steps: MaxBuildSteps::from(3_u64),
                ..limits
            };
            for current in [0_u64, 2, 3] {
                let mut meter = BuildMeter::new(limits);
                meter.used = BuildUsage {
                    build_steps: BuildStepsUsed::from(current),
                    ..seed
                };
                let before = meter.usage();
                let expected = if current < 3 {
                    Ok(())
                }
                else {
                    Err(BuildError::LimitExceeded {
                        kind: BuildLimitKind::BuildSteps,
                        limit: LimitBound::from(3_u64),
                    })
                };
                assert_eq!(meter.check_step(), expected);
                assert_eq!(meter.usage(), before);
                assert_eq!(meter.charge_step(), expected);
                let after = if expected.is_ok() {
                    BuildUsage {
                        build_steps: BuildStepsUsed::from(current.saturating_add(1)),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
            }
        }
        let mut meter = BuildMeter::new(BuildLimits {
            max_build_steps: MaxBuildSteps::from(u64::MAX),
            ..limits
        });
        meter.used = BuildUsage {
            build_steps: BuildStepsUsed::from(u64::MAX),
            ..seed
        };
        let before = meter.usage();
        let overflow = Err(BuildError::ArithmeticOverflow {
            operation: BuildArithmetic::BuildSteps,
        });
        assert_eq!(meter.check_step(), overflow);
        assert_eq!(meter.charge_step(), overflow);
        assert_eq!(meter.usage(), before);
    }

    /// Individual charges preserve unrelated resources and retain the highest
    /// observed stack depth.
    #[test]
    fn render_meter_charges_preserve_refusal_and_peak_boundaries()
    {
        let limits = RenderLimits::default();
        let empty = RenderMeter::new(limits);
        assert_eq!(
            [
                u64::from(empty.usage().memo_states),
                u64::from(empty.usage().frontier_entries),
                u64::from(empty.usage().plan_nodes_created),
                u64::from(empty.usage().peak_live_plan_nodes),
                u64::from(empty.usage().output_bytes),
                u64::from(empty.usage().layout_steps),
                u64::from(empty.usage().resolver_work_entries),
                u64::from(empty.usage().peak_resolver_stack),
                u64::from(empty.usage().vm_steps),
                u64::from(empty.usage().peak_vm_stack)
            ],
            [0_u64; 10]
        );
        assert_eq!(empty.live_plan_nodes, 0);
        let seed = RenderUsage {
            memo_states: MemoStatesUsed::from(3_u64),
            frontier_entries: FrontierEntriesUsed::from(5_u64),
            plan_nodes_created: PlanNodesCreated::from(7_u64),
            peak_live_plan_nodes: PeakLivePlanNodes::from(2_u64),
            output_bytes: OutputBytesUsed::from(11_u64),
            layout_steps: LayoutStepsUsed::from(13_u64),
            resolver_work_entries: ResolverWorkEntriesUsed::from(17_u64),
            peak_resolver_stack: PeakResolverStack::from(3_u64),
            vm_steps: VmStepsUsed::from(19_u64),
            peak_vm_stack: PeakVmStack::from(5_u64),
        };
        {
            for (current, ceiling) in [(0_u64, 1_u64), (2, 3), (3, 3), (u64::MAX, u64::MAX)] {
                let limits = RenderLimits {
                    max_memo_states: MaxMemoStates::from(ceiling),
                    ..limits
                };
                let mut meter = RenderMeter::new(limits);
                meter.used = RenderUsage {
                    memo_states: MemoStatesUsed::from(current),
                    ..seed
                };
                meter.live_plan_nodes = 2;
                let before = meter.usage();
                let next = u128::from(current).saturating_add(1);
                let expected = if next > u128::from(u64::MAX) {
                    Err(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::StepCounter,
                    })
                }
                else if next > u128::from(ceiling) {
                    Err(RenderError::LimitExceeded {
                        kind: RenderLimitKind::MemoStates,
                        limit: LimitBound::from(ceiling),
                    })
                }
                else {
                    Ok(())
                };
                assert_eq!(meter.charge_memo_state(), expected);
                let after = if expected.is_ok() {
                    RenderUsage {
                        memo_states: MemoStatesUsed::from(
                            u64::try_from(next).expect("admitted counter"),
                        ),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
                assert_eq!(meter.live_plan_nodes, 2);
            }
        }
        {
            for (current, ceiling) in [(0_u64, 1_u64), (2, 3), (3, 3), (u64::MAX, u64::MAX)] {
                let limits = RenderLimits {
                    max_frontier_entries: MaxFrontierEntries::from(ceiling),
                    ..limits
                };
                let mut meter = RenderMeter::new(limits);
                meter.used = RenderUsage {
                    frontier_entries: FrontierEntriesUsed::from(current),
                    ..seed
                };
                meter.live_plan_nodes = 2;
                let before = meter.usage();
                let next = u128::from(current).saturating_add(1);
                let expected = if next > u128::from(u64::MAX) {
                    Err(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::StepCounter,
                    })
                }
                else if next > u128::from(ceiling) {
                    Err(RenderError::LimitExceeded {
                        kind: RenderLimitKind::FrontierEntries,
                        limit: LimitBound::from(ceiling),
                    })
                }
                else {
                    Ok(())
                };
                assert_eq!(meter.charge_frontier_entry(), expected);
                let after = if expected.is_ok() {
                    RenderUsage {
                        frontier_entries: FrontierEntriesUsed::from(
                            u64::try_from(next).expect("admitted counter"),
                        ),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
                assert_eq!(meter.live_plan_nodes, 2);
            }
        }
        {
            for (current, ceiling) in [(0_u64, 1_u64), (2, 3), (3, 3), (u64::MAX, u64::MAX)] {
                let limits = RenderLimits {
                    max_layout_steps: MaxLayoutSteps::from(ceiling),
                    ..limits
                };
                let mut meter = RenderMeter::new(limits);
                meter.used = RenderUsage {
                    layout_steps: LayoutStepsUsed::from(current),
                    ..seed
                };
                meter.live_plan_nodes = 2;
                let before = meter.usage();
                let next = u128::from(current).saturating_add(1);
                let expected = if next > u128::from(u64::MAX) {
                    Err(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::StepCounter,
                    })
                }
                else if next > u128::from(ceiling) {
                    Err(RenderError::LimitExceeded {
                        kind: RenderLimitKind::LayoutSteps,
                        limit: LimitBound::from(ceiling),
                    })
                }
                else {
                    Ok(())
                };
                assert_eq!(meter.charge_layout_step(), expected);
                let after = if expected.is_ok() {
                    RenderUsage {
                        layout_steps: LayoutStepsUsed::from(
                            u64::try_from(next).expect("admitted counter"),
                        ),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
                assert_eq!(meter.live_plan_nodes, 2);
            }
        }
        {
            for (current, ceiling) in [(0_u64, 1_u64), (2, 3), (3, 3), (u64::MAX, u64::MAX)] {
                let limits = RenderLimits {
                    max_vm_steps: MaxVmSteps::from(ceiling),
                    ..limits
                };
                let mut meter = RenderMeter::new(limits);
                meter.used = RenderUsage {
                    vm_steps: VmStepsUsed::from(current),
                    ..seed
                };
                meter.live_plan_nodes = 2;
                let before = meter.usage();
                let next = u128::from(current).saturating_add(1);
                let expected = if next > u128::from(u64::MAX) {
                    Err(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::StepCounter,
                    })
                }
                else if next > u128::from(ceiling) {
                    Err(RenderError::LimitExceeded {
                        kind: RenderLimitKind::VmSteps,
                        limit: LimitBound::from(ceiling),
                    })
                }
                else {
                    Ok(())
                };
                assert_eq!(meter.charge_vm_step(), expected);
                let after = if expected.is_ok() {
                    RenderUsage {
                        vm_steps: VmStepsUsed::from(u64::try_from(next).expect("admitted counter")),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
                assert_eq!(meter.live_plan_nodes, 2);
            }
        }
        {
            for (current, ceiling) in [(0_u64, 3_u64), (2, 5), (5, 5), (u64::MAX, u64::MAX)] {
                let limits = RenderLimits {
                    max_output_bytes: MaxOutputBytes::from(ceiling),
                    ..limits
                };
                let mut meter = RenderMeter::new(limits);
                meter.used = RenderUsage {
                    output_bytes: OutputBytesUsed::from(current),
                    ..seed
                };
                meter.live_plan_nodes = 2;
                let before = meter.usage();
                let next = u128::from(current).saturating_add(3);
                let expected = if next > u128::from(u64::MAX) {
                    Err(RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::OutputBytes,
                    })
                }
                else if next > u128::from(ceiling) {
                    Err(RenderError::LimitExceeded {
                        kind: RenderLimitKind::OutputBytes,
                        limit: LimitBound::from(ceiling),
                    })
                }
                else {
                    Ok(())
                };
                assert_eq!(meter.check_output_bytes(OutputBytes::from(3_u64)), expected);
                assert_eq!(meter.usage(), before);
                assert_eq!(
                    meter.charge_output_bytes(OutputBytes::from(3_u64)),
                    expected
                );
                let after = if expected.is_ok() {
                    RenderUsage {
                        output_bytes: OutputBytesUsed::from(
                            u64::try_from(next).expect("admitted counter"),
                        ),
                        ..before
                    }
                }
                else {
                    before
                };
                assert_eq!(meter.usage(), after);
                assert_eq!(meter.limits, limits);
                assert_eq!(meter.live_plan_nodes, 2);
            }
        }
        let mut meter = RenderMeter::new(RenderLimits {
            max_vm_stack: MaxVmStack::from(3_u64),
            ..limits
        });
        for depth in [0_u64, 1, 3, 2, 4] {
            let before = meter.usage();
            let expected = if depth > 3 {
                Err(RenderError::LimitExceeded {
                    kind: RenderLimitKind::VmStack,
                    limit: LimitBound::from(3_u64),
                })
            }
            else {
                Ok(())
            };
            assert_eq!(meter.observe_vm_stack(PeakVmStack::from(depth)), expected);
            assert_eq!(
                meter.usage(),
                if expected.is_ok() {
                    RenderUsage {
                        peak_vm_stack: PeakVmStack::from(
                            u64::from(before.peak_vm_stack).max(depth),
                        ),
                        ..before
                    }
                }
                else {
                    before
                }
            );
        }
    }

    /// Compound refusals preserve both counters and choose the documented first
    /// failure.
    #[test]
    fn compound_plan_and_work_charges_refuse_before_any_counter_changes()
    {
        let limits = RenderLimits {
            max_plan_nodes_created: MaxPlanNodesCreated::from(3_u64),
            max_live_plan_nodes: MaxLivePlanNodes::from(2_u64),
            max_resolver_work_entries: MaxResolverWorkEntries::from(3_u64),
            max_resolver_stack: MaxResolverStack::from(2_u64),
            ..RenderLimits::default()
        };
        let mut meter = RenderMeter::new(limits);
        assert_eq!(meter.charge_plan_node(), Ok(()));
        assert_eq!(meter.charge_plan_node(), Ok(()));
        let before = meter.usage();
        assert_eq!(u64::from(before.plan_nodes_created), 2);
        assert_eq!(u64::from(before.peak_live_plan_nodes), 2);
        assert_eq!(
            meter.charge_plan_node(),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::LivePlanNodes,
                limit: LimitBound::from(2_u64)
            })
        );
        assert_eq!(meter.usage(), before);
        assert_eq!(meter.live_plan_nodes, 2);
        meter.release_plan_node();
        assert_eq!(meter.usage(), before);
        assert_eq!(meter.live_plan_nodes, 1);
        assert_eq!(meter.charge_plan_node(), Ok(()));
        let before = meter.usage();
        assert_eq!(u64::from(before.plan_nodes_created), 3);
        assert_eq!(u64::from(before.peak_live_plan_nodes), 2);
        assert_eq!(
            meter.charge_plan_node(),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::PlanNodesCreated,
                limit: LimitBound::from(3_u64)
            })
        );
        assert_eq!(meter.usage(), before);
        assert_eq!(meter.live_plan_nodes, 2);
        meter.limits.max_plan_nodes_created = MaxPlanNodesCreated::from(u64::MAX);
        meter.used.plan_nodes_created = PlanNodesCreated::from(u64::MAX);
        let before = meter.usage();
        assert_eq!(
            meter.charge_plan_node(),
            Err(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::PlanRefcount
            })
        );
        assert_eq!(meter.usage(), before);
        assert_eq!(meter.live_plan_nodes, 2);
        assert_eq!(
            meter.push_resolver_work(PeakResolverStack::from(1_u64)),
            Ok(())
        );
        let before = meter.usage();
        assert_eq!(
            meter.push_resolver_work(PeakResolverStack::from(3_u64)),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::ResolverStack,
                limit: LimitBound::from(2_u64)
            })
        );
        assert_eq!(meter.usage(), before);
        assert_eq!(
            meter.push_resolver_work(PeakResolverStack::from(2_u64)),
            Ok(())
        );
        assert_eq!(
            meter.push_resolver_work(PeakResolverStack::from(1_u64)),
            Ok(())
        );
        let before = meter.usage();
        assert_eq!(u64::from(before.resolver_work_entries), 3);
        assert_eq!(u64::from(before.peak_resolver_stack), 2);
        assert_eq!(
            meter.push_resolver_work(PeakResolverStack::from(3_u64)),
            Err(RenderError::LimitExceeded {
                kind: RenderLimitKind::ResolverWorkEntries,
                limit: LimitBound::from(3_u64)
            })
        );
        assert_eq!(meter.usage(), before);
        meter.limits.max_resolver_work_entries = MaxResolverWorkEntries::from(u64::MAX);
        meter.used.resolver_work_entries = ResolverWorkEntriesUsed::from(u64::MAX);
        let before = meter.usage();
        assert_eq!(
            meter.push_resolver_work(PeakResolverStack::from(3_u64)),
            Err(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::ResolverWorkCounter
            })
        );
        assert_eq!(meter.usage(), before);
    }
}
