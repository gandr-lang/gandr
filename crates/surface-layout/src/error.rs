//! Build- and render-phase error vocabulary.
//!
//! Checked construction and finalization failures surface as the values
//! enumerated here. A failed finalization yields no partial arena; counters
//! may retain work completed before a refusal.
//!
//! The classification enums are deliberately closed. A caller switching on a
//! kind, a site, an operation, or an invariant is reading the whole space, so
//! a new failure mode is a deliberate change here rather than a silent
//! widening.
//!
//! Resolution and the render machine charge separate render counters, and a
//! build failure can never consume a render budget.

use core::fmt;

use crate::units::LimitBound;

/// Which build limit was crossed.
///
/// # Specification
/// - requires: the value names the limit whose ceiling the builder reached.
/// - ensures: the set is exactly the four build limits and never widens
///   silently.
/// - provides: the machine-readable half of a limit-exceeded build error.
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BuildLimitKind
{
    /// Stored document nodes, flatten images included.
    DocNodes,
    /// Uniquely stored text and verbatim bytes.
    TextBytes,
    /// Stored verbatim physical fragments.
    VerbatimLines,
    /// Constructor and finalization steps.
    BuildSteps,
}

/// Which store failed to grow.
///
/// Every named store checks its limit, then reserves fallibly, so an allocation
/// failure is attributable to one site rather than to the process. The flatten
/// interner is an ordered map, which offers no fallible reservation; its growth
/// is bounded by the node ceiling instead.
///
/// # Specification
/// - requires: the value names the store whose fallible reservation failed.
/// - ensures: the set is exactly the five build-phase stores.
/// - provides: the machine-readable half of an allocation-failure build error.
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BuildAllocationSite
{
    /// The document node arena.
    NodeArena,
    /// The text arena.
    TextArena,
    /// The verbatim arena.
    VerbatimArena,
    /// The flattened-image table finalization fills.
    FlattenImages,
    /// The explicit work stack finalization runs on.
    FinalizeStack,
}

/// Which checked build-phase arithmetic overflowed.
///
/// # Specification
/// - requires: the value names the operation whose checked step returned no
///   result.
/// - ensures: the set is exactly the six build-phase arithmetic sites.
/// - provides: the machine-readable half of an arithmetic-overflow build error.
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BuildArithmetic
{
    /// Incrementing the stored node count.
    NodeCount,
    /// Accumulating stored text bytes.
    TextBytes,
    /// Accumulating stored verbatim fragments.
    VerbatimLines,
    /// Incrementing the build-step counter.
    BuildSteps,
    /// Narrowing an insertion position into a dense identity.
    IdConversion,
    /// Counting the scalar width of text or of one verbatim fragment.
    ScalarWidth,
}

/// Which render limit was crossed.
///
/// # Specification
/// - requires: the value names the render counter whose ceiling was reached.
/// - ensures: every resolution budget has one closed machine-readable kind.
/// - provides: the limit classification in [`RenderError`].
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RenderLimitKind
{
    /// Number of memoized in-bound states.
    MemoStates,
    /// Number of retained frontier entries.
    FrontierEntries,
    /// Number of plan nodes ever created.
    PlanNodesCreated,
    /// Number of simultaneously live plan nodes.
    LivePlanNodes,
    /// Number of output bytes accounted for.
    OutputBytes,
    /// Number of layout transitions and comparisons.
    LayoutSteps,
    /// Number of resolver work entries pushed.
    ResolverWorkEntries,
    /// Peak resolver work-vector length.
    ResolverStack,
    /// Number of virtual-machine instructions.
    VmSteps,
    /// Peak virtual-machine stack length.
    VmStack,
}

/// Which render store or work stack failed to reserve.
///
/// The memo table is an ordered map, which offers no fallible reservation; its
/// growth is bounded by the memo-state ceiling instead.
///
/// # Specification
/// - requires: the value identifies the allocation site that refused growth.
/// - ensures: no unmetered render allocation is reported generically.
/// - provides: the allocation classification in [`RenderError`].
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `vm::tests::append_refusals_preserve_unicode_output_and_meter_state`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RenderAllocationSite
{
    /// A retained frontier.
    Frontier,
    /// The generational plan arena.
    PlanArena,
    /// The resolver's explicit work vector.
    ResolverStack,
    /// The virtual-machine stack.
    VmStack,
    /// The final output buffer.
    Output,
}

/// Which checked render arithmetic operation overflowed.
///
/// # Specification
/// - requires: the operation is the exact failed checked step.
/// - ensures: arithmetic failures remain distinguishable from limits.
/// - provides: the arithmetic classification in [`RenderError`].
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `plan::tests::reference_and_generation_ceilings_preserve_identity_boundaries`
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RenderArithmetic
{
    /// Advancing a current column.
    Column,
    /// Advancing indentation.
    Indentation,
    /// Squaring or adding overflow cost.
    SquaredOverflow,
    /// Adding a line break.
    LineBreaks,
    /// Adding output bytes.
    OutputBytes,
    /// Incrementing a cumulative render counter.
    StepCounter,
    /// Incrementing resolver work entries.
    ResolverWorkCounter,
    /// Measuring a work stack's depth after a push.
    StackDepth,
    /// Incrementing a plan reference count.
    PlanRefcount,
    /// Advancing a recycled plan slot's generation.
    PlanGeneration,
    /// Narrowing a plan slot index into a plan identity.
    PlanSlot,
}

/// Why memoized layout resolution refused.
///
/// # Specification
/// - requires: the error came from a checked render operation.
/// - ensures: resolution returns a typed failure without partial output.
/// - provides: the closed render-phase error space.
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `limits::tests::render_meter_charges_preserve_refusal_and_peak_boundaries`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Debug, Eq, PartialEq)]
pub enum RenderError
{
    /// A document handle does not belong to the supplied arena.
    UnknownDoc,
    /// The computation width is smaller than the page width.
    InvalidWidth,
    /// A checked render arithmetic operation overflowed.
    ArithmeticOverflow
    {
        /// The operation whose checked step returned no result.
        operation: RenderArithmetic,
    },
    /// A render store or work stack could not reserve capacity.
    AllocationFailed
    {
        /// The store whose reservation failed.
        site: RenderAllocationSite,
    },
    /// A named render ceiling was reached.
    LimitExceeded
    {
        /// The limit whose ceiling was reached.
        kind: RenderLimitKind,
        /// The configured ceiling.
        limit: LimitBound,
    },
    /// The resolver or the render machine found its own state inconsistent:
    /// something its own earlier steps should have supplied was missing.
    Invariant
    {
        /// The invariant that did not hold.
        invariant: RenderInvariant,
    },
}

/// Which render-phase invariant did not hold.
///
/// Each is guaranteed by the crate's own construction, so a value of this type
/// reports a defect in the engine, never a property of the caller's document;
/// it is returned rather than panicked because nothing in the crate panics.
///
/// # Specification
/// - requires: the value names the invariant a render step found broken.
/// - ensures: the set is exactly the engine's internal render invariants.
/// - provides: the machine-readable half of an invariant render error.
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `vm::tests::execution_checks_identity_order_and_byte_reconciliation`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RenderInvariant
{
    /// A plan identity was stale, foreign or already released.
    PlanIdentity,
    /// An identity stored in a sealed arena named no entry of its own store.
    DocumentIdentity,
    /// The resolver's work stack lacked the continuation a result needed.
    Continuation,
    /// A measure set offered no measure where one was needed: an empty
    /// frontier or a promise not yet forced.
    MissingMeasure,
    /// The render machine emitted a byte count other than the measured one.
    OutputReconciliation,
    /// A stored verbatim text carried no fragment record.
    VerbatimFragments,
}

/// Why document construction or finalization refused.
///
/// # Specification
/// - requires: the value is produced by a builder operation that refused.
/// - ensures: the builder is left unfinalized and no partial arena escapes.
/// - provides: the closed failure space of the build phase.
/// - panics: none.
/// - executable: none — this closed classification is a data carrier; the
///   operations returning it carry executable failure predicates.
///
/// # Adequacy
/// - hypothesis: L3 — the closed vocabulary is observed through distinct
///   diagnostics and exact payloads; the linked refusal witnesses additionally
///   exercise reachable operation boundaries. Misclassified tested refusals,
///   collapsed causes and lost bounds change these observations. Allocator
///   exhaustion and physically unattainable store sizes are not injected, so
///   causal coverage is limited to those linked boundaries.
/// - witness: `limits::tests::build_meter_charges_are_atomic_and_preflights_do_not_spend`
/// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuildError
{
    /// The process-local arena-key counter has no value left to mint.
    ArenaKeyExhausted,
    /// The dense node identity space is full.
    NodeIdExhausted,
    /// A handle came from another arena, or names no node in this one.
    UnknownDoc,
    /// Text carried a carriage return, a line feed, or a tab.
    InvalidText,
    /// Verbatim text carried a bare carriage return.
    InvalidVerbatimLineEnding,
    /// A checked build-phase arithmetic step overflowed.
    ArithmeticOverflow
    {
        /// The operation whose checked step returned no result.
        operation: BuildArithmetic,
    },
    /// A named store could not reserve the capacity it needed.
    AllocationFailed
    {
        /// The store whose fallible reservation failed.
        site: BuildAllocationSite,
    },
    /// A build limit was reached.
    LimitExceeded
    {
        /// The limit whose ceiling was reached.
        kind: BuildLimitKind,
        /// That ceiling, widened without loss.
        limit: LimitBound,
    },
}

impl fmt::Display for BuildLimitKind
{
    /// Writes the limit as the quantity it bounds.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::DocNodes => "stored document nodes",
            | Self::TextBytes => "stored text bytes",
            | Self::VerbatimLines => "stored verbatim fragments",
            | Self::BuildSteps => "build steps",
        })
    }
}

impl fmt::Display for BuildAllocationSite
{
    /// Writes the store as the arena or stack it names.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::NodeArena => "the document node arena",
            | Self::TextArena => "the text arena",
            | Self::VerbatimArena => "the verbatim arena",
            | Self::FlattenImages => "the flattened-image table",
            | Self::FinalizeStack => "the finalization work stack",
        })
    }
}

impl fmt::Display for BuildArithmetic
{
    /// Writes the operation as the quantity it advanced.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::NodeCount => "the stored node count",
            | Self::TextBytes => "the stored text bytes",
            | Self::VerbatimLines => "the stored verbatim fragments",
            | Self::BuildSteps => "the build-step count",
            | Self::IdConversion => "a dense identity narrowing",
            | Self::ScalarWidth => "a scalar width",
        })
    }
}

impl fmt::Display for RenderLimitKind
{
    /// Writes the limit as the quantity it bounds.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::MemoStates => "memoized states",
            | Self::FrontierEntries => "frontier entries",
            | Self::PlanNodesCreated => "plan nodes created",
            | Self::LivePlanNodes => "live plan nodes",
            | Self::OutputBytes => "output bytes",
            | Self::LayoutSteps => "layout steps",
            | Self::ResolverWorkEntries => "resolver work entries",
            | Self::ResolverStack => "the resolver stack depth",
            | Self::VmSteps => "render machine steps",
            | Self::VmStack => "the render machine stack depth",
        })
    }
}

impl fmt::Display for RenderAllocationSite
{
    /// Writes the store as the table or stack it names.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Frontier => "a frontier",
            | Self::PlanArena => "the plan arena",
            | Self::ResolverStack => "the resolver work stack",
            | Self::VmStack => "the render machine stack",
            | Self::Output => "the output buffer",
        })
    }
}

impl fmt::Display for RenderArithmetic
{
    /// Writes the operation as the quantity it advanced.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Column => "the current column",
            | Self::Indentation => "the indentation",
            | Self::SquaredOverflow => "the squared overflow cost",
            | Self::LineBreaks => "the line-break count",
            | Self::OutputBytes => "the output byte count",
            | Self::StepCounter => "a cumulative render counter",
            | Self::ResolverWorkCounter => "the resolver work count",
            | Self::StackDepth => "a work stack depth",
            | Self::PlanRefcount => "a plan reference count",
            | Self::PlanGeneration => "a plan slot generation",
            | Self::PlanSlot => "a plan slot index",
        })
    }
}

impl fmt::Display for RenderInvariant
{
    /// Writes the invariant as the property that failed.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: each named classification has a distinct descriptive
    ///   diagnostic.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::PlanIdentity => "a plan identity was not live",
            | Self::DocumentIdentity => "a sealed document identity named nothing",
            | Self::Continuation => "the resolver's work stack lacked a continuation",
            | Self::MissingMeasure => "a measure set offered no measure",
            | Self::OutputReconciliation => {
                "the rendered byte count differed from the measured one"
            },
            | Self::VerbatimFragments => "a stored verbatim text carried no fragment record",
        })
    }
}

impl fmt::Display for RenderError
{
    /// Writes the failure as one sentence naming what refused.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: the diagnostic identifies the cause and preserves every
    ///   numeric ceiling; distinct causes remain distinguishable.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::UnknownDoc => {
                f.write_str("the document handle does not belong to this layout arena")
            },
            | Self::InvalidWidth => {
                f.write_str("the computation width must be at least the page width")
            },
            | Self::ArithmeticOverflow { operation } => {
                write!(
                    f,
                    "a checked layout render computation overflowed: {operation}"
                )
            },
            | Self::AllocationFailed { site } => {
                write!(
                    f,
                    "a layout render store could not reserve capacity: {site}"
                )
            },
            | Self::LimitExceeded { kind, limit } => {
                write!(f, "a layout render limit was reached: {kind} at {limit}")
            },
            | Self::Invariant { invariant } => {
                write!(f, "a layout engine invariant did not hold: {invariant}")
            },
        }
    }
}

impl core::error::Error for RenderError
{
}

impl fmt::Display for BuildError
{
    /// Writes the failure as one sentence naming what refused.
    ///
    /// # Specification
    /// - requires: the caller supplies a formatter, including sinks that refuse
    ///   writes.
    /// - ensures: the diagnostic identifies the cause and preserves every
    ///   numeric ceiling; distinct causes remain distinguishable.
    /// - provides: human-readable failure information without fixing its
    ///   wording.
    /// - fails: propagates the formatter sink refusal.
    /// - panics: none.
    /// - executable: none — Formatter has a write-only sink and exposes neither
    ///   emitted bytes nor its refusal state; observing those effects here
    ///   would require wrapping or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every named cause and ceilings at zero, one and the
    ///   integer maximum expose distinct diagnostics and exact numeric
    ///   payloads. A real exhausted output sink must retain its I/O refusal.
    ///   Collapsed causes, truncated bounds or swallowed writes change these
    ///   observations; wording and field position are not pinned.
    /// - witness: `error::tests::diagnostics_preserve_distinct_causes_bounds_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::ArenaKeyExhausted => f.write_str("the layout arena key counter is exhausted"),
            | Self::NodeIdExhausted => {
                f.write_str("the layout document node identity space is exhausted")
            },
            | Self::UnknownDoc => {
                f.write_str("the document handle does not belong to this layout arena")
            },
            | Self::InvalidText => {
                f.write_str("layout text must not contain a carriage return, a line feed, or a tab")
            },
            | Self::InvalidVerbatimLineEnding => {
                f.write_str("verbatim text must not contain a bare carriage return")
            },
            | Self::ArithmeticOverflow { operation } => {
                write!(
                    f,
                    "a checked layout build computation overflowed: {operation}"
                )
            },
            | Self::AllocationFailed { site } => {
                write!(f, "a layout build store could not reserve capacity: {site}")
            },
            | Self::LimitExceeded { kind, limit } => {
                write!(f, "a layout build limit was reached: {kind} at {limit}")
            },
        }
    }
}

impl core::error::Error for BuildError
{
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;

    use super::*;

    /// Diagnostics distinguish causes, retain full bounds and do not hide a
    /// real sink refusal.
    #[test]
    fn diagnostics_preserve_distinct_causes_bounds_and_sink_failures()
    {
        let mut build = alloc::vec![
            BuildError::ArenaKeyExhausted,
            BuildError::NodeIdExhausted,
            BuildError::UnknownDoc,
            BuildError::InvalidText,
            BuildError::InvalidVerbatimLineEnding
        ];
        for operation in [
            BuildArithmetic::NodeCount,
            BuildArithmetic::TextBytes,
            BuildArithmetic::VerbatimLines,
            BuildArithmetic::BuildSteps,
            BuildArithmetic::IdConversion,
            BuildArithmetic::ScalarWidth,
        ] {
            build.push(BuildError::ArithmeticOverflow { operation });
        }
        for site in [
            BuildAllocationSite::NodeArena,
            BuildAllocationSite::TextArena,
            BuildAllocationSite::VerbatimArena,
            BuildAllocationSite::FlattenImages,
            BuildAllocationSite::FinalizeStack,
        ] {
            build.push(BuildError::AllocationFailed { site });
        }
        for kind in [
            BuildLimitKind::DocNodes,
            BuildLimitKind::TextBytes,
            BuildLimitKind::VerbatimLines,
            BuildLimitKind::BuildSteps,
        ] {
            for limit in [0_u64, 1, u64::MAX] {
                build.push(BuildError::LimitExceeded {
                    kind,
                    limit: LimitBound::from(limit),
                });
            }
        }
        let direct = std::io::Write::write_all(&mut [0_u8; 0].as_mut_slice(), b"x")
            .expect_err("exhausted sink");
        let mut messages = alloc::collections::BTreeSet::new();
        for error in build {
            let message = error.to_string();
            if let BuildError::LimitExceeded { limit, .. } = error {
                assert!(message.contains(&u64::from(limit).to_string()));
            }
            let mut storage = [0_u8; 1];
            let refusal =
                std::io::Write::write_fmt(&mut storage.as_mut_slice(), format_args!("{error}"))
                    .expect_err("diagnostic sink must refuse");
            assert_eq!(refusal.kind(), direct.kind());
            assert!(
                messages.insert(message),
                "distinct build causes and bounds must not collapse"
            );
        }
        let mut render = alloc::vec![RenderError::UnknownDoc, RenderError::InvalidWidth];
        for operation in [
            RenderArithmetic::Column,
            RenderArithmetic::Indentation,
            RenderArithmetic::SquaredOverflow,
            RenderArithmetic::LineBreaks,
            RenderArithmetic::OutputBytes,
            RenderArithmetic::StepCounter,
            RenderArithmetic::ResolverWorkCounter,
            RenderArithmetic::StackDepth,
            RenderArithmetic::PlanRefcount,
            RenderArithmetic::PlanGeneration,
            RenderArithmetic::PlanSlot,
        ] {
            render.push(RenderError::ArithmeticOverflow { operation });
        }
        for site in [
            RenderAllocationSite::Frontier,
            RenderAllocationSite::PlanArena,
            RenderAllocationSite::ResolverStack,
            RenderAllocationSite::VmStack,
            RenderAllocationSite::Output,
        ] {
            render.push(RenderError::AllocationFailed { site });
        }
        for invariant in [
            RenderInvariant::PlanIdentity,
            RenderInvariant::DocumentIdentity,
            RenderInvariant::Continuation,
            RenderInvariant::MissingMeasure,
            RenderInvariant::OutputReconciliation,
            RenderInvariant::VerbatimFragments,
        ] {
            render.push(RenderError::Invariant { invariant });
        }
        for kind in [
            RenderLimitKind::MemoStates,
            RenderLimitKind::FrontierEntries,
            RenderLimitKind::PlanNodesCreated,
            RenderLimitKind::LivePlanNodes,
            RenderLimitKind::OutputBytes,
            RenderLimitKind::LayoutSteps,
            RenderLimitKind::ResolverWorkEntries,
            RenderLimitKind::ResolverStack,
            RenderLimitKind::VmSteps,
            RenderLimitKind::VmStack,
        ] {
            for limit in [0_u64, 1, u64::MAX] {
                render.push(RenderError::LimitExceeded {
                    kind,
                    limit: LimitBound::from(limit),
                });
            }
        }
        let mut messages = alloc::collections::BTreeSet::new();
        for error in render {
            let message = error.to_string();
            if let RenderError::LimitExceeded { limit, .. } = error {
                assert!(message.contains(&u64::from(limit).to_string()));
            }
            let mut storage = [0_u8; 1];
            let refusal =
                std::io::Write::write_fmt(&mut storage.as_mut_slice(), format_args!("{error}"))
                    .expect_err("diagnostic sink must refuse");
            assert_eq!(refusal.kind(), direct.kind());
            assert!(
                messages.insert(message),
                "distinct render causes and bounds must not collapse"
            );
        }
    }
}
