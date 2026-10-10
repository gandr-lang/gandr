//! Nominal scalar types for the layout engine.
//!
//! Every quantity the engine carries has a name. A width is not an index, an
//! indentation is not a column, and a byte budget is not a node budget, so none
//! of them is spelled as a bare integer anywhere a caller can see it. The
//! wrappers are the API boundary rather than a convenience alias: each is
//! `#[repr(transparent)]`, each has a checked constructor or an exact external
//! conversion, and none exposes an inherent accessor that hands the primitive
//! back.
//!
//! A widening conversion is a `From`, a narrowing one is a `TryFrom` whose
//! error is the owning crate error, and neither is an inherent method.

use crate::error::BuildArithmetic;
use crate::error::BuildError;
use crate::error::BuildLimitKind;

/// A count of Unicode scalar values occupying one line of output.
///
/// Width in this engine is scalar count rather than display cell count. A
/// client that owns its tabs expands them before construction; a tab preserved
/// inside verbatim text counts as one scalar and is never rewritten. Moving to
/// display cells later is one change here rather than two estimators.
///
/// # Specification
/// - requires: the value is a scalar count already checked against overflow.
/// - ensures: ordering agrees with the ordering of the underlying counts.
/// - provides: the one width currency the measure, cost, and taint rules read.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, the u32 ceiling and the platform maximum are
///   compared through the narrowing result; truncation, saturation and a
///   shifted accepted boundary change the count or refusal.
/// - witness: `units::tests::platform_counts_narrow_without_loss`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ScalarWidth
{
    /// The scalar count.
    width: u32,
}

/// The additional indentation a `Nest` node applies to its child.
///
/// # Specification
/// - requires: the value is the amount written at the construction site.
/// - ensures: addition against a current indentation is checked by the caller.
/// - provides: the argument type of the builder's nesting constructor.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — nested indentation and the u32 overflow boundary are
///   observed through emitted spaces and the typed indentation refusal;
///   wrapping, lost nesting and confusion between indentation and incoming
///   column change output or error.
/// - witness: `algebra::tests::nest_raises_indentation_by_a_checked_amount`
/// - witness: `algebra::tests::nest_reports_overflow_rather_than_wrapping_the_indentation`
/// - witness: `algebra::tests::align_sets_indentation_to_the_current_column`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct NestAmount
{
    /// The indentation increment.
    amount: u32,
}

/// The ceiling on stored document nodes, flatten images included.
///
/// # Specification
/// - requires: the value is the caller's chosen ceiling.
/// - ensures: the builder refuses to store a node once the count reaches it.
/// - provides: one field of the build limit record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxDocNodes
{
    /// The node count.
    nodes: u32,
}

/// The ceiling on uniquely stored text and verbatim bytes.
///
/// # Specification
/// - requires: the value is the caller's chosen ceiling.
/// - ensures: the builder refuses to store text once the byte count reaches it.
/// - provides: one field of the build limit record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxTextBytes
{
    /// The byte count.
    bytes: usize,
}

/// The ceiling on stored verbatim physical fragments.
///
/// # Specification
/// - requires: the value is the caller's chosen ceiling.
/// - ensures: the builder refuses a verbatim node whose scan would cross it.
/// - provides: one field of the build limit record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxVerbatimLines
{
    /// The fragment count.
    lines: u32,
}

/// The ceiling on constructor and finalization steps.
///
/// A step is one checked input edge, one interner probe, one visit, or one
/// flatten edge. It is the budget that bounds work rather than storage.
///
/// # Specification
/// - requires: the value is the caller's chosen ceiling.
/// - ensures: construction and finalization refuse once the count reaches it.
/// - provides: one field of the build limit record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxBuildSteps
{
    /// The step count.
    steps: u64,
}

/// Document nodes stored so far, flatten images included.
///
/// # Specification
/// - requires: the counter is owned by exactly one build meter.
/// - ensures: the count is monotone for the meter's whole lifetime.
/// - provides: one field of the build usage record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct DocNodesUsed
{
    /// The node count.
    nodes: u64,
}

/// Uniquely stored text and verbatim bytes so far.
///
/// # Specification
/// - requires: the counter is owned by exactly one build meter.
/// - ensures: a second edge to an existing identity adds nothing to it.
/// - provides: the byte count of stored text and verbatim content.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct TextBytesUsed
{
    /// The byte count.
    bytes: u64,
}

/// Stored verbatim physical fragments so far.
///
/// # Specification
/// - requires: the counter is owned by exactly one build meter.
/// - ensures: the count is monotone for the meter's whole lifetime.
/// - provides: one field of the build usage record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct VerbatimLinesUsed
{
    /// The fragment count.
    lines: u64,
}

/// Constructor and finalization steps consumed so far.
///
/// # Specification
/// - requires: the counter is owned by exactly one build meter.
/// - ensures: the count is monotone for the meter's whole lifetime.
/// - provides: one field of the build usage record.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BuildStepsUsed
{
    /// The step count.
    steps: u64,
}

/// The numeric ceiling reported beside an exceeded limit.
///
/// One widened currency keeps the error's shape independent of which limit was
/// crossed, so a caller reads the kind for meaning and this for the number.
///
/// # Specification
/// - requires: the value is the limit that was crossed, widened without loss.
/// - ensures: the widening is exact for every limit currency in the crate.
/// - provides: the numeric payload of a limit-exceeded error.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero, exact ceilings, the first excess and counter
///   overflow are observed through exact usage and typed refusal payloads.
///   Wrong increments, wrong limit kinds, off-by-one ceilings and
///   arithmetic/limit precedence change these observations; shared identities
///   must not be charged twice.
/// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
/// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
/// - witness: `algebra::tests::a_second_edge_to_a_shared_handle_charges_no_new_text_bytes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct LimitBound
{
    /// The widened ceiling.
    bound: u64,
}

impl core::fmt::Display for LimitBound
{
    /// Writes the ceiling as its decimal value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "{}", self.bound)
    }
}

/// The requested page width used by the cost ordering.
///
/// # Specification
/// - requires: the value is a scalar column ceiling.
/// - ensures: the width remains distinct from computation and indentation.
/// - provides: the public page-width currency.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — equal and reversed widths, zero and u32 maximum expose
///   the option ordering through accepted fields or `InvalidWidth`; swapping
///   the currencies or accepting the reversed boundary changes the result.
/// - witness: `measure::tests::width_options_preserve_policy_and_reject_reversal`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PageWidth(u32);

/// The width within which the optimality theorem is computed.
///
/// # Specification
/// - requires: the value is at least the page width for valid options.
/// - ensures: in-bound resolver contexts are representable.
/// - provides: the public computation-width currency.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — equal and reversed widths, zero and u32 maximum expose
///   the option ordering through accepted fields or `InvalidWidth`; swapping
///   the currencies or accepting the reversed boundary changes the result.
/// - witness: `measure::tests::width_options_preserve_policy_and_reject_reversal`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ComputationWidth(u32);

/// A current output column.
///
/// # Specification
/// - requires: the value is a checked scalar column.
/// - ensures: column arithmetic remains nominal inside resolution.
/// - provides: the resolver's column currency.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — nested indentation and the u32 overflow boundary are
///   observed through emitted spaces and the typed indentation refusal;
///   wrapping, lost nesting and confusion between indentation and incoming
///   column change output or error.
/// - witness: `algebra::tests::nest_raises_indentation_by_a_checked_amount`
/// - witness: `algebra::tests::nest_reports_overflow_rather_than_wrapping_the_indentation`
/// - witness: `algebra::tests::align_sets_indentation_to_the_current_column`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct Column(u32);

/// An indentation column.
///
/// # Specification
/// - requires: the value is a checked indentation.
/// - ensures: indentation cannot be confused with a page width.
/// - provides: the resolver's indentation currency.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — nested indentation and the u32 overflow boundary are
///   observed through emitted spaces and the typed indentation refusal;
///   wrapping, lost nesting and confusion between indentation and incoming
///   column change output or error.
/// - witness: `algebra::tests::nest_raises_indentation_by_a_checked_amount`
/// - witness: `algebra::tests::nest_reports_overflow_rather_than_wrapping_the_indentation`
/// - witness: `algebra::tests::align_sets_indentation_to_the_current_column`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct Indentation(u32);

/// Squared overflow accumulated by a layout.
///
/// # Specification
/// - requires: each increment was checked before addition.
/// - ensures: ordering is the lexicographic cost's first component.
/// - provides: the public overflow currency.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero and overflowing sums expose exact cost components,
///   output-byte counts and distinct arithmetic errors. Reversing cost
///   priority, wrapping, or confusing breaks with bytes changes the selected
///   cost or refusal.
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct SquaredOverflow(u64);

/// Layout-owned physical line breaks.
///
/// # Specification
/// - requires: every counted ending was emitted by a layout node.
/// - ensures: the count is cumulative and checked.
/// - provides: the public line-break cost component.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero and overflowing sums expose exact cost components,
///   output-byte counts and distinct arithmetic errors. Reversing cost
///   priority, wrapping, or confusing breaks with bytes changes the selected
///   cost or refusal.
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct LineBreaks(u64);

/// Exact output bytes associated with a resolved plan.
///
/// # Specification
/// - requires: bytes were counted from stored text and endings.
/// - ensures: the count is checked before it is retained.
/// - provides: the public output-size projection.
/// - panics: none.
/// - executable: none — this quantity is a data carrier; consuming arithmetic
///   and meter operations, rather than the declaration, carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 — zero and overflowing sums expose exact cost components,
///   output-byte counts and distinct arithmetic errors. Reversing cost
///   priority, wrapping, or confusing breaks with bytes changes the selected
///   cost or refusal.
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct OutputBytes(u64);

/// A cumulative memo-state ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxMemoStates(u64);

/// A cumulative frontier-entry ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxFrontierEntries(u64);

/// A cumulative plan-allocation ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxPlanNodesCreated(u64);

/// A simultaneous live-plan ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxLivePlanNodes(u64);

/// A cumulative output-byte ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxOutputBytes(u64);

/// A cumulative layout-step ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxLayoutSteps(u64);

/// A cumulative resolver-work-entry ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxResolverWorkEntries(u64);

/// A simultaneous resolver-stack ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxResolverStack(u64);

/// A cumulative virtual-machine-step ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxVmSteps(u64);

/// A simultaneous virtual-machine-stack ceiling.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MaxVmStack(u64);

/// Cumulative memo states used by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct MemoStatesUsed(u64);

/// Cumulative frontier entries used by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct FrontierEntriesUsed(u64);

/// Cumulative plan nodes created by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PlanNodesCreated(u64);

/// Peak live plan nodes observed by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PeakLivePlanNodes(u64);

/// Cumulative output bytes used by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct OutputBytesUsed(u64);

/// Cumulative layout steps used by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct LayoutStepsUsed(u64);

/// Cumulative resolver work entries used by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ResolverWorkEntriesUsed(u64);

/// Peak resolver stack observed by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PeakResolverStack(u64);

/// Cumulative virtual-machine steps used by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct VmStepsUsed(u64);

/// Peak virtual-machine stack observed by a render meter.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PeakVmStack(u64);

/// Implements exact `u32` conversions for a transparent currency.
macro_rules! u32_currency {
    ($name:ty) => {
        impl From<u32> for $name
        {
            /// Reads the primitive as this quantity.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: u32) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for u32
        {
            /// Reads the quantity back out as its primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

/// Implements exact `u64` conversions for a transparent currency.
macro_rules! u64_currency {
    ($name:ty) => {
        impl From<u64> for $name
        {
            /// Reads the primitive as this quantity.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: u64) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for u64
        {
            /// Reads the quantity back out as its primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

u32_currency!(PageWidth);
u32_currency!(ComputationWidth);
u32_currency!(Column);
u32_currency!(Indentation);
u64_currency!(SquaredOverflow);
u64_currency!(LineBreaks);
u64_currency!(OutputBytes);
u64_currency!(MaxMemoStates);
u64_currency!(MaxFrontierEntries);
u64_currency!(MaxPlanNodesCreated);
u64_currency!(MaxLivePlanNodes);
u64_currency!(MaxOutputBytes);
u64_currency!(MaxLayoutSteps);
u64_currency!(MaxResolverWorkEntries);
u64_currency!(MaxResolverStack);
u64_currency!(MaxVmSteps);
u64_currency!(MaxVmStack);
u64_currency!(MemoStatesUsed);
u64_currency!(FrontierEntriesUsed);
u64_currency!(PlanNodesCreated);
u64_currency!(PeakLivePlanNodes);
u64_currency!(OutputBytesUsed);
u64_currency!(LayoutStepsUsed);
u64_currency!(ResolverWorkEntriesUsed);
u64_currency!(PeakResolverStack);
u64_currency!(VmStepsUsed);
u64_currency!(PeakVmStack);

impl From<ScalarWidth> for Column
{
    /// Reads a scalar width as the column it advances to from column zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(width: ScalarWidth) -> Self
    {
        Self(u32::from(width))
    }
}

impl From<NestAmount> for Indentation
{
    /// Reads a nesting amount as the indentation it adds from zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(amount: NestAmount) -> Self
    {
        Self(u32::from(amount))
    }
}

impl From<u32> for NestAmount
{
    /// Reads the primitive as a nesting amount.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(amount: u32) -> Self
    {
        Self { amount }
    }
}

impl From<u32> for ScalarWidth
{
    /// Reads the primitive as a scalar width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(width: u32) -> Self
    {
        Self { width }
    }
}

impl TryFrom<usize> for ScalarWidth
{
    type Error = BuildError;

    /// Converts a platform width into the checked scalar-width currency.
    ///
    /// # Specification
    /// - requires: `width` is the source scalar count.
    /// - ensures: success preserves the count exactly.
    /// - provides: the narrowing conversion used by text ingestion.
    /// - fails: returns `ArithmeticOverflow` when the count exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for an unrepresentable scalar count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one, the u32 ceiling and the platform maximum
    ///   are observed as exact counts or the owning arithmetic refusal.
    ///   Truncation, saturation and a shifted narrowing boundary change the
    ///   result. The u64 refusal is unreachable on supported platforms with at
    ///   most 64-bit usize.
    /// - witness: `units::tests::platform_counts_narrow_without_loss`
    #[anodized::spec(
        ensures: |ret| match (ret.as_ref(), u32::try_from(width)) { (Ok(value), Ok(expected)) => value.width == expected, (Err(error), Err(_)) => *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth }, _ => false }
    )]
    #[inline]
    fn try_from(width: usize) -> Result<Self, Self::Error>
    {
        let Ok(width) = u32::try_from(width)
        else {
            return Err(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::ScalarWidth,
            });
        };
        Ok(Self { width })
    }
}

impl From<u32> for MaxDocNodes
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: u32) -> Self
    {
        Self { nodes }
    }
}

impl From<usize> for MaxTextBytes
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: usize) -> Self
    {
        Self { bytes }
    }
}

impl From<u32> for MaxVerbatimLines
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lines: u32) -> Self
    {
        Self { lines }
    }
}

impl From<u64> for MaxBuildSteps
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: u64) -> Self
    {
        Self { steps }
    }
}

impl From<ScalarWidth> for LimitBound
{
    /// Reads a scalar width as the bound a refusal names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(width: ScalarWidth) -> Self
    {
        Self {
            bound: u64::from(width.width),
        }
    }
}

impl From<NestAmount> for ScalarWidth
{
    /// Reads a nesting amount as the width of the spaces it emits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(amount: NestAmount) -> Self
    {
        Self {
            width: amount.amount,
        }
    }
}
impl From<NestAmount> for u32
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(amount: NestAmount) -> Self
    {
        amount.amount
    }
}

impl From<ScalarWidth> for u32
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(width: ScalarWidth) -> Self
    {
        width.width
    }
}

impl From<MaxDocNodes> for u32
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: MaxDocNodes) -> Self
    {
        nodes.nodes
    }
}

impl From<MaxTextBytes> for usize
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: MaxTextBytes) -> Self
    {
        bytes.bytes
    }
}

impl From<MaxVerbatimLines> for u32
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lines: MaxVerbatimLines) -> Self
    {
        lines.lines
    }
}

impl From<MaxBuildSteps> for u64
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: MaxBuildSteps) -> Self
    {
        steps.steps
    }
}

impl From<DocNodesUsed> for u64
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: DocNodesUsed) -> Self
    {
        nodes.nodes
    }
}

impl From<TextBytesUsed> for u64
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: TextBytesUsed) -> Self
    {
        bytes.bytes
    }
}

impl From<VerbatimLinesUsed> for u64
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lines: VerbatimLinesUsed) -> Self
    {
        lines.lines
    }
}

impl From<BuildStepsUsed> for u64
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: BuildStepsUsed) -> Self
    {
        steps.steps
    }
}

impl From<u64> for LimitBound
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bound: u64) -> Self
    {
        Self { bound }
    }
}

impl From<LimitBound> for u64
{
    /// Reads the quantity back out as its primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bound: LimitBound) -> Self
    {
        bound.bound
    }
}
impl From<u64> for DocNodesUsed
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: u64) -> Self
    {
        Self { nodes }
    }
}

impl From<u64> for TextBytesUsed
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: u64) -> Self
    {
        Self { bytes }
    }
}

impl From<u64> for VerbatimLinesUsed
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lines: u64) -> Self
    {
        Self { lines }
    }
}

impl From<u64> for BuildStepsUsed
{
    /// Reads the primitive as this quantity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(steps: u64) -> Self
    {
        Self { steps }
    }
}
impl TryFrom<usize> for TextBytesUsed
{
    type Error = BuildError;

    /// Converts a platform byte count into nominal text-byte usage.
    ///
    /// # Specification
    /// - requires: `bytes` is the complete stored-byte count.
    /// - ensures: success preserves the count exactly.
    /// - provides: the usage currency for text-byte accounting.
    /// - fails: returns `ArithmeticOverflow` when the count is not
    ///   representable.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for an unrepresentable byte count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one, the u32 ceiling and the platform maximum
    ///   are observed as exact counts or the owning arithmetic refusal.
    ///   Truncation, saturation and a shifted narrowing boundary change the
    ///   result. The u64 refusal is unreachable on supported platforms with at
    ///   most 64-bit usize.
    /// - witness: `units::tests::platform_counts_narrow_without_loss`
    #[anodized::spec(
        ensures: |ret| match (ret.as_ref(), u64::try_from(bytes)) { (Ok(value), Ok(expected)) => value.bytes == expected, (Err(error), Err(_)) => *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::TextBytes }, _ => false }
    )]
    #[inline]
    fn try_from(bytes: usize) -> Result<Self, Self::Error>
    {
        let bytes = u64::try_from(bytes).map_err(|_error| BuildError::ArithmeticOverflow {
            operation: BuildArithmetic::TextBytes,
        })?;
        Ok(Self { bytes })
    }
}

impl TryFrom<usize> for VerbatimLinesUsed
{
    type Error = BuildError;

    /// Converts a platform fragment count into nominal verbatim-line usage.
    ///
    /// # Specification
    /// - requires: `lines` is the complete scan count for one verbatim value.
    /// - ensures: success preserves the count exactly.
    /// - provides: the usage currency for physical-fragment accounting.
    /// - fails: returns `ArithmeticOverflow` when the count is not
    ///   representable.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for an unrepresentable fragment count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one, the u32 ceiling and the platform maximum
    ///   are observed as exact counts or the owning arithmetic refusal.
    ///   Truncation, saturation and a shifted narrowing boundary change the
    ///   result. The u64 refusal is unreachable on supported platforms with at
    ///   most 64-bit usize.
    /// - witness: `units::tests::platform_counts_narrow_without_loss`
    #[anodized::spec(
        ensures: |ret| match (ret.as_ref(), u64::try_from(lines)) { (Ok(value), Ok(expected)) => value.lines == expected, (Err(error), Err(_)) => *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::VerbatimLines }, _ => false }
    )]
    #[inline]
    fn try_from(lines: usize) -> Result<Self, Self::Error>
    {
        let lines = u64::try_from(lines).map_err(|_error| BuildError::ArithmeticOverflow {
            operation: BuildArithmetic::VerbatimLines,
        })?;
        Ok(Self { lines })
    }
}
impl DocNodesUsed
{
    /// Charges one node against the nominal node ceiling.
    ///
    /// # Specification
    /// - requires: the current node count is charged against `limit`.
    /// - ensures: success increments usage exactly once.
    /// - provides: node accounting for original and flattened images.
    /// - fails: returns `ArithmeticOverflow` or `LimitExceeded` without
    ///   changing the current usage.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for counter overflow or `LimitExceeded` at
    /// the configured node ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero charges, the last admitted unit, the first
    ///   refused unit and u64 overflow are observed as exact counts or typed
    ///   errors. Changing addition, the inclusive ceiling, refusal kind or
    ///   arithmetic-before-limit precedence changes these observations; public
    ///   shared-document witnesses cover lifetime accounting.
    /// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    #[anodized::spec(
        ensures: |ret| { let next = u128::from(self.nodes).saturating_add(u128::from(1_u64));
            let ceiling = Some(u64::from(limit.nodes));
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::NodeCount } }
            else { ceiling.is_some_and(|ceiling| next > u128::from(ceiling)
                && *error == BuildError::LimitExceeded { kind: BuildLimitKind::DocNodes, limit: LimitBound::from(ceiling) }) } },
            |charged| next == u128::from(charged.nodes)
                && ceiling.is_some_and(|ceiling| charged.nodes <= ceiling)) }
    )]
    #[inline]
    pub(crate) fn checked_charge(
        self,
        limit: MaxDocNodes,
    ) -> Result<Self, BuildError>
    {
        let next = self
            .nodes
            .checked_add(1u64)
            .ok_or(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::NodeCount,
            })?;
        if next > u64::from(limit.nodes) {
            return Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::DocNodes,
                limit: LimitBound::from(u64::from(limit.nodes)),
            });
        }
        Ok(Self { nodes: next })
    }
}

impl TextBytesUsed
{
    /// Charges nominal new bytes against the text-byte ceiling.
    ///
    /// # Specification
    /// - requires: `amount` is the new stored-byte count.
    /// - ensures: success increments usage exactly by `amount`.
    /// - provides: text-byte accounting for unique identities.
    /// - fails: returns `ArithmeticOverflow` or `LimitExceeded` without
    ///   changing the current usage.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for counter or limit conversion overflow,
    /// or `LimitExceeded` at the configured byte ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero charges, the last admitted unit, the first
    ///   refused unit and u64 overflow are observed as exact counts or typed
    ///   errors. Changing addition, the inclusive ceiling, refusal kind or
    ///   arithmetic-before-limit precedence changes these observations; public
    ///   shared-document witnesses cover lifetime accounting.
    /// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    #[anodized::spec(
        ensures: |ret| { let next = u128::from(self.bytes).saturating_add(u128::from(amount.bytes));
            let ceiling = u64::try_from(limit.bytes).ok();
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::TextBytes } }
            else { ceiling.is_some_and(|ceiling| next > u128::from(ceiling)
                && *error == BuildError::LimitExceeded { kind: BuildLimitKind::TextBytes, limit: LimitBound::from(ceiling) }) } },
            |charged| next == u128::from(charged.bytes)
                && ceiling.is_some_and(|ceiling| charged.bytes <= ceiling)) }
    )]
    #[inline]
    pub(crate) fn checked_charge(
        self,
        amount: Self,
        limit: MaxTextBytes,
    ) -> Result<Self, BuildError>
    {
        let next = self
            .bytes
            .checked_add(amount.bytes)
            .ok_or(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::TextBytes,
            })?;
        let limit =
            u64::try_from(limit.bytes).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::TextBytes,
            })?;
        if next > limit {
            return Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::TextBytes,
                limit: LimitBound::from(limit),
            });
        }
        Ok(Self { bytes: next })
    }
}

impl VerbatimLinesUsed
{
    /// Charges nominal new fragments against the verbatim-line ceiling.
    ///
    /// # Specification
    /// - requires: `amount` is the complete new physical-fragment count.
    /// - ensures: success increments usage exactly by `amount`.
    /// - provides: verbatim-line accounting for opaque content.
    /// - fails: returns `ArithmeticOverflow` or `LimitExceeded` without
    ///   changing the current usage.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for counter overflow or `LimitExceeded` at
    /// the configured fragment ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero charges, the last admitted unit, the first
    ///   refused unit and u64 overflow are observed as exact counts or typed
    ///   errors. Changing addition, the inclusive ceiling, refusal kind or
    ///   arithmetic-before-limit precedence changes these observations; public
    ///   shared-document witnesses cover lifetime accounting.
    /// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    #[anodized::spec(
        ensures: |ret| { let next = u128::from(self.lines).saturating_add(u128::from(amount.lines));
            let ceiling = Some(u64::from(limit.lines));
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::VerbatimLines } }
            else { ceiling.is_some_and(|ceiling| next > u128::from(ceiling)
                && *error == BuildError::LimitExceeded { kind: BuildLimitKind::VerbatimLines, limit: LimitBound::from(ceiling) }) } },
            |charged| next == u128::from(charged.lines)
                && ceiling.is_some_and(|ceiling| charged.lines <= ceiling)) }
    )]
    #[inline]
    pub(crate) fn checked_charge(
        self,
        amount: Self,
        limit: MaxVerbatimLines,
    ) -> Result<Self, BuildError>
    {
        let next = self
            .lines
            .checked_add(amount.lines)
            .ok_or(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::VerbatimLines,
            })?;
        if next > u64::from(limit.lines) {
            return Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::VerbatimLines,
                limit: LimitBound::from(u64::from(limit.lines)),
            });
        }
        Ok(Self { lines: next })
    }
}

impl BuildStepsUsed
{
    /// Charges one nominal build step against the step ceiling.
    ///
    /// # Specification
    /// - requires: the caller has identified one checked operation.
    /// - ensures: success increments usage exactly once.
    /// - provides: the work budget for construction and finalization.
    /// - fails: returns `ArithmeticOverflow` or `LimitExceeded` without
    ///   changing the current usage.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` for counter overflow or `LimitExceeded` at
    /// the configured step ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero charges, the last admitted unit, the first
    ///   refused unit and u64 overflow are observed as exact counts or typed
    ///   errors. Changing addition, the inclusive ceiling, refusal kind or
    ///   arithmetic-before-limit precedence changes these observations; public
    ///   shared-document witnesses cover lifetime accounting.
    /// - witness: `units::tests::checked_charges_preserve_exact_boundaries_and_error_precedence`
    /// - witness: `algebra::tests::each_build_ceiling_refuses_exactly_at_its_boundary`
    #[anodized::spec(
        ensures: |ret| { let next = u128::from(self.steps).saturating_add(u128::from(1_u64));
            let ceiling = Some(limit.steps);
            ret.as_ref().map_or_else(|error| { if next > u128::from(u64::MAX) || ceiling.is_none() { *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::BuildSteps } }
            else { ceiling.is_some_and(|ceiling| next > u128::from(ceiling)
                && *error == BuildError::LimitExceeded { kind: BuildLimitKind::BuildSteps, limit: LimitBound::from(ceiling) }) } },
            |charged| next == u128::from(charged.steps)
                && ceiling.is_some_and(|ceiling| charged.steps <= ceiling)) }
    )]
    #[inline]
    pub(crate) fn checked_charge(
        self,
        limit: MaxBuildSteps,
    ) -> Result<Self, BuildError>
    {
        let next = self
            .steps
            .checked_add(1u64)
            .ok_or(BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::BuildSteps,
            })?;
        if next > limit.steps {
            return Err(BuildError::LimitExceeded {
                kind: BuildLimitKind::BuildSteps,
                limit: LimitBound::from(limit.steps),
            });
        }
        Ok(Self { steps: next })
    }
}
#[cfg(test)]
mod tests
{
    use super::*;

    /// Platform counts preserve every represented value and reject only
    /// narrowing loss.
    #[test]
    fn platform_counts_narrow_without_loss()
    {
        for count in [0_usize, 1, usize::MAX] {
            assert_eq!(
                ScalarWidth::try_from(count).map(u32::from),
                u32::try_from(count).map_err(|_error| BuildError::ArithmeticOverflow {
                    operation: BuildArithmetic::ScalarWidth,
                })
            );
            assert_eq!(
                TextBytesUsed::try_from(count).map(u64::from),
                u64::try_from(count).map_err(|_error| BuildError::ArithmeticOverflow {
                    operation: BuildArithmetic::TextBytes,
                })
            );
            assert_eq!(
                VerbatimLinesUsed::try_from(count).map(u64::from),
                u64::try_from(count).map_err(|_error| BuildError::ArithmeticOverflow {
                    operation: BuildArithmetic::VerbatimLines,
                })
            );
        }
        if let Ok(ceiling) = usize::try_from(u32::MAX)
            && ceiling < usize::MAX
        {
            assert_eq!(
                ScalarWidth::try_from(ceiling),
                Ok(ScalarWidth::from(u32::MAX))
            );
            assert_eq!(
                ScalarWidth::try_from(ceiling.saturating_add(1)),
                Err(BuildError::ArithmeticOverflow {
                    operation: BuildArithmetic::ScalarWidth
                })
            );
        }
    }

    /// Wide arithmetic separates inclusive ceilings from counter overflow and
    /// preserves refusal kinds.
    #[test]
    fn checked_charges_preserve_exact_boundaries_and_error_precedence()
    {
        let expected = |current: u64, amount: u64, limit: u64, operation, kind| {
            let sum = u128::from(current).saturating_add(u128::from(amount));
            if sum > u128::from(u64::MAX) {
                Err(BuildError::ArithmeticOverflow { operation })
            }
            else if sum > u128::from(limit) {
                Err(BuildError::LimitExceeded {
                    kind,
                    limit: LimitBound::from(limit),
                })
            }
            else {
                Ok(u64::try_from(sum).expect("bounded widened sum"))
            }
        };
        for current in [
            0_u64,
            1,
            2,
            u64::from(u32::MAX),
            u64::MAX.saturating_sub(1),
            u64::MAX,
        ] {
            for ceiling in [0_u32, 1, 2, u32::MAX] {
                assert_eq!(
                    DocNodesUsed::from(current)
                        .checked_charge(MaxDocNodes::from(ceiling))
                        .map(u64::from),
                    expected(
                        current,
                        1,
                        u64::from(ceiling),
                        BuildArithmetic::NodeCount,
                        BuildLimitKind::DocNodes
                    )
                );
                for amount in [0_u64, 1, 2, u64::MAX] {
                    assert_eq!(
                        VerbatimLinesUsed::from(current)
                            .checked_charge(
                                VerbatimLinesUsed::from(amount),
                                MaxVerbatimLines::from(ceiling)
                            )
                            .map(u64::from),
                        expected(
                            current,
                            amount,
                            u64::from(ceiling),
                            BuildArithmetic::VerbatimLines,
                            BuildLimitKind::VerbatimLines
                        )
                    );
                }
            }
            for ceiling in [0_u64, 1, 2, u64::MAX] {
                assert_eq!(
                    BuildStepsUsed::from(current)
                        .checked_charge(MaxBuildSteps::from(ceiling))
                        .map(u64::from),
                    expected(
                        current,
                        1,
                        ceiling,
                        BuildArithmetic::BuildSteps,
                        BuildLimitKind::BuildSteps
                    )
                );
            }
            for ceiling in [0_usize, 1, 2, usize::MAX] {
                for amount in [0_u64, 1, 2, u64::MAX] {
                    assert_eq!(
                        TextBytesUsed::from(current)
                            .checked_charge(
                                TextBytesUsed::from(amount),
                                MaxTextBytes::from(ceiling)
                            )
                            .map(u64::from),
                        expected(
                            current,
                            amount,
                            u64::try_from(ceiling).expect("supported platform width"),
                            BuildArithmetic::TextBytes,
                            BuildLimitKind::TextBytes
                        )
                    );
                }
            }
        }
    }
}
