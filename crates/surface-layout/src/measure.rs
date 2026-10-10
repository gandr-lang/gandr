//! Measure, cost, and resolution options.
//!
//! The resolver cannot decide a winning layout without its cost currency, width
//! context, and physical line-ending policy, so they live together here.
//! Mutable measures remain private; the public API exposes only the selected
//! summary returned by [`crate::resolve::resolve`].

use anodized::spec;

use crate::error::RenderArithmetic;
use crate::error::RenderError;
use crate::plan::PlanId;
use crate::units::Column;
use crate::units::ComputationWidth;
use crate::units::Indentation;
use crate::units::LineBreaks;
use crate::units::OutputBytes;
use crate::units::PageWidth;
use crate::units::ScalarWidth;
use crate::units::SquaredOverflow;

/// The physical ending emitted by layout-owned line nodes.
///
/// # Specification
/// - requires: the value is selected before resolution starts.
/// - ensures: all layout-owned endings use exactly this byte shape.
/// - provides: the physical ending policy for a resolution.
/// - panics: none.
/// - executable: none — the declaration is a closed data carrier with no
///   executable boundary; construction, arithmetic and resolution operations
///   carry the corresponding predicates.
///
/// # Adequacy
/// - hypothesis: L3 — both ending policies are observed through complete
///   rendered bytes and VM byte reconciliation; swapping endings or treating
///   CRLF as one byte changes output or produces a mismatch.
/// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(u8)]
pub enum PhysicalLineEnding
{
    /// A single line-feed byte.
    Lf,
    /// A carriage-return followed by line-feed.
    CrLf,
}

impl PhysicalLineEnding
{
    /// Returns the exact byte width of this ending.
    ///
    /// # Specification
    /// - requires: the ending is one of the closed enum variants.
    /// - ensures: the returned count matches emitted bytes.
    /// - provides: output accounting for layout-owned line nodes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — LF and CRLF policies expose byte accounting through
    ///   complete rendered output; a wrong ending width makes the VM byte
    ///   reconciliation fail even when the scalar width is unchanged.
    /// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
    #[spec(
        ensures: |ret| u64::from(ret) == match self { Self::Lf => 1, Self::CrLf => 2 }
    )]
    #[inline]
    #[must_use]
    pub(crate) fn byte_width(self) -> OutputBytes
    {
        match self {
            | Self::Lf => OutputBytes::from(1u64),
            | Self::CrLf => OutputBytes::from(2u64),
        }
    }
}

/// Options held constant for one resolution invocation.
///
/// # Specification
/// - requires: `computation_width` is at least `page_width`.
/// - ensures: every memo key observes one fixed width and ending policy.
/// - provides: the caller's page, computation, and physical-ending choices.
/// - fails: [`Self::try_new`] rejects an invalid width ordering.
/// - panics: none.
/// - executable: none — the declaration is a closed data carrier with no
///   executable boundary; construction, arithmetic and resolution operations
///   carry the corresponding predicates.
///
/// # Adequacy
/// - hypothesis: L3 — zero, equality, reversed widths and u32 maximum under
///   both ending policies expose accepted fields and the `InvalidWidth`
///   refusal. Swapping widths or ending policy and shifting the ordering
///   boundary change these observations.
/// - witness: `measure::tests::width_options_preserve_policy_and_reject_reversal`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LayoutOptions
{
    /// The width used by the lexicographic cost.
    pub page_width: PageWidth,
    /// The width within which the optimality theorem is computed.
    pub computation_width: ComputationWidth,
    /// The ending emitted by layout-owned line nodes.
    pub line_ending: PhysicalLineEnding,
}

impl Default for LayoutOptions
{
    /// A page of 100 columns computed within 120, with `\n` line endings.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the computation width is no smaller than the page width.
    /// - provides: the options a caller with no page of its own renders at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the default policy must remain inside the accepted
    ///   width domain. The witness observes successful reconstruction with
    ///   identical fields rather than pinning incidental numeric defaults; a
    ///   reversed ordering changes that result.
    /// - witness: `measure::tests::width_options_preserve_policy_and_reject_reversal`
    #[spec(
        ensures: |ret| u32::from(ret.computation_width) >= u32::from(ret.page_width)
    )]
    #[inline]
    fn default() -> Self
    {
        Self {
            page_width: PageWidth::from(100u32),
            computation_width: ComputationWidth::from(120u32),
            line_ending: PhysicalLineEnding::Lf,
        }
    }
}

impl LayoutOptions
{
    /// Creates options after checking the width ordering.
    ///
    /// # Specification
    /// - requires: both widths are nominal scalar-column ceilings.
    /// - ensures: the computation width is no smaller than the page width.
    /// - provides: validated resolution options.
    /// - fails: returns [`RenderError::InvalidWidth`] for reversed widths.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`RenderError::InvalidWidth`] when computation is narrower than
    /// the page.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal, ascending and reversed widths include zero and
    ///   u32 maximum under both ending policies. Exact accepted fields and
    ///   `InvalidWidth` distinguish a shifted boundary, swapped widths, lost
    ///   ending policy and an incorrect refusal.
    /// - witness: `measure::tests::width_options_preserve_policy_and_reject_reversal`
    #[spec(
        ensures: |ret| ret.as_ref().map_or_else(|error| u32::from(computation_width) < u32::from(page_width)
                && *error == RenderError::InvalidWidth,
            |options| u32::from(computation_width) >= u32::from(page_width)
                && options.page_width == page_width
                && options.computation_width == computation_width
                && options.line_ending == line_ending)
    )]
    #[inline]
    pub fn try_new(
        page_width: PageWidth,
        computation_width: ComputationWidth,
        line_ending: PhysicalLineEnding,
    ) -> Result<Self, RenderError>
    {
        if u32::from(computation_width) < u32::from(page_width) {
            return Err(RenderError::InvalidWidth);
        }
        Ok(Self {
            page_width,
            computation_width,
            line_ending,
        })
    }
}

/// The lexicographic cost of one layout.
///
/// # Specification
/// - requires: both components were accumulated through checked operations.
/// - ensures: squared overflow is compared before line breaks.
/// - provides: the public optimality projection.
/// - panics: none.
/// - executable: none — the declaration is a closed data carrier with no
///   executable boundary; construction, arithmetic and resolution operations
///   carry the corresponding predicates.
///
/// # Adequacy
/// - hypothesis: L3 — asymmetric component pairs distinguish lexicographic
///   overflow-first ordering; exact sums and overflow precedence distinguish
///   swapped fields, saturation and omitted components.
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
/// - witness: `algebra::tests::resolver_choice_uses_squared_overflow_before_line_breaks`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LayoutCost
{
    /// Incremental squared overflow.
    pub squared_overflow: SquaredOverflow,
    /// Layout-owned line endings.
    pub line_breaks: LineBreaks,
}

impl LayoutCost
{
    /// Returns the zero cost.
    ///
    /// # Specification
    /// - requires: no output has been charged.
    /// - ensures: both components are zero.
    /// - provides: the identity cost for [`crate::arena::DocNode::Empty`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero is observed as the additive identity of costs
    ///   with asymmetric and maximal components. A nonzero component changes
    ///   the sum or causes an otherwise absent overflow.
    /// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
    #[spec(
        ensures: |ret| u64::from(ret.squared_overflow) == 0
                && u64::from(ret.line_breaks) == 0
    )]
    #[inline]
    #[must_use]
    pub(crate) fn zero() -> Self
    {
        Self {
            squared_overflow: SquaredOverflow::from(0u64),
            line_breaks: LineBreaks::from(0u64),
        }
    }
}

/// Whether the selected root came from a width-tainted promise.
///
/// # Specification
/// - requires: the value comes from the resolver's root state.
/// - ensures: taint is reported without truncating the chosen output.
/// - provides: a nominal public taint projection.
/// - panics: none.
/// - executable: none — the declaration is a closed data carrier with no
///   executable boundary; construction, arithmetic and resolution operations
///   carry the corresponding predicates.
///
/// # Adequacy
/// - hypothesis: L3 — bounded and width-tainted contexts are observed through
///   the public taint projection and complete selected output. Dropping taint,
///   truncating the promise or changing left bias changes those observations.
/// - witness: `algebra::tests::tainted_contexts_preserve_taint_and_output`
/// - witness: `algebra::tests::render_tainted_root_uses_complete_left_biased_output`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(u8)]
pub enum WidthTaint
{
    /// The selected root stayed inside the computation theorem.
    Untainted,
    /// The selected root required a retained width promise.
    Tainted,
}

/// One private candidate measure.
///
/// # Specification
/// - requires: the plan identity belongs to the current resolution arena.
/// - ensures: column, cost and byte count describe that same candidate plan.
/// - provides: one coherent alternative for frontier selection.
/// - panics: none.
/// - executable: none — this record has no executable boundary; resolver
///   transitions construct its fields and VM reconciliation checks the selected
///   byte count.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive small documents compare selected costs and
///   output with a direct oracle, while complete rendering checks byte
///   reconciliation. Mixing summaries from different candidates or confusing
///   scalar columns with bytes changes the winner or output.
/// - witness: `algebra::tests::exhaustive_small_documents_match_the_direct_oracle`
/// - witness: `algebra::tests::render_text_and_layout_metadata_are_exact`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Measure
{
    /// The column where this candidate ends.
    pub last_column: Column,
    /// The candidate's lexicographic cost.
    pub cost: LayoutCost,
    /// The first-order plan producing this candidate.
    pub plan: PlanId,
    /// Exact bytes emitted by this candidate.
    pub output_bytes: OutputBytes,
}

/// Computes the overflow delta for one contiguous fragment.
///
/// # Specification
/// - requires: `start` and `width` are checked scalar columns.
/// - ensures: the result is the difference of squared excesses at the two
///   endpoints.
/// - provides: the incremental text and first-verbatim-fragment charge.
/// - fails: reports checked column or square overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exhaustive small column/width/page cube and endpoint
///   extremes are compared with widened squared-excess arithmetic.
///   Incoming-column loss, unsigned wrap, charging total rather than
///   incremental overflow, and accepting an overflowing endpoint square change
///   the cost or typed refusal. Allocation is outside this pure arithmetic
///   boundary.
/// - witness: `measure::tests::fragment_costs_match_widened_endpoint_arithmetic`
#[spec(
    ensures: |ret| { let before = u128::from(u32::from(start)).saturating_sub(u128::from(u32::from(page))).saturating_pow(2);
        let after = u128::from(u32::from(start)).saturating_add(u128::from(u32::from(width))).saturating_sub(u128::from(u32::from(page))).saturating_pow(2);
        ret.as_ref().map_or_else(|error| after > u128::from(u64::MAX)
            && *error == RenderError::ArithmeticOverflow { operation: RenderArithmetic::SquaredOverflow },
        |value| after <= u128::from(u64::MAX)
            && u128::from(u64::from(*value)) == after.saturating_sub(before)) }
)]
fn overflow_delta(
    start: Column,
    width: ScalarWidth,
    page: PageWidth,
) -> Result<SquaredOverflow, RenderError>
{
    let start_value = u64::from(u32::from(start));
    let width_value = u64::from(u32::from(width));
    let end_value =
        start_value
            .checked_add(width_value)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::Column,
            })?;
    let page_value = u64::from(u32::from(page));
    let start_excess = start_value.saturating_sub(page_value);
    let end_excess = end_value.saturating_sub(page_value);
    let start_square =
        start_excess
            .checked_mul(start_excess)
            .ok_or(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::SquaredOverflow,
            })?;
    let end_square = end_excess
        .checked_mul(end_excess)
        .ok_or(RenderError::ArithmeticOverflow {
            operation: RenderArithmetic::SquaredOverflow,
        })?;
    let delta = end_square
        .checked_sub(start_square)
        .ok_or(RenderError::ArithmeticOverflow {
            operation: RenderArithmetic::SquaredOverflow,
        })?;
    Ok(SquaredOverflow::from(delta))
}

/// Computes an absolute-column overflow square for a later verbatim fragment.
///
/// # Specification
/// - requires: `width` is a checked physical-fragment width.
/// - ensures: the charge starts at column zero.
/// - provides: the later-fragment cost contribution.
/// - fails: reports checked square overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exhaustive small column/width/page cube and endpoint
///   extremes are compared with widened squared-excess arithmetic.
///   Incoming-column loss, unsigned wrap, charging total rather than
///   incremental overflow, and accepting an overflowing endpoint square change
///   the cost or typed refusal. Allocation is outside this pure arithmetic
///   boundary.
/// - witness: `measure::tests::fragment_costs_match_widened_endpoint_arithmetic`
#[spec(
    ensures: |ret| { let before = u128::from(0_u32).saturating_sub(u128::from(u32::from(page))).saturating_pow(2);
        let after = u128::from(0_u32).saturating_add(u128::from(u32::from(width))).saturating_sub(u128::from(u32::from(page))).saturating_pow(2);
        ret.as_ref().map_or_else(|error| after > u128::from(u64::MAX)
            && *error == RenderError::ArithmeticOverflow { operation: RenderArithmetic::SquaredOverflow },
        |value| after <= u128::from(u64::MAX)
            && u128::from(u64::from(*value)) == after.saturating_sub(before)) }
)]
pub(crate) fn absolute_overflow(
    width: ScalarWidth,
    page: PageWidth,
) -> Result<SquaredOverflow, RenderError>
{
    overflow_delta(Column::from(0u32), width, page)
}

/// Adds two costs with checked component arithmetic.
///
/// # Specification
/// - requires: both costs came from checked layout fragments.
/// - ensures: each component is added exactly once.
/// - provides: concatenation and fragment accumulation.
/// - fails: reports overflow in the named component.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — asymmetric components, zero, exact u64 ceilings and
///   simultaneous overflow are observed as componentwise sums or the first
///   typed arithmetic refusal. Swapping components, wrapping, dropping an
///   operand and reversing overflow precedence change the result.
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
#[spec(
    ensures: |ret| { let overflow = u128::from(u64::from(left.squared_overflow)).saturating_add(u128::from(u64::from(right.squared_overflow)));
        let breaks = u128::from(u64::from(left.line_breaks)).saturating_add(u128::from(u64::from(right.line_breaks)));
        ret.as_ref().map_or_else(|error| if overflow > u128::from(u64::MAX) { *error == RenderError::ArithmeticOverflow { operation: RenderArithmetic::SquaredOverflow } }
        else { breaks > u128::from(u64::MAX)
            && *error == RenderError::ArithmeticOverflow { operation: RenderArithmetic::LineBreaks } },
        |cost| overflow == u128::from(u64::from(cost.squared_overflow))
            && breaks == u128::from(u64::from(cost.line_breaks))) }
)]
pub(crate) fn add_cost(
    left: LayoutCost,
    right: LayoutCost,
) -> Result<LayoutCost, RenderError>
{
    let squared_overflow = u64::from(left.squared_overflow)
        .checked_add(u64::from(right.squared_overflow))
        .ok_or(RenderError::ArithmeticOverflow {
            operation: RenderArithmetic::SquaredOverflow,
        })?;
    let line_breaks = u64::from(left.line_breaks)
        .checked_add(u64::from(right.line_breaks))
        .ok_or(RenderError::ArithmeticOverflow {
            operation: RenderArithmetic::LineBreaks,
        })?;
    Ok(LayoutCost {
        squared_overflow: SquaredOverflow::from(squared_overflow),
        line_breaks: LineBreaks::from(line_breaks),
    })
}

/// Adds exact output-byte counts with checked arithmetic.
///
/// # Specification
/// - requires: both byte counts describe the same candidate.
/// - ensures: no byte count wraps.
/// - provides: concatenation output accounting.
/// - fails: reports [`RenderArithmetic::OutputBytes`] on overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, one, u64 maximum and its predecessor are crossed
///   pairwise; exact byte sums and `OutputBytes` refusals distinguish wrapping,
///   saturation, a lost operand and the wrong arithmetic classification.
/// - witness: `measure::tests::cost_and_byte_addition_preserve_components_and_error_priority`
#[spec(
    ensures: |ret| { let sum = u128::from(u64::from(left)).saturating_add(u128::from(u64::from(right)));
        ret.as_ref().map_or_else(|error| sum > u128::from(u64::MAX)
            && *error == RenderError::ArithmeticOverflow { operation: RenderArithmetic::OutputBytes },
        |bytes| sum == u128::from(u64::from(*bytes))) }
)]
pub(crate) fn add_output_bytes(
    left: OutputBytes,
    right: OutputBytes,
) -> Result<OutputBytes, RenderError>
{
    let bytes =
        u64::from(left)
            .checked_add(u64::from(right))
            .ok_or(RenderError::ArithmeticOverflow {
                operation: RenderArithmetic::OutputBytes,
            })?;
    Ok(OutputBytes::from(bytes))
}

/// Returns the cost of a text-like fragment starting at `column`.
///
/// # Specification
/// - requires: `width` and `column` describe one stored fragment.
/// - ensures: overflow is charged from the incoming column.
/// - provides: the first-fragment cost rule.
/// - fails: reports checked arithmetic overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an exhaustive small column/width/page cube and endpoint
///   extremes are compared with widened squared-excess arithmetic.
///   Incoming-column loss, unsigned wrap, charging total rather than
///   incremental overflow, and accepting an overflowing endpoint square change
///   the cost or typed refusal. Allocation is outside this pure arithmetic
///   boundary.
/// - witness: `measure::tests::fragment_costs_match_widened_endpoint_arithmetic`
#[spec(
    ensures: |ret| { let before = u128::from(u32::from(column)).saturating_sub(u128::from(u32::from(page))).saturating_pow(2);
        let after = u128::from(u32::from(column)).saturating_add(u128::from(u32::from(width))).saturating_sub(u128::from(u32::from(page))).saturating_pow(2);
        ret.as_ref().map_or_else(|error| after > u128::from(u64::MAX)
            && *error == RenderError::ArithmeticOverflow { operation: RenderArithmetic::SquaredOverflow },
        |value| after <= u128::from(u64::MAX)
            && u128::from(u64::from(*value)) == after.saturating_sub(before)) }
)]
pub(crate) fn incoming_overflow(
    column: Column,
    width: ScalarWidth,
    page: PageWidth,
) -> Result<SquaredOverflow, RenderError>
{
    overflow_delta(column, width, page)
}

/// Adds a line break and indentation to an existing cost.
///
/// # Specification
/// - requires: `indentation` is the checked indentation of a line node.
/// - ensures: one line break and indentation overflow are charged.
/// - provides: the layout-owned newline cost rule.
/// - fails: reports checked arithmetic overflow.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — indentation below, at and above the page, including u32
///   maximum, is observed as an absolute overflow square and exactly one break.
///   Incoming-column contamination, off-by-one excess and a lost or doubled
///   break change the cost.
/// - witness: `measure::tests::fragment_costs_match_widened_endpoint_arithmetic`
#[spec(
    ensures: |ret| ret.as_ref().is_ok_and(|cost| u64::from(cost.line_breaks) == 1
            && u64::from(cost.squared_overflow) == u64::from(u32::from(indentation).saturating_sub(u32::from(page))).saturating_pow(2))
)]
pub(crate) fn line_cost(
    indentation: Indentation,
    page: PageWidth,
) -> Result<LayoutCost, RenderError>
{
    let indentation_width = ScalarWidth::from(u32::from(indentation));
    let overflow = absolute_overflow(indentation_width, page)?;
    let line_breaks = 1u64;
    Ok(LayoutCost {
        squared_overflow: overflow,
        line_breaks: LineBreaks::from(line_breaks),
    })
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// Width ordering and ending policy survive validation, including both
    /// extreme widths.
    #[test]
    fn width_options_preserve_policy_and_reject_reversal()
    {
        for page in [0_u32, 1, u32::MAX] {
            for computation in [0_u32, 1, u32::MAX] {
                for ending in [PhysicalLineEnding::Lf, PhysicalLineEnding::CrLf] {
                    let result = LayoutOptions::try_new(
                        PageWidth::from(page),
                        ComputationWidth::from(computation),
                        ending,
                    );
                    if computation < page {
                        assert_eq!(result, Err(RenderError::InvalidWidth));
                    }
                    else {
                        assert_eq!(
                            result,
                            Ok(LayoutOptions {
                                page_width: PageWidth::from(page),
                                computation_width: ComputationWidth::from(computation),
                                line_ending: ending
                            })
                        );
                    }
                }
            }
        }
        let defaults = LayoutOptions::default();
        assert_eq!(
            LayoutOptions::try_new(
                defaults.page_width,
                defaults.computation_width,
                defaults.line_ending
            ),
            Ok(defaults)
        );
    }

    /// Endpoint squares, not only their difference, must fit the cost currency.
    #[test]
    fn fragment_costs_match_widened_endpoint_arithmetic()
    {
        let check = |start: u32, width: u32, page: u32| {
            let first = u128::from(start).saturating_sub(u128::from(page));
            let last = u128::from(start)
                .saturating_add(u128::from(width))
                .saturating_sub(u128::from(page));
            let first_square = first.saturating_mul(first);
            let last_square = last.saturating_mul(last);
            let expected = if last_square > u128::from(u64::MAX) {
                Err(RenderError::ArithmeticOverflow {
                    operation: RenderArithmetic::SquaredOverflow,
                })
            }
            else {
                Ok(SquaredOverflow::from(
                    u64::try_from(last_square.saturating_sub(first_square))
                        .expect("bounded square difference"),
                ))
            };
            assert_eq!(
                overflow_delta(
                    Column::from(start),
                    ScalarWidth::from(width),
                    PageWidth::from(page)
                ),
                expected
            );
            assert_eq!(
                incoming_overflow(
                    Column::from(start),
                    ScalarWidth::from(width),
                    PageWidth::from(page)
                ),
                expected
            );
            if start == 0 {
                assert_eq!(
                    absolute_overflow(ScalarWidth::from(width), PageWidth::from(page)),
                    expected
                );
                assert_eq!(
                    line_cost(Indentation::from(width), PageWidth::from(page)),
                    expected.map(|squared_overflow| LayoutCost {
                        squared_overflow,
                        line_breaks: LineBreaks::from(1_u64)
                    })
                );
            }
        };
        for start in 0_u32 ..= 8 {
            for width in 0_u32 ..= 8 {
                for page in 0_u32 ..= 8 {
                    check(start, width, page);
                }
            }
        }
        for (start, width, page) in [
            (u32::MAX, 1, 0),
            (u32::MAX, u32::MAX, u32::MAX),
            (u32::MAX, u32::MAX, 0),
            (0, u32::MAX, 0),
            (0, u32::MAX, u32::MAX),
            (u32::MAX, 0, 0),
            (u32::MAX, 1, u32::MAX),
        ] {
            check(start, width, page);
        }
    }

    /// Component and byte arithmetic retain exact maxima and classify the first
    /// overflow.
    #[test]
    fn cost_and_byte_addition_preserve_components_and_error_priority()
    {
        for (left_overflow, left_breaks, right_overflow, right_breaks) in [
            (0_u64, 0_u64, 0_u64, 0_u64),
            (u64::MAX, 0, 0, u64::MAX),
            (0, u64::MAX, 0, 1),
            (u64::MAX, 0, 1, 0),
            (u64::MAX, u64::MAX, 1, 1),
            (1, 2, 3, 4),
        ] {
            let left = LayoutCost {
                squared_overflow: SquaredOverflow::from(left_overflow),
                line_breaks: LineBreaks::from(left_breaks),
            };
            let right = LayoutCost {
                squared_overflow: SquaredOverflow::from(right_overflow),
                line_breaks: LineBreaks::from(right_breaks),
            };
            let overflow = u128::from(left_overflow).saturating_add(u128::from(right_overflow));
            let breaks = u128::from(left_breaks).saturating_add(u128::from(right_breaks));
            let expected = if overflow > u128::from(u64::MAX) {
                Err(RenderError::ArithmeticOverflow {
                    operation: RenderArithmetic::SquaredOverflow,
                })
            }
            else if breaks > u128::from(u64::MAX) {
                Err(RenderError::ArithmeticOverflow {
                    operation: RenderArithmetic::LineBreaks,
                })
            }
            else {
                Ok(LayoutCost {
                    squared_overflow: SquaredOverflow::from(
                        u64::try_from(overflow).expect("bounded overflow cost"),
                    ),
                    line_breaks: LineBreaks::from(
                        u64::try_from(breaks).expect("bounded line count"),
                    ),
                })
            };
            assert_eq!(add_cost(left, right), expected);
            assert_eq!(add_cost(left, LayoutCost::zero()), Ok(left));
            assert_eq!(add_cost(LayoutCost::zero(), right), Ok(right));
        }
        let overflow_first = LayoutCost {
            squared_overflow: SquaredOverflow::from(0_u64),
            line_breaks: LineBreaks::from(u64::MAX),
        };
        let fewer_breaks = LayoutCost {
            squared_overflow: SquaredOverflow::from(1_u64),
            line_breaks: LineBreaks::from(0_u64),
        };
        assert!(overflow_first < fewer_breaks);
        for left in [0_u64, 1, u64::MAX.saturating_sub(1), u64::MAX] {
            for right in [0_u64, 1, u64::MAX.saturating_sub(1), u64::MAX] {
                let sum = u128::from(left).saturating_add(u128::from(right));
                let expected = u64::try_from(sum).map(OutputBytes::from).map_err(|_error| {
                    RenderError::ArithmeticOverflow {
                        operation: RenderArithmetic::OutputBytes,
                    }
                });
                assert_eq!(
                    add_output_bytes(OutputBytes::from(left), OutputBytes::from(right)),
                    expected
                );
            }
        }
    }
}
