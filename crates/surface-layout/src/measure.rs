//! Measure, cost, and resolution options.
//!
//! The resolver cannot decide a winning layout without its cost currency, width
//! context, and physical line-ending policy, so they live together here.
//! Mutable measures remain private; the public API exposes only the selected
//! summary returned by [`crate::resolve::resolve`].

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
