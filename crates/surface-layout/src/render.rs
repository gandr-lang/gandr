//! The render entry point and machine handoff.
//!
//! Resolution produces a retained first-order plan. This module checks the
//! selected output size, reserves the final buffer once, and delegates all
//! plan execution to the explicit VM in [`crate::vm`]. Tainted results remain
//! complete output; taint reports theorem scope rather than truncation.

use alloc::string::String;

use crate::arena::DocArena;
use crate::arena::DocId;
use crate::error::RenderError;
use crate::limits::RenderMeter;
use crate::measure::LayoutCost;
use crate::measure::LayoutOptions;
use crate::measure::WidthTaint;
use crate::resolve::resolve_for_render;
use crate::vm;

/// Complete rendered UTF-8 output.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct RenderedText(String);

impl From<String> for RenderedText
{
    /// Wraps the bytes the machine emitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for RenderedText
{
    /// The rendered text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl core::ops::Deref for RenderedText
{
    type Target = str;

    /// The rendered text, so string methods apply directly.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &Self::Target
    {
        self.0.as_str()
    }
}

impl core::fmt::Display for RenderedText
{
    /// Writes the rendered text unchanged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly the rendered bytes, no quoting or escaping.
    /// - provides: the output a reader sees.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0.as_str())
    }
}

impl PartialEq<&str> for RenderedText
{
    /// Compares the rendered text with a string, byte for byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &&str,
    ) -> bool
    {
        self.0 == *other
    }
}

impl PartialEq<RenderedText> for &str
{
    /// Compares a string with the rendered text, byte for byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &RenderedText,
    ) -> bool
    {
        *self == other.0
    }
}

/// A complete render result and its selected-layout metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rendered
{
    /// The exact emitted bytes as UTF-8 text.
    pub text: RenderedText,
    /// The selected lexicographic layout cost.
    pub cost: LayoutCost,
    /// Whether the selected layout required width taint.
    pub width_tainted: WidthTaint,
}

/// Resolves and renders one document without exposing partial output.
///
/// # Specification
/// - requires: `root` belongs to `arena`, `options` has computation width at
///   least as large as page width, and `meter` remains exclusively borrowed.
/// - ensures: the selected output byte count is checked and reserved once,
///   every VM append is metered before mutation, and success returns all bytes.
/// - provides: exact rendered text, selected cost, and width-taint status.
/// - fails: returns a typed render error without returning partial output.
/// - panics: none.
///
/// # Errors
/// Returns [`RenderError`] for invalid handles, invalid widths, checked
/// arithmetic, allocation failure, or any named resolution/VM limit.
///
/// # Adequacy
/// - hypothesis: L3 — exact output, taint completeness, promise columns and
///   indentation, append accounting, machine ceilings, and no-partial-output
///   behavior distinguish the fused render path.
/// - witness: `algebra::tests::render_text_and_layout_metadata_are_exact`
/// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
/// - witness: `algebra::tests::render_tainted_root_uses_complete_left_biased_output`
/// - witness: `algebra::tests::render_tainted_root_preserves_promise_columns_and_indentation`
/// - witness: `algebra::tests::render_limits_fail_without_partial_output`
/// - witness: `algebra::tests::render_vm_stack_limit_is_checked_before_output`
#[inline]
pub fn render(
    arena: &DocArena,
    root: DocId,
    options: &LayoutOptions,
    meter: &mut RenderMeter,
) -> Result<Rendered, RenderError>
{
    let resolved = resolve_for_render(arena, root, *options, meter)?;
    let expected = resolved.output_bytes();
    meter.check_output_bytes(expected)?;
    let output = vm::execute(
        arena,
        resolved.plan_arena(),
        resolved.plan(),
        expected,
        meter,
    )?;
    Ok(Rendered {
        text: output.into_text(),
        cost: resolved.cost(),
        width_tainted: resolved.width_taint(),
    })
}
