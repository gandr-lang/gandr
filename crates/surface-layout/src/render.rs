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
    /// - executable: none — Formatter exposes a write-only sink, not the bytes
    ///   written or its failure state; checking either would require wrapping
    ///   or replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rendered Unicode, control bytes and an exhausted
    ///   fixed-size I/O sink expose unchanged display bytes and propagation of
    ///   write failure. Quoting, escaping, truncation or swallowed sink errors
    ///   change these observations; diagnostic wording is not pinned.
    /// - witness: `render::tests::display_preserves_bytes_and_propagates_an_exhausted_sink`
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
///
/// # Specification
/// - requires: the value comes from a successful render.
/// - ensures: the complete UTF-8 text, cost and width-taint status describe the
///   same selected layout.
/// - provides: the state represented by this item.
/// - panics: none.
/// - executable: none — this result is a data carrier; render constructs its
///   coherent output and metadata.
///
/// # Adequacy
/// - hypothesis: L3 — complete Unicode and mixed-ending output, selected
///   metadata, preserved taint context and exact ceilings expose the fused
///   render surface. Byte/scalar confusion, duplicate output charges, lost
///   taint or partial success change these observations. Failure never returns
///   a rendered value; counters may record work already performed.
/// - witness: `algebra::tests::render_text_and_layout_metadata_are_exact`
/// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
/// - witness: `algebra::tests::render_tainted_root_preserves_promise_columns_and_indentation`
/// - witness: `algebra::tests::render_limits_fail_without_partial_output`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
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
/// - requires: the arena is finalized and the meter remains exclusively
///   borrowed; candidate handles and widths include the documented refusal
///   cases.
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
/// - hypothesis: L3 — complete Unicode and mixed-ending output, selected
///   metadata, preserved taint context and exact ceilings expose the fused
///   render surface. Byte/scalar confusion, duplicate output charges, lost
///   taint or partial success change these observations. Failure never returns
///   a rendered value; counters may record work already performed.
/// - witness: `algebra::tests::render_text_and_layout_metadata_are_exact`
/// - witness: `algebra::tests::render_preserves_verbatim_bytes_and_physical_endings`
/// - witness: `algebra::tests::render_tainted_root_preserves_promise_columns_and_indentation`
/// - witness: `algebra::tests::render_limits_fail_without_partial_output`
/// - witness: `resolve::tests::resolution_validates_inputs_before_work_and_charges_output_once`
#[anodized::spec(
    captures: before = meter.usage(),
    ensures: |ret| if arena.contains(root) == crate::arena::DocHandleStatus::Absent { matches!(ret, Err(RenderError::UnknownDoc))
            && meter.usage() == before }
        else if u32::from(options.computation_width) < u32::from(options.page_width) { matches!(ret, Err(RenderError::InvalidWidth))
            && meter.usage() == before }
        else { ret.as_ref().map_or(true,
        |rendered| u64::try_from(rendered.text.len()).ok().and_then(|bytes| u64::from(before.output_bytes).checked_add(bytes)) == Some(u64::from(meter.usage().output_bytes))) }
)]
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

#[cfg(test)]
mod tests
{
    /// Display is byte-preserving and an exhausted output sink cannot become
    /// success.
    #[test]
    fn display_preserves_bytes_and_propagates_an_exhausted_sink()
    {
        let text = super::RenderedText::from(alloc::string::String::from("é𐐀\r\n\0\\\""));
        assert_eq!(alloc::format!("{text}"), text.as_ref());
        let mut storage = [0_u8; 3];
        let failure =
            std::io::Write::write_fmt(&mut storage.as_mut_slice(), format_args!("{text}"))
                .expect_err("bounded sink must refuse");
        let direct = std::io::Write::write_all(&mut [0_u8; 0].as_mut_slice(), b"x")
            .expect_err("exhausted sink");
        assert_eq!(failure.kind(), direct.kind());
        assert_eq!(storage.as_slice(), &text.as_bytes()[.. 3]);
    }
}
