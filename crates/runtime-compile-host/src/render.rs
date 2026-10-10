//! Canonical value rendering for compile-host agreement.

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

/// A value rendered in the host's s-expression grammar.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct RenderedValue(String);
impl From<String> for RenderedValue
{
    /// Own an externally supplied rendering.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: String) -> Self
    {
        Self(value)
    }
}
impl AsRef<str> for RenderedValue
{
    /// Borrow the rendering.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}
impl core::fmt::Display for RenderedValue
{
    /// Print the canonical text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(&self.0)
    }
}
/// Why a terminal value has no compile-host rendering.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RenderError
{
    /// A former is outside the positive grammar.
    OutsideSlice,
    /// An address does not resolve.
    DanglingValue(ValueId),
    /// An integer exceeds the signed wire range.
    IntegerOutOfRange,
}
impl core::fmt::Display for RenderError
{
    /// Name the refusing operation; the typed error retains its address.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::OutsideSlice => "value has no positive-core rendering",
            | Self::DanglingValue(_) => "value address does not resolve",
            | Self::IntegerOutOfRange => "integer exceeds signed 64-bit image range",
        })
    }
}
impl core::error::Error for RenderError
{
}
/// A pending node or delimiter.
enum Step
{
    /// Visit one arena node.
    Value(ValueId),
    /// Append a static grammar delimiter.
    Text(&'static str),
}
/// Render a terminal integer, unit, pair or sum injection without recursion.
///
/// # Specification
/// - ensures: returns the grammar (int N), (unit), (pair V V), (inl V), (inr
///   V), preserving field order and signed integer value.
/// - fails: `OutsideSlice` for other formers, `DanglingValue` for an absent
///   node, `IntegerOutOfRange` for a literal outside the signed image range.
/// - panics: none.
///
/// # Errors
/// Returns the corresponding `RenderError`, including for nested failures.
///
/// # Adequacy
/// - hypothesis: L2 exact nested grammar goldens separate order and delimiter
///   faults; L3 nested excluded values, signed endpoints and dangling nodes
///   separate failure classes.
/// - witness: `tests::rendering::a_nested_value_renders_in_source_order`
/// - witness: `tests::rendering::a_value_outside_the_slice_has_no_spelling`
/// - witness: `tests::rendering::literal_bounds_and_dangling_values_preserve_refusals`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |text| text.0.starts_with('(') && text.0.ends_with(')')))]
#[inline]
pub fn canonical(
    core: &CoreArena,
    root: ValueId,
) -> Result<RenderedValue, RenderError>
{
    let mut text = String::new();
    let mut pending = vec![Step::Value(root)];
    while let Some(step) = pending.pop() {
        let id = match step {
            | Step::Text(delimiter) => {
                text.push_str(delimiter);
                continue;
            },
            | Step::Value(id) => id,
        };
        let value = core.value(id).ok_or(RenderError::DanglingValue(id))?;
        match *value {
            | Value::Literal(Literal::Integer(ref integer)) => {
                let integer = crate::image::Literal::try_from(integer)
                    .map_err(|_range| RenderError::IntegerOutOfRange)?;
                text.push_str("(int ");
                // Formatting a built-in integer into String is infallible.
                let _written =
                    core::fmt::Write::write_fmt(&mut text, format_args!("{}", i64::from(integer)));
                text.push(')');
            },
            | Value::Unit => text.push_str("(unit)"),
            | Value::Pair(first, second) => {
                text.push_str("(pair ");
                pending.extend([
                    Step::Text(")"),
                    Step::Value(second),
                    Step::Text(" "),
                    Step::Value(first),
                ]);
            },
            | Value::Injection(side, payload) => {
                text.push_str(match side {
                    | Side::Left => "(inl ",
                    | Side::Right => "(inr ",
                });
                pending.extend([Step::Text(")"), Step::Value(payload)]);
            },
            | _ => return Err(RenderError::OutsideSlice),
        }
    }
    Ok(RenderedValue(text))
}
