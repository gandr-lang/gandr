//! Nominal boundaries the comment gate's signatures stop at.

/// Borrowed text a signature may name without exposing `str`.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Text<'text>(pub &'text str);

/// A borrowed ledger key.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct Line<'text>(pub &'text str);

/// A yes-or-no answer.
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Yes(pub bool);

impl AsRef<str> for Text<'_>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl AsRef<str> for Line<'_>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl core::fmt::Display for Line<'_>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}
