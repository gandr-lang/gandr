//! Why a ledger's text does not read.

use core::fmt;

/// Why a ledger's text does not read.
///
/// # Specification
/// - provides: the line that refused, so the message names what to fix or
///   regenerate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LedgerError
{
    /// A line, neither blank nor a `#` line, that no key reads from.
    Unread
    {
        /// The line, trimmed.
        line: String,
    },
}

impl fmt::Display for LedgerError
{
    /// Names the line no key reads from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the refused line in backquotes.
    /// - provides: the message a check prints for a malformed ledger.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the message names the line; a dropped line changes
    ///   the asserted text.
    /// - witness: `error::tests::a_refusal_names_its_line`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unread { ref line } => write!(f, "`{line}` is not a ledger key"),
        }
    }
}

/// A refusal is an error value, so a check can report it.
impl core::error::Error for LedgerError
{
}

#[cfg(test)]
mod tests
{
    use super::LedgerError;

    #[test]
    fn a_refusal_names_its_line()
    {
        assert_eq!(
            LedgerError::Unread {
                line: "corpus/a.gandr Passive".to_owned()
            }
            .to_string(),
            "`corpus/a.gandr Passive` is not a ledger key"
        );
    }
}
