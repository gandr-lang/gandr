//! The refusals a budget report can meet, each naming what it refused.

use core::fmt;

/// Why a budget report could not be produced or filed.
///
/// # Specification
/// - provides: one variant per refusal; each carries the argument or the
///   command it refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BudgetError
{
    /// A `--budget` argument is not a job name, `=`, and whole seconds.
    Budget
    {
        /// The argument.
        text: String,
    },
    /// A `gh` invocation could not run, exited unsuccessfully, or printed
    /// what this crate does not read.
    Gh
    {
        /// The invocation, as typed.
        command: String,
        /// Why it did not start, how it exited, or what it printed.
        message: String,
    },
    /// Standard output could not be written.
    Output
    {
        /// The writer's description of the failure.
        message: String,
    },
}

impl fmt::Display for BudgetError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's input and its detail.
    /// - provides: the message the binary prints before exiting with status 2.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant's rendering names its input and its
    ///   detail; a dropped field or a swapped variant changes the asserted
    ///   line.
    /// - witness: `error::tests::every_refusal_names_its_input`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Budget { ref text } => write!(
                f,
                "`{text}` is not a job name, `=`, and a whole number of seconds"
            ),
            | Self::Gh {
                ref command,
                ref message,
            } => write!(f, "`{command}` failed: {message}"),
            | Self::Output { ref message } => write!(f, "standard output: {message}"),
        }
    }
}

/// A refusal is an error value, so clap can report a malformed `--budget`.
impl core::error::Error for BudgetError
{
}

#[cfg(test)]
mod tests
{
    use super::BudgetError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let cases = [
            (
                BudgetError::Budget {
                    text: "check Clippy wall".into(),
                },
                "`check Clippy wall` is not a job name, `=`, and a whole number of seconds",
            ),
            (
                BudgetError::Gh {
                    command: "gh issue list".into(),
                    message: "HTTP 401: Bad credentials".into(),
                },
                "`gh issue list` failed: HTTP 401: Bad credentials",
            ),
            (
                BudgetError::Output {
                    message: "broken pipe".into(),
                },
                "standard output: broken pipe",
            ),
        ];
        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected, "{error:?}");
        }
    }
}
