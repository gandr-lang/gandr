//! The refusals filing a commit's hotpath checks can meet, each naming what it
//! refused.

use core::fmt;

use gandr_workflow_github::GitHubError;

/// Why the checks could not be read or filed.
///
/// # Specification
/// - provides: one variant per refusal; each carries the argument or the
///   command it refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GuardError
{
    /// A `--repository` argument is not `OWNER/NAME`.
    Repository
    {
        /// The argument.
        text: String,
    },
    /// A `--sha` argument is not seven to forty lowercase hexadecimal digits.
    Sha
    {
        /// The argument.
        text: String,
    },
    /// A `gh` invocation could not run, exited unsuccessfully, or printed
    /// what this crate does not read.
    Gh(GitHubError),
    /// Standard output could not be written.
    Output
    {
        /// The writer's description of the failure.
        message: String,
    },
    /// A hotpath report or a regression policy the judge reads could not be
    /// read, or holds what the judge does not read.
    Input
    {
        /// The file, as given.
        path: String,
        /// Why it could not be read, or what it holds.
        message: String,
    },
}

impl fmt::Display for GuardError
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
            Self::Repository { ref text } => write!(f, "`{text}` is not `OWNER/NAME`"),
            Self::Sha { ref text } => write!(
                f,
                "`{text}` is not a commit: seven to forty lowercase hexadecimal digits"
            ),
            Self::Gh(ref error) => error.fmt(f),
            Self::Output { ref message } => write!(f, "standard output: {message}"),
            Self::Input {
                ref path,
                ref message,
            } => write!(f, "`{path}`: {message}"),
        }
    }
}

/// A refusal is an error value, so clap can report a malformed argument.
impl core::error::Error for GuardError
{
}

impl From<GitHubError> for GuardError
{
    /// The refusal of a failed `gh` invocation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: GitHubError) -> Self
    {
        Self::Gh(error)
    }
}

#[cfg(test)]
mod tests
{
    use super::GuardError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let cases = [
            (
                GuardError::Repository {
                    text: "gandr".into(),
                },
                "`gandr` is not `OWNER/NAME`",
            ),
            (
                GuardError::Sha {
                    text: "main".into(),
                },
                "`main` is not a commit: seven to forty lowercase hexadecimal digits",
            ),
            (
                GuardError::Output {
                    message: "broken pipe".into(),
                },
                "standard output: broken pipe",
            ),
            (
                GuardError::Input {
                    path: "target/hotpath/runs/store-1.json".into(),
                    message: "the timing section is missing".into(),
                },
                "`target/hotpath/runs/store-1.json`: the timing section is missing",
            ),
        ];
        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected, "{error:?}");
        }
    }
}
