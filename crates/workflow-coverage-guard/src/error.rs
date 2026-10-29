//! The refusals a coverage comparison can meet, each naming what it refused.

use core::fmt;

use gandr_workflow_github::GitHubError;

/// Why the comparison could not be made or filed.
///
/// # Specification
/// - provides: one variant per refusal; each carries the argument, the address,
///   the commit or the command it refused, so the message points at what must
///   change.
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
    /// A `--threshold` argument is not a decimal of at most two fractional
    /// digits.
    Threshold
    {
        /// The argument.
        text: String,
    },
    /// A Codecov request could not run, failed, or answered what this crate
    /// does not read.
    Fetch
    {
        /// The address requested.
        url: String,
        /// Why `curl` did not start, how it exited, or why the answer is not
        /// read.
        message: String,
    },
    /// Codecov had not finished processing the commit's upload in the time
    /// allowed, or processing ended in another state.
    Unprocessed
    {
        /// The commit.
        sha: String,
        /// The state Codecov last reported.
        state: String,
    },
    /// The commit is not among the uploads Codecov lists for `main`.
    Unlisted
    {
        /// The commit.
        sha: String,
    },
    /// No processed upload of `main` precedes the commit's.
    NoBaseline
    {
        /// The commit.
        sha: String,
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
    /// The badge file could not be written.
    Badge
    {
        /// The file, as given.
        path: String,
        /// The writer's description of the failure.
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
            Self::Threshold { ref text } => write!(
                f,
                "`{text}` is not a number of points with at most two decimals"
            ),
            Self::Fetch {
                ref url,
                ref message,
            } => write!(f, "`{url}` failed: {message}"),
            Self::Unprocessed { ref sha, ref state } => write!(
                f,
                "Codecov has not processed the upload of {sha}: its state is `{state}`"
            ),
            Self::Unlisted { ref sha } => {
                write!(f, "{sha} is not among the uploads Codecov lists for main")
            },
            Self::NoBaseline { ref sha } => {
                write!(f, "no processed upload of main precedes {sha}")
            },
            Self::Gh(ref error) => error.fmt(f),
            Self::Output { ref message } => write!(f, "standard output: {message}"),
            Self::Badge {
                ref path,
                ref message,
            } => write!(f, "the badge `{path}`: {message}"),
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
        let sha = || "f6b04aebd5fff9512341d81310be4a4446db3ba4".to_owned();
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
                GuardError::Threshold {
                    text: "0.125".into(),
                },
                "`0.125` is not a number of points with at most two decimals",
            ),
            (
                GuardError::Fetch {
                    url: "https://api.codecov.io/x".into(),
                    message: "exit status: 22: HTTP 404".into(),
                },
                "`https://api.codecov.io/x` failed: exit status: 22: HTTP 404",
            ),
            (
                GuardError::Unprocessed {
                    sha: sha(),
                    state: "pending".into(),
                },
                "Codecov has not processed the upload of \
                 f6b04aebd5fff9512341d81310be4a4446db3ba4: its state is `pending`",
            ),
            (
                GuardError::Unlisted { sha: sha() },
                "f6b04aebd5fff9512341d81310be4a4446db3ba4 is not among the uploads Codecov \
                 lists for main",
            ),
            (
                GuardError::NoBaseline { sha: sha() },
                "no processed upload of main precedes f6b04aebd5fff9512341d81310be4a4446db3ba4",
            ),
            (
                GuardError::Output {
                    message: "broken pipe".into(),
                },
                "standard output: broken pipe",
            ),
            (
                GuardError::Badge {
                    path: "badge/coverage.json".into(),
                    message: "permission denied".into(),
                },
                "the badge `badge/coverage.json`: permission denied",
            ),
        ];
        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected, "{error:?}");
        }
    }
}
