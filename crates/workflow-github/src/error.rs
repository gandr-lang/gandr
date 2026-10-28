//! The one error family of a `gh` invocation, each refusal naming the
//! invocation it refused.

use core::fmt;
use std::process::Command;
use std::process::ExitStatus;

use crate::Invocation;

/// Why a `gh` invocation gave no answer the caller reads.
///
/// # Specification
/// - provides: one variant per way an invocation fails; each carries the
///   invocation, so the message names what to rerun.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GitHubError
{
    /// The command could not start, its input could not be written, or it
    /// could not be waited for.
    Unstarted
    {
        /// The invocation.
        invocation: Invocation,
        /// What the operating system reported.
        detail: String,
    },
    /// The command exited unsuccessfully.
    Exited
    {
        /// The invocation.
        invocation: Invocation,
        /// How it exited.
        status: ExitStatus,
        /// What it wrote to standard error, trimmed.
        stderr: String,
    },
    /// The command answered what the caller does not read: not the JSON, the
    /// number or the line it parses.
    Unread
    {
        /// The invocation.
        invocation: Invocation,
        /// What the caller could not read, and why.
        detail: String,
    },
}

impl GitHubError
{
    /// The refusal of `command`'s answer, which the caller could not read
    /// for `detail`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the refusal names the invocation and the detail; a
    ///   dropped argument or a lost detail changes the asserted line.
    /// - witness: `error::tests::every_refusal_names_its_invocation`
    #[inline]
    #[must_use]
    pub fn unread(
        command: &Command,
        detail: String,
    ) -> Self
    {
        Self::Unread {
            invocation: Invocation::from(command),
            detail,
        }
    }
}

impl fmt::Display for GitHubError
{
    /// Names the invocation and why it failed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line, `` `<invocation>` failed: <detail> ``, the
    ///   detail of an exit its status and its standard error.
    /// - provides: the message every workflow binary prints for a failed `gh`.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant's rendering names its invocation and
    ///   its detail; a dropped field or a swapped variant changes the asserted
    ///   line.
    /// - witness: `error::tests::every_refusal_names_its_invocation`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unstarted {
                ref invocation,
                ref detail,
            }
            | Self::Unread {
                ref invocation,
                ref detail,
            } => write!(f, "`{invocation}` failed: {detail}"),
            Self::Exited {
                ref invocation,
                status,
                ref stderr,
            } => write!(f, "`{invocation}` failed: {status}: {stderr}"),
        }
    }
}

/// A refusal is an error value, so a binary can report it.
impl core::error::Error for GitHubError
{
}

#[cfg(test)]
mod tests
{
    use std::process::Command;

    use super::GitHubError;
    use crate::Invocation;

    #[test]
    fn every_refusal_names_its_invocation()
    {
        let mut command = Command::new("gh");
        let _listing = command.args(["issue", "list", "--json", "number,title"]);
        assert_eq!(
            GitHubError::Unstarted {
                invocation: Invocation::from(&command),
                detail: String::from("No such file or directory (os error 2)"),
            }
            .to_string(),
            "`gh issue list --json number,title` failed: No such file or directory (os error 2)"
        );
        assert_eq!(
            GitHubError::unread(&command, String::from("expected value at line 1 column 1"))
                .to_string(),
            "`gh issue list --json number,title` failed: expected value at line 1 column 1"
        );
    }

    #[cfg(unix)]
    #[test]
    fn an_exit_names_its_status_and_standard_error()
    {
        use std::os::unix::process::ExitStatusExt as _;

        let command = Command::new("gh");
        assert_eq!(
            GitHubError::Exited {
                invocation: Invocation::from(&command),
                status: std::process::ExitStatus::from_raw(256),
                stderr: String::from("HTTP 401: Bad credentials"),
            }
            .to_string(),
            "`gh` failed: exit status: 1: HTTP 401: Bad credentials"
        );
    }
}
