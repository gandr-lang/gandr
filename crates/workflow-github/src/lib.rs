//! **GitHub's boundary**: the one place a workflow crate runs `gh` and turns
//! its failure into a refusal. The lane budget, the hotpath guard, the
//! coverage guard and the test timings each read GitHub through `gh`; each
//! builds its own invocation, and every one of them runs it here.
//!
//! - [`run`] starts an invocation, feeds it a body when asked, and returns what
//!   it wrote to standard output.
//! - [`GitHubError`] is the one error family: the invocation did not start,
//!   exited unsuccessfully, or answered what its caller does not read.
//!
//! What each crate asks GitHub stays with that crate. The lane budget lists
//! the CI workflow's runs through `gh api` and files one issue that it opens,
//! reopens and closes; the test timings list merge-queue runs through
//! `gh run list` and download their reports; the hotpath guard files one
//! issue per function and edits its comments; the coverage guard edits one
//! open issue. Those are four policies over one runner.

pub mod error;

use core::fmt;
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

pub use crate::error::GitHubError;

/// An invocation as a shell spells it: the program and its arguments,
/// separated by spaces.
///
/// # Specification
/// - provides: the name a refusal gives the command it refused.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Invocation(String);

impl From<&Command> for Invocation
{
    /// The invocation `command` makes.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal's line names the program and every argument
    ///   in order, so a dropped or reordered argument changes it.
    /// - witness: `error::tests::every_refusal_names_its_invocation`
    #[inline]
    fn from(command: &Command) -> Self
    {
        Self(
            core::iter::once(command.get_program())
                .chain(command.get_args())
                .map(|part| part.to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join(" "),
        )
    }
}

impl fmt::Display for Invocation
{
    /// Writes the invocation as a shell spells it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Invocation::from`].
    /// - witness: `error::tests::every_refusal_names_its_invocation`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The text an invocation reads as a body on standard input, as
/// `--body-file -` and `-F body=@-` read it.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Body(String);

impl From<String> for Body
{
    /// The body `text`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fed body is what the command reads back, so an
    ///   emptied body changes the answer.
    /// - witness: `tests::a_fed_body_is_read_on_standard_input`
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

/// What an invocation reads on standard input.
///
/// # Specification
/// - provides: the two inputs an invocation takes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Feed
{
    /// Nothing: standard input stays the parent's.
    Nothing,
    /// A body, written whole before the answer is read.
    Body(Body),
}

/// Runs `command`, feeding it `feed` on standard input, and returns what it
/// wrote to standard output.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the command's standard output, read as UTF-8 with any invalid
///   sequence replaced.
/// - provides: the one place a `gh` invocation's failure becomes a refusal.
/// - fails: [`GitHubError::Unstarted`] when the command cannot start, its input
///   cannot be written, or it cannot be waited for; [`GitHubError::Exited`]
///   when it exits unsuccessfully, with its standard error.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a command that succeeds, one that fails with a message,
///   one that is not there, and one that reads back the body it was fed; a
///   swallowed exit status, a lost message or an unfed body changes the
///   observed result.
/// - witness: `tests::a_fed_body_is_read_on_standard_input`
/// - witness: `tests::a_failing_command_is_refused_with_its_message`
/// - witness: `tests::a_missing_program_is_refused_as_unstarted`
#[inline]
pub fn run(
    command: &mut Command,
    feed: Feed,
) -> Result<String, GitHubError>
{
    let invocation = Invocation::from(&*command);
    let unstarted = |error: std::io::Error| GitHubError::Unstarted {
        invocation: invocation.clone(),
        detail: error.to_string(),
    };
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Feed::Body(_) = feed {
        command.stdin(Stdio::piped());
    }
    let mut child = command.spawn().map_err(unstarted)?;
    if let (Feed::Body(Body(text)), Some(mut stdin)) = (feed, child.stdin.take()) {
        stdin.write_all(text.as_bytes()).map_err(unstarted)?;
    }
    let output = child.wait_with_output().map_err(unstarted)?;
    if !output.status.success() {
        return Err(GitHubError::Exited {
            invocation,
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

#[cfg(test)]
mod tests
{
    use std::process::Command;

    use super::Body;
    use super::Feed;
    use super::GitHubError;
    use super::run;

    #[cfg(unix)]
    #[test]
    fn a_fed_body_is_read_on_standard_input()
    {
        let answer = run(
            Command::new("sh").args(["-c", "cat"]),
            Feed::Body(Body::from(String::from("the report\n"))),
        );
        assert_eq!(answer, Ok(String::from("the report\n")));
        let unfed = run(
            Command::new("sh").args(["-c", "echo listed"]),
            Feed::Nothing,
        );
        assert_eq!(unfed, Ok(String::from("listed\n")));
    }

    #[cfg(unix)]
    #[test]
    fn a_failing_command_is_refused_with_its_message()
    {
        let refused = run(
            Command::new("sh").args(["-c", "echo 'HTTP 401: Bad credentials' >&2; exit 1"]),
            Feed::Nothing,
        )
        .map_err(|error| error.to_string());
        assert_eq!(
            refused,
            Err(String::from(
                "`sh -c echo 'HTTP 401: Bad credentials' >&2; exit 1` failed: exit status: 1: \
                 HTTP 401: Bad credentials"
            ))
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_missing_program_is_refused_as_unstarted()
    {
        let refused = run(
            &mut Command::new("/nonexistent/gh"),
            Feed::Body(Body::from(String::from("unread"))),
        );
        assert!(
            matches!(refused, Err(GitHubError::Unstarted { .. })),
            "{refused:?}"
        );
    }
}
