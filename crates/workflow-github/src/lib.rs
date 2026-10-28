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
use core::time::Duration;
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

/// How many times [`read`] runs an invocation GitHub answers with a server
/// error before it refuses: a transient error is read past, and a lasting one
/// still fails the read.
const READ_ATTEMPTS: usize = 3;

/// What `gh` writes to standard error when GitHub answers with a server
/// error, as in `gh: Server Error (HTTP 502)`.
const SERVER_ERROR: &str = "(HTTP 5";

/// The pause [`read`] takes after a server error before running the
/// invocation again.
pub const READ_PAUSE: Duration = Duration::from_secs(2);

/// Runs the read-only invocation `command` as [`run`] does, and runs it again
/// after `pause` while GitHub answers it with a server error (`HTTP 5xx`),
/// for at most three attempts in all.
///
/// A write is never given to `read`: running it again could repeat it.
///
/// # Specification
/// - requires: `command` only reads.
/// - ensures: the first answer of up to three attempts; an attempt that exits
///   with a server error is followed by another, and every other outcome is
///   returned as it is.
/// - provides: the reads a night makes surviving one transient server error.
/// - fails: as [`run`]: the first failure that is not a server error, or the
///   third attempt's server error.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — an invocation answering after one server error, one
///   refused with a client error, and one refused with a server error every
///   time; a missing retry, a retried client error or a fourth attempt changes
///   the attempts counted.
/// - witness: `tests::a_server_error_is_read_again_3492`
/// - witness: `tests::a_client_error_is_refused_at_once`
/// - witness: `tests::a_lasting_server_error_is_refused_after_three_attempts`
#[inline]
pub fn read(
    command: &mut Command,
    pause: Duration,
) -> Result<String, GitHubError>
{
    for _ in 1 .. READ_ATTEMPTS {
        match run(command, Feed::Nothing) {
            Err(GitHubError::Exited { ref stderr, .. }) if stderr.contains(SERVER_ERROR) => {
                std::thread::sleep(pause);
            },
            answer => return answer,
        }
    }
    run(command, Feed::Nothing)
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;
    use std::process::Command;

    use super::Body;
    use super::Feed;
    use super::GitHubError;
    use super::read;
    use super::run;

    /// An emptied counter file of its own for the test named `$name`.
    macro_rules! counter {
        ($name:literal) => {{
            let path = std::env::temp_dir().join(format!(
                "gandr-workflow-github-{}-{}",
                std::process::id(),
                $name
            ));
            let _absent = std::fs::remove_file(&path);
            path
        }};
    }

    /// A `sh` command that counts its attempts in the file `$count` and
    /// fails, writing `$stderr`, until its attempt `$answers_at`, then
    /// answers `answered`.
    macro_rules! flaky {
        ($count:expr, $stderr:literal, $answers_at:literal) => {{
            let mut command = Command::new("sh");
            command.args([
                "-c",
                r#"echo x >> "$0"; n=$(wc -l < "$0"); if [ "$n" -lt "$2" ]; then echo "$1" >&2; exit 1; fi; echo answered"#,
                &$count.to_string_lossy(),
                $stderr,
                $answers_at,
            ]);
            command
        }};
    }

    /// How many attempts the counter file `$count` holds.
    macro_rules! attempts {
        ($count:expr) => {
            std::fs::read_to_string(&$count)
                .expect("the command counted its attempts")
                .lines()
                .count()
        };
    }

    #[cfg(unix)]
    #[test]
    fn a_server_error_is_read_again_3492()
    {
        let count = counter!("server-once");
        let answer = read(
            &mut flaky!(count, "gh: Server Error (HTTP 502)", "2"),
            Duration::ZERO,
        );
        assert_eq!(answer, Ok(String::from("answered\n")), "#3492");
        assert_eq!(attempts!(count), 2);
    }

    #[cfg(unix)]
    #[test]
    fn a_client_error_is_refused_at_once()
    {
        let count = counter!("client");
        let answer = read(
            &mut flaky!(count, "gh: Not Found (HTTP 404)", "9"),
            Duration::ZERO,
        );
        assert!(
            matches!(answer, Err(GitHubError::Exited { ref stderr, .. }) if stderr == "gh: Not Found (HTTP 404)"),
            "{answer:?}"
        );
        assert_eq!(attempts!(count), 1);
    }

    #[cfg(unix)]
    #[test]
    fn a_lasting_server_error_is_refused_after_three_attempts()
    {
        let count = counter!("server-lasting");
        let answer = read(
            &mut flaky!(count, "gh: Server Error (HTTP 503)", "9"),
            Duration::ZERO,
        );
        assert!(
            matches!(answer, Err(GitHubError::Exited { ref stderr, .. }) if stderr == "gh: Server Error (HTTP 503)"),
            "{answer:?}"
        );
        assert_eq!(attempts!(count), 3, "#3492");
    }

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
