//! **GitHub's boundary**: the one place a workflow crate runs `gh` and turns
//! its failure into a refusal. The lane budget, the hotpath guard, the
//! coverage guard and the test timings each read GitHub through `gh`; each
//! builds its own invocation, and every one of them runs it here.
//!
//! - [`run`] starts an invocation, feeds it a body when asked, and returns what
//!   it wrote to standard output.
//! - [`Site`] declares one call site of `gh`: the scope that holds it and its
//!   verb, on one line that the check of the API budget reads. A call builds
//!   the words of its verb from its site.
//! - [`GitHubError`] is the one error family: the invocation did not start,
//!   exited unsuccessfully, or answered what its caller does not read.
//!
//! What each crate asks GitHub stays with that crate. The lane budget lists
//! the landing-checks workflow's runs through `gh api` and files one issue that
//! it opens, reopens and closes; the test timings list merge-queue runs through
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

/// One call site of `gh`: the scope that holds the call and the verb of the
/// call, as `.config/gh/sites.awk` prints them and `calls.toml` prices them.
///
/// A site stands on one line of the file that makes the call, as
/// `const NAME: Site = Site::new("<scope>", "<verb>");`. The check of the
/// budget reads each such line of a Rust file of a workflow crate, and one
/// line is one call. The call takes the words of its verb from [`Site::words`],
/// so no call of `gh` has another verb than its line.
///
/// # Specification
/// - provides: the price of a call of `gh` that a Rust crate makes, read from
///   the declared line and never from the call's own text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Site
{
    /// The function that makes the call.
    scope: &'static str,
    /// The verb: a command and its first word, as `pr view`; `api graphql`;
    /// or `api` and the method of a REST call, as `api GET`.
    verb: &'static str,
}

impl Site
{
    /// The site of the call in `scope` with `verb`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the words of a REST site and of a command site; a
    ///   site that drops its verb gives no words.
    /// - witness: `tests::a_site_gives_the_words_of_its_verb`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            primitive_signature,
            reason = "the declared line of a site names its scope and its verb as two literals in a `const`, and a `const` takes no `From`"
        )
    )]
    pub const fn new(
        scope: &'static str,
        verb: &'static str,
    ) -> Self
    {
        Self { scope, verb }
    }

    /// The function that makes the call.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the scope names the row of the call, and the check of
    ///   the budget reads it from the line; a call reads no scope.
    /// - witness: `tests::a_site_gives_the_words_of_its_verb`
    #[inline]
    #[must_use]
    pub const fn scope(&self) -> Word
    {
        Word(self.scope)
    }

    /// The words of the verb as the first arguments of `gh`: `api` and
    /// `--method` with the method of a REST site, and each word of another
    /// verb.
    ///
    /// # Specification
    /// - requires: the verb is one that `sites.awk` prints.
    /// - ensures: for `api` and a method in upper case, `api`, `--method` and
    ///   the method. For each other verb, its words in their order.
    /// - provides: a call whose verb is the verb of its line.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the outcome is a value.
    ///
    /// # Cost
    /// - allocation: the words, setup
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a REST site, a GraphQL site and a command site; a
    ///   REST verb given as its words asks `gh` for a method as an endpoint.
    /// - witness: `tests::a_site_gives_the_words_of_its_verb`
    #[inline]
    #[must_use]
    pub fn words(&self) -> Vec<Word>
    {
        match self.verb.split_once(' ') {
            Some(("api", method)) if method.bytes().all(|byte| byte.is_ascii_uppercase()) => {
                vec![Word("api"), Word("--method"), Word(method)]
            },
            _ => self.verb.split(' ').map(Word).collect(),
        }
    }
}

/// One word of a declared site: its scope, or one word of the arguments of its
/// verb.
///
/// # Specification
/// - provides: a word that comes from a declared line and no other text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Word(&'static str);

impl From<Word> for &'static str
{
    /// The text of `word`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the words of a REST site; a text that is not the
    ///   word's changes the asserted words.
    /// - witness: `tests::a_site_gives_the_words_of_its_verb`
    #[inline]
    fn from(word: Word) -> Self
    {
        word.0
    }
}

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
    use super::Site;
    use super::read;
    use super::run;

    #[test]
    fn a_site_gives_the_words_of_its_verb()
    {
        let text = |site: Site| -> Vec<&'static str> {
            site.words().into_iter().map(<&str>::from).collect()
        };
        let rest = Site::new("signers", "api GET");
        assert_eq!(<&str>::from(rest.scope()), "signers");
        assert_eq!(text(rest), ["api", "--method", "GET"]);
        assert_eq!(text(Site::new("graph", "api graphql")), ["api", "graphql"]);
        assert_eq!(text(Site::new("view", "pr view")), ["pr", "view"]);
    }

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
