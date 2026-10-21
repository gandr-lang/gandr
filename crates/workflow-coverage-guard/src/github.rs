//! The one issue a drop files, through `gh`, which resolves the repository
//! from `GH_REPO` or the checkout.

use core::fmt;
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

use serde::Deserialize;

use crate::error::GuardError;
use crate::report::Comparison;
use crate::report::Standing;
use crate::report::TITLE_PREFIX;

/// The labels a new issue is opened with: a defect of CI, which triage picks
/// up.
const LABELS: [&str; 2] = ["kind:defect", "area:ci"];

/// An issue's number in the repository.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IssueNumber(u64);

impl fmt::Display for IssueNumber
{
    /// Writes `#` and the number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "#{}", self.0)
    }
}

/// What filing the comparison did.
///
/// # Specification
/// - provides: the line the binary prints after the report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Filed
{
    /// The coverage dropped and no drop issue was open: one was opened, at
    /// the address `gh` printed.
    Opened(String),
    /// The coverage dropped and a drop issue was open: its title and body
    /// now state this drop.
    Updated(IssueNumber),
    /// The coverage held: no issue was read or written.
    Untouched,
}

impl fmt::Display for Filed
{
    /// Writes one sentence naming the action and the issue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Opened(ref url) => write!(f, "Opened {url}."),
            Self::Updated(number) => write!(f, "Updated {number}."),
            Self::Untouched => f.write_str("Coverage held; no issue filed."),
        }
    }
}

/// One issue as `gh issue list --json number,title` prints it.
#[derive(Debug, Deserialize)]
struct Listed
{
    /// The issue's number.
    number: u64,
    /// The issue's title.
    title: String,
}

/// What a `gh` invocation reads on standard input.
#[derive(Clone, Copy, Debug)]
enum Feed<'report>
{
    /// Nothing: standard input stays the parent's.
    Nothing,
    /// The comparison, as the issue body `--body-file -` reads.
    Body(&'report Comparison),
}

/// Runs `command`, feeding it `feed` on standard input, and returns what it
/// wrote to standard output.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the command's standard output, read as UTF-8 with any invalid
///   sequence replaced.
/// - provides: the one place a `gh` invocation's failure becomes a refusal.
/// - fails: [`GuardError::Gh`], naming the invocation, when the command cannot
///   start, its input cannot be written, or it exits unsuccessfully; the
///   message is its standard error.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` that succeeds, one that fails with a message,
///   and one that records the body it was fed; a swallowed exit status, a lost
///   message or an unfed body changes the observed result.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
fn run(
    command: &mut Command,
    feed: Feed<'_>,
) -> Result<String, GuardError>
{
    let label = format!("{command:?}");
    let refuse = |message: String| GuardError::Gh {
        command: label.clone(),
        message,
    };
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Feed::Body(_) = feed {
        command.stdin(Stdio::piped());
    }
    let mut child = command.spawn().map_err(|error| refuse(error.to_string()))?;
    if let (Feed::Body(comparison), Some(mut stdin)) = (feed, child.stdin.take()) {
        stdin
            .write_all(comparison.to_string().as_bytes())
            .map_err(|error| refuse(error.to_string()))?;
    }
    let output = child
        .wait_with_output()
        .map_err(|error| refuse(error.to_string()))?;
    if !output.status.success() {
        return Err(refuse(format!(
            "{}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Files `comparison` on the one open drop issue: opened when none is open,
/// retitled and rewritten when one is; nothing when the coverage held.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository with
///   permission to write issues.
/// - ensures: when the comparison stands [`Standing::Dropped`], the open issue
///   whose title starts with [`TITLE_PREFIX`] carries its title and body,
///   opened labelled `kind:defect` and `area:ci` if none was open; when it
///   stands [`Standing::Steady`], no `gh` invocation runs.
/// - provides: one open drop issue per repository, never one per night; a
///   closed one is history and stays closed.
/// - fails: [`GuardError::Gh`] when a `gh` invocation fails or the listing is
///   not the JSON this crate reads.
/// - panics: none.
/// - executable: none — the outcome is the repository's issue state.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` holding no drop issue, an open one beside an
///   unrelated one, and a steady comparison; opening a second issue, editing
///   the unrelated one or touching any issue while steady changes the recorded
///   invocations.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_second_drop_updates_the_open_issue`
/// - witness: `tests::cli::a_steady_upload_files_nothing`
#[inline]
pub fn file(comparison: &Comparison) -> Result<Filed, GuardError>
{
    if comparison.standing() == Standing::Steady {
        return Ok(Filed::Untouched);
    }
    let title = comparison.title().to_string();
    let mut list = Command::new("gh");
    list.args([
        "issue",
        "list",
        "--state",
        "open",
        "--limit",
        "100",
        "--search",
        &format!("\"{}\" in:title", TITLE_PREFIX.trim_end()),
        "--json",
        "number,title",
    ]);
    let listing = run(&mut list, Feed::Nothing)?;
    let issues: Vec<Listed> = serde_json::from_str(&listing).map_err(|error| GuardError::Gh {
        command: format!("{list:?}"),
        message: error.to_string(),
    })?;
    if let Some(issue) = issues
        .into_iter()
        .find(|issue| issue.title.starts_with(TITLE_PREFIX))
    {
        run(
            Command::new("gh").args([
                "issue",
                "edit",
                &issue.number.to_string(),
                "--title",
                &title,
                "--body-file",
                "-",
            ]),
            Feed::Body(comparison),
        )?;
        return Ok(Filed::Updated(IssueNumber(issue.number)));
    }
    let mut create = Command::new("gh");
    create.args(["issue", "create", "--title", &title, "--body-file", "-"]);
    for label in LABELS {
        create.args(["--label", label]);
    }
    let url = run(&mut create, Feed::Body(comparison))?;
    Ok(Filed::Opened(url.trim().to_owned()))
}
