//! The one issue a drop files, through `gh`, which resolves the repository
//! from `GH_REPO` or the checkout.

use core::fmt;
use std::process::Command;

use gandr_workflow_github::Body;
use gandr_workflow_github::Feed;
use gandr_workflow_github::GitHubError;
use gandr_workflow_github::READ_PAUSE;
use gandr_workflow_github::read;
use gandr_workflow_github::run;
use serde::Deserialize;

use crate::error::GuardError;
use crate::report::Comparison;
use crate::report::Standing;
use crate::report::TITLE_PREFIX;

/// The labels a new issue is opened with: a defect of CI, which triage picks
/// up, kept by the guard as a collector.
const LABELS: [&str; 3] = ["kind:defect", "area:ci", "collector"];

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

/// Files `comparison` on the one open drop issue: opened when none is open,
/// retitled and rewritten when one is; nothing when the coverage held.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository with
///   permission to write issues.
/// - ensures: when the comparison stands [`Standing::Dropped`], the open issue
///   whose title starts with [`TITLE_PREFIX`] carries its title and body,
///   opened labelled `kind:defect`, `area:ci` and `collector` if none was open,
///   and labelled `collector` when it was; when it stands [`Standing::Steady`],
///   no `gh` invocation runs.
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
    let listing = read(&mut list, READ_PAUSE)?;
    let issues: Vec<Listed> = serde_json::from_str(&listing)
        .map_err(|error| GitHubError::unread(&list, error.to_string()))?;
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
                "--add-label",
                "collector",
            ]),
            Feed::Body(Body::from(comparison.to_string())),
        )?;
        return Ok(Filed::Updated(IssueNumber(issue.number)));
    }
    let mut create = Command::new("gh");
    create.args(["issue", "create", "--title", &title, "--body-file", "-"]);
    for label in LABELS {
        create.args(["--label", label]);
    }
    let url = run(&mut create, Feed::Body(Body::from(comparison.to_string())))?;
    Ok(Filed::Opened(url.trim().to_owned()))
}
