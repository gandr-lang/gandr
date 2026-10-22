//! A commit's checks and pull request, and each regressed function's issue,
//! through `gh`, which resolves the repository of an `issue` command from
//! `GH_REPO` or the checkout.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::check::CommitSha;
use crate::check::Concluded;
use crate::check::CrateDir;
use crate::check::Listed;
use crate::check::Repository;
use crate::check::SiteName;
use crate::check::Unstated;
use crate::error::GuardError;
use crate::index::Comment;
use crate::index::CommentUrl;
use crate::index::Index;
use crate::index::IssueBody;
use crate::index::IssueTitle;
use crate::index::KIND;
use crate::index::Run;
use crate::index::Standing;
use crate::index::Unposted;
use crate::report::ListedPull;
use crate::report::Pull;
use crate::report::Regression;
use crate::report::Report;
use crate::report::Unpulled;
use crate::report::pull_of;

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

/// What filing did to one function's issue.
///
/// # Specification
/// - provides: a line the binary prints after the report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Filed
{
    /// The function had no issue: one was opened, at the address `gh`
    /// printed, and closed again when its one row is settled.
    Opened(IssueTitle, String, Standing),
    /// The function's issue now states this run, and stands open or was
    /// closed as its rows stand.
    Updated(IssueNumber, Standing),
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
        let state = |standing: Standing| match standing {
            Standing::Open => "open",
            Standing::Settled => "closed",
        };
        match *self {
            Self::Opened(ref title, ref url, standing) => {
                write!(f, "Opened {url} ({title}), {}.", state(standing))
            },
            Self::Updated(number, standing) => write!(f, "Updated {number}, {}.", state(standing)),
        }
    }
}

/// One issue as `gh issue list --json number,title,state,body` prints it.
#[derive(Debug, Deserialize)]
struct ListedIssue
{
    /// The issue's number.
    number: u64,
    /// The issue's title.
    title: IssueTitle,
    /// `OPEN` or `CLOSED`.
    state: String,
    /// The issue's body.
    #[serde(default)]
    body: IssueBody,
}

/// What a `gh` invocation reads on standard input.
#[derive(Clone, Copy, Debug)]
enum Feed<'text>
{
    /// Nothing: standard input stays the parent's.
    Nothing,
    /// A comment's report, as `--body-file -` reads it.
    Report(&'text Report),
    /// An issue's index, as `--body-file -` reads it.
    Index(&'text Index),
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
/// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
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
    let text = match feed {
        Feed::Nothing => None,
        Feed::Report(report) => Some(report.to_string()),
        Feed::Index(index) => Some(index.to_string()),
    };
    if text.is_some() {
        command.stdin(Stdio::piped());
    }
    let mut child = command.spawn().map_err(|error| refuse(error.to_string()))?;
    if let (Some(text), Some(mut stdin)) = (text, child.stdin.take()) {
        stdin
            .write_all(text.as_bytes())
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

/// The concluded `hotpath / <benchmark>` checks of `sha`.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: every completed `hotpath / ` check of the commit whose conclusion
///   is `failure` or `success`, in the order GitHub lists them, each read by
///   [`Listed::concluded`]; every page of the listing is read.
/// - provides: the checks a report is made of, all of them at once, so each
///   benchmark's event files the same rows.
/// - fails: [`GuardError::Gh`] when the query fails or a line it prints is not
///   the JSON this crate reads.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a commit whose listing holds two failed hotpath checks, a
///   passing one, a pending one and a failed check of another name; reading the
///   pending or foreign one changes the report.
/// - witness: `tests::cli::only_a_completed_failed_hotpath_check_is_filed`
#[inline]
pub fn checks(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Vec<Concluded>, GuardError>
{
    let mut query = Command::new("gh");
    query.args([
        "api",
        "--paginate",
        &format!("repos/{repository}/commits/{sha}/check-runs?per_page=100"),
        "--jq",
        ".check_runs[] | {name, status, conclusion, html_url, summary: (.output.summary // \"\")}",
    ]);
    let listing = run(&mut query, Feed::Nothing)?;
    let mut concluded = Vec::new();
    for line in listing.lines().filter(|line| !line.trim().is_empty()) {
        let listed: Listed = serde_json::from_str(line).map_err(|error| GuardError::Gh {
            command: format!("{query:?}"),
            message: error.to_string(),
        })?;
        if let Maybe::Present(check) = listed.concluded() {
            concluded.push(check);
        }
    }
    Ok(concluded)
}

/// The pull request `sha` names.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: the pull request GitHub associates with the commit that it heads,
///   else the first it lists; absent when it lists none.
/// - provides: the subject of the rows.
/// - fails: [`GuardError::Gh`] when the query fails or prints what this crate
///   does not read.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a commit a pull request heads and one none carries;
///   inventing a pull request or losing one changes the rows' subject.
/// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
/// - witness: `tests::cli::a_commit_without_a_pull_request_is_filed_by_its_sha`
#[inline]
pub fn pull(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Maybe<Pull, Unpulled>, GuardError>
{
    let mut query = Command::new("gh");
    query.args(["api", &format!("repos/{repository}/commits/{sha}/pulls")]);
    let answer = run(&mut query, Feed::Nothing)?;
    let listed: Vec<ListedPull> =
        serde_json::from_str(&answer).map_err(|error| GuardError::Gh {
            command: format!("{query:?}"),
            message: error.to_string(),
        })?;
    Ok(pull_of(sha, listed))
}

/// One function's issue as filing finds it and leaves it.
#[derive(Debug)]
struct Touched
{
    /// The issue's number and whether it stood open, when it exists.
    issue: Maybe<(IssueNumber, Standing), Unstated>,
    /// The crate the function lives in, for the area label.
    krate: Maybe<CrateDir, Unstated>,
    /// Its index, as this run leaves it.
    index: Index,
    /// The report owed as a comment.
    comment: Comment,
}

/// Files `report` on each regressed function's issue: rows recorded, comments
/// appended where owed, open rows of passing series marked fixed, and each
/// issue closed or reopened as its rows stand.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository with
///   permission to write issues.
/// - ensures: when the report holds no failed and no passed check, no `gh`
///   invocation runs. Otherwise the `kind:performance` issues are listed once;
///   each function a failed check regressed has the issue titled `perf:
///   <function>`, opened when it had none, carrying its row (see
///   [`Index::record`]), with the report appended first as a comment when
///   [`Index::owes`] says one is owed, except that a function whose every
///   regression the pull request's body accepts opens no issue; each function
///   with an open row of the report's subject in a passing series has that row
///   marked fixed, unless a failed check of the same series regressed the
///   function; each touched issue is closed when it stands settled and was
///   open, reopened when it stands open and was closed.
/// - provides: one issue per function, its body the index of its regressions.
/// - fails: [`GuardError::Gh`] when a `gh` invocation fails or the listing is
///   not the JSON this crate reads.
/// - panics: none.
/// - executable: none — the outcome is the repository's issue state.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` holding no issue, one holding a function's
///   issue with the pull request's open row, a passing rerun, a shift, a
///   settled issue meeting a new regression, a series both failed and passed,
///   and an accepted landing with and without its function's issue; a second
///   issue, a comment per rerun, an open row left after the pass, a regressed
///   row fixed, an issue opened for an acceptance, or an issue left in the
///   wrong state changes the recorded invocations.
/// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
/// - witness: `tests::cli::a_later_run_updates_its_row_without_a_comment`
/// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
/// - witness: `tests::cli::a_uniform_shift_is_a_runner_shift_row_without_a_comment`
/// - witness: `tests::cli::a_new_regression_reopens_a_settled_issue`
/// - witness: `tests::cli::a_clear_commit_files_nothing`
/// - witness: `tests::cli::a_benchmark_both_failed_and_passed_fixes_only_the_rows_it_did_not_regress`
/// - witness: `tests::cli::a_landing_with_an_accepted_verdict_files_no_issue`
/// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
/// - witness: `tests::cli::an_unaccepted_benchmark_beside_an_accepted_one_still_files`
#[inline]
pub fn file(report: &Report) -> Result<Vec<Filed>, GuardError>
{
    let regressions = report.regressions();
    if regressions.is_empty() && report.passed().is_empty() {
        return Ok(Vec::new());
    }
    let mut list = Command::new("gh");
    list.args([
        "issue",
        "list",
        "--state",
        "all",
        "--label",
        KIND,
        "--limit",
        "1000",
        "--json",
        "number,title,state,body",
    ]);
    let listing = run(&mut list, Feed::Nothing)?;
    let issues: Vec<ListedIssue> =
        serde_json::from_str(&listing).map_err(|error| GuardError::Gh {
            command: format!("{list:?}"),
            message: error.to_string(),
        })?;
    let subject = report.subject();
    let regressed = report.regressed();
    let at = Run {
        repository: report.repository(),
        sha: report.sha(),
        subject: &subject,
        regressed: &regressed,
    };
    let found = |function: &SiteName| {
        let title = IssueTitle::of(function);
        issues.iter().find(|issue| issue.title == title)
    };
    let mut touched: BTreeMap<SiteName, Touched> = BTreeMap::new();
    let open = |function: &SiteName, krate: &Maybe<CrateDir, Unstated>| {
        found(function).map_or_else(
            || Touched {
                issue: Maybe::Absent(Unstated),
                krate: krate.clone(),
                index: Index::new(function, krate),
                comment: Comment::Unowed,
            },
            |issue| Touched {
                issue: Maybe::Present((
                    IssueNumber(issue.number),
                    if issue.state == "OPEN" {
                        Standing::Open
                    }
                    else {
                        Standing::Settled
                    },
                )),
                krate: krate.clone(),
                index: Index::read(&issue.body),
                comment: Comment::Unowed,
            },
        )
    };
    for regression in &regressions {
        // A settled acceptance is recorded where an issue stands, and opens
        // none: the verdict obligation already recorded it on the pull request.
        if matches!(regression.accepted, Maybe::Present(_))
            && !touched.contains_key(&regression.function)
            && found(&regression.function).is_none()
        {
            continue;
        }
        let entry = touched
            .entry(regression.function.clone())
            .or_insert_with(|| open(&regression.function, &regression.krate));
        if entry.index.owes(&subject, regression, &regressed) == Comment::Owed {
            entry.comment = Comment::Owed;
        }
    }
    for issue in &issues {
        let Some(function) = issue.title.function()
        else {
            continue;
        };
        let index = Index::read(&issue.body);
        // A function a failed check regressed is touched already; its own
        // filing keeps that series' row open.
        let owed = report
            .passed()
            .keys()
            .any(|series| index.standing_in(&subject, series) == Standing::Open);
        if owed {
            touched
                .entry(function.clone())
                .or_insert_with(|| open(&function, &Maybe::Absent(Unstated)));
        }
    }
    let mut filed = Vec::new();
    for (function, entry) in touched {
        filed.push(file_function(&function, entry, report, &regressions, &at)?);
    }
    Ok(filed)
}

/// Files the run on `function`'s issue, as [`file()`] states for each touched
/// function: rows recorded and fixed, the issue opened if it had none, the
/// report commented when owed, the body written, and the issue closed or
/// reopened as its rows stand.
///
/// # Specification
/// - requires: `entry` is `function`'s issue as listed, and `regressions` the
///   report's.
/// - ensures: as [`file()`] states for one function.
/// - provides: the filing of one issue.
/// - fails: [`GuardError::Gh`] when a `gh` invocation fails, or `gh issue
///   create` prints no issue's address.
/// - panics: none.
/// - executable: none — the outcome is the repository's issue state.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`file()`].
/// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
/// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
/// - witness: `tests::cli::a_new_regression_reopens_a_settled_issue`
/// - witness: `tests::cli::a_benchmark_both_failed_and_passed_fixes_only_the_rows_it_did_not_regress`
fn file_function(
    function: &SiteName,
    mut entry: Touched,
    report: &Report,
    regressions: &[Regression],
    at: &Run<'_>,
) -> Result<Filed, GuardError>
{
    let unposted = Maybe::Absent(Unposted);
    let own = || {
        regressions
            .iter()
            .filter(|regression| &regression.function == function)
    };
    for regression in own() {
        entry.index.record(regression, at, &unposted);
    }
    for (series, passing) in report.passed() {
        if !own().any(|regression| &regression.series == series) {
            entry.index.fix(series, passing, at);
        }
    }
    let (number, was, opened) = match entry.issue {
        Maybe::Present((number, was)) => (number, was, None),
        Maybe::Absent(_) => {
            let title = IssueTitle::of(function);
            let mut create = Command::new("gh");
            create.args([
                "issue",
                "create",
                "--title",
                &title.to_string(),
                "--body-file",
                "-",
            ]);
            for label in labels(&entry.krate) {
                create.args(["--label", &label]);
            }
            let url = run(&mut create, Feed::Index(&entry.index))?
                .trim()
                .to_owned();
            let number = url
                .rsplit('/')
                .next()
                .and_then(|tail| tail.parse::<u64>().ok())
                .ok_or_else(|| GuardError::Gh {
                    command: format!("{create:?}"),
                    message: format!("printed `{url}`, not an issue's address"),
                })?;
            (IssueNumber(number), Standing::Open, Some((title, url)))
        },
    };
    let number_text = number.0.to_string();
    if entry.comment == Comment::Owed {
        let mut post = Command::new("gh");
        post.args(["issue", "comment", &number_text, "--body-file", "-"]);
        let posted = Maybe::Present(
            run(&mut post, Feed::Report(report))?
                .trim()
                .parse::<CommentUrl>()
                .unwrap_or_else(|never| match never {}),
        );
        for regression in own() {
            entry.index.record(regression, at, &posted);
        }
    }
    if opened.is_none() || entry.comment == Comment::Owed {
        let mut edit = Command::new("gh");
        edit.args(["issue", "edit", &number_text, "--body-file", "-"]);
        for label in labels(&entry.krate) {
            edit.args(["--add-label", &label]);
        }
        run(&mut edit, Feed::Index(&entry.index))?;
    }
    let standing = entry.index.standing();
    let verb = match (was, standing) {
        (Standing::Open, Standing::Settled) => Some("close"),
        (Standing::Settled, Standing::Open) => Some("reopen"),
        (Standing::Open, Standing::Open) | (Standing::Settled, Standing::Settled) => None,
    };
    if let Some(verb) = verb {
        run(
            Command::new("gh").args(["issue", verb, &number_text]),
            Feed::Nothing,
        )?;
    }
    Ok(match opened {
        Some((title, url)) => Filed::Opened(title, url, standing),
        None => Filed::Updated(number, standing),
    })
}

/// The labels a function's issue carries: [`KIND`], and its crate's area when
/// the crate is known.
///
/// # Specification
/// trivial.
fn labels(krate: &Maybe<CrateDir, Unstated>) -> Vec<String>
{
    let area = match *krate {
        Maybe::Present(ref krate) => match krate.area() {
            Maybe::Present(area) => Some(area.to_string()),
            Maybe::Absent(_) => None,
        },
        Maybe::Absent(_) => None,
    };
    core::iter::once(KIND.to_owned()).chain(area).collect()
}
