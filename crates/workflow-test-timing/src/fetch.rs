//! Successful merge-queue runs of the CI workflow and their JUnit reports,
//! fetched with `gh` into a store with one directory per run.
//!
//! A run downloads into a scratch directory and is renamed into place once
//! complete, so an interrupted fetch leaves no partial run behind, and a run
//! already stored is never fetched again.

use core::fmt;
use core::num::NonZeroUsize;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use anodized::spec;

use crate::error::TimingError;
use crate::report::History;
use crate::report::Lane;
use crate::report::ReportText;
use crate::report::samples;

/// A workflow run's identifier; a later run has a greater one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RunId(u64);

impl From<u64> for RunId
{
    /// Reads `id` as a run identifier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: u64) -> Self
    {
        Self(id)
    }
}

impl fmt::Display for RunId
{
    /// Writes the identifier as a decimal number.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried number through `u64`'s rendering.
    /// - provides: the name of the run's directory in the store and the
    ///   argument `gh run download` takes.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fetched run is stored under its decimal identifier,
    ///   and a second report finds it there.
    /// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// The repository whose runs are read, as `OWNER/NAME`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Repository(String);

impl From<String> for Repository
{
    /// Adopts `name` as given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: String) -> Self
    {
        Self(name)
    }
}

/// How many of the latest runs a report reads; never zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunLimit(NonZeroUsize);

impl core::str::FromStr for RunLimit
{
    type Err = core::num::ParseIntError;

    /// Reads a positive decimal count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count `text` spells, when it is a positive integer.
    /// - provides: the `--runs` argument.
    /// - fails: the parse error of a non-number or of zero.
    /// - panics: none.
    /// - executable: none — the outcome is `NonZeroUsize`'s own parse.
    ///
    /// # Errors
    /// A [`core::num::ParseIntError`] for anything but a positive integer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `--runs 0` exits 2 and `--runs 2` reads two runs; a
    ///   limit that admitted zero or ignored the number changes either.
    /// - witness: `tests::cli::a_malformed_invocation_exits_two`
    /// - witness: `tests::cli::a_report_reads_the_newest_stored_runs`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl From<RunLimit> for usize
{
    /// The count as an iterator bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(limit: RunLimit) -> Self
    {
        limit.0.get()
    }
}

/// Runs `command` and returns what it wrote to standard output.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the command's standard output, read as UTF-8 with any invalid
///   sequence replaced.
/// - provides: the one place a `gh` invocation's failure is turned into a
///   refusal.
/// - fails: [`TimingError::Gh`], naming the invocation, when the command cannot
///   start or exits unsuccessfully; the message is its standard error.
/// - panics: none.
/// - executable: none — the outcome is the external process's; nothing in the
///   call's own state can check it.
///
/// # Errors
/// [`TimingError::Gh`] — the command did not start or did not succeed.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` that succeeds and one that fails with a
///   message; a swallowed exit status or a lost message changes the report or
///   the printed refusal.
/// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
fn output(command: &mut Command) -> Result<String, TimingError>
{
    let invocation = core::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|part| part.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(" ");
    let output = command.output().map_err(|error| TimingError::Gh {
        command: invocation.clone(),
        message: error.to_string(),
    })?;
    if !output.status.success() {
        return Err(TimingError::Gh {
            command: invocation,
            message: String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// The latest successful merge-queue runs of the CI workflow, newest first.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for `repository`.
/// - ensures: at most `limit` run identifiers, in the order `gh run list` gives
///   them.
/// - provides: the runs a report draws its samples from.
/// - fails: [`TimingError::Gh`] when `gh` fails or prints a line that is not a
///   run identifier.
/// - panics: none.
///
/// # Errors
/// [`TimingError::Gh`] — the listing failed or was not a list of numbers.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` listing two runs yields both, fetched in
///   turn; a fake that prints a non-number is refused.
/// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |runs| runs.len() <= usize::from(limit)))]
#[inline]
pub fn recent_runs(
    repository: &Repository,
    limit: RunLimit,
) -> Result<Vec<RunId>, TimingError>
{
    let mut command = Command::new("gh");
    command
        .args(["run", "list", "--repo", &repository.0])
        .args([
            "--workflow",
            "ci.yml",
            "--event",
            "merge_group",
            "--status",
            "success",
        ])
        .args(["--limit", &limit.0.to_string()])
        .args(["--json", "databaseId", "--jq", ".[].databaseId"]);
    let listing = output(&mut command)?;
    let mut runs = Vec::new();
    for line in listing.lines().take(limit.into()) {
        let id = line
            .trim()
            .parse::<u64>()
            .map_err(|error| TimingError::Gh {
                command: "gh run list".to_owned(),
                message: format!("`{line}` is not a run identifier: {error}"),
            })?;
        runs.push(RunId(id));
    }
    Ok(runs)
}

/// Whether a run was fetched now or was already in the store.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Stored
{
    /// The run was downloaded by this call.
    Fetched,
    /// The store already held it.
    Already,
}

/// Stores `run`'s JUnit reports under `store/<run>`, unless already stored.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for `repository`, when the run
///   is not stored yet.
/// - ensures: `store/<run>` holds the run's `junit-*` artifacts, each in a
///   directory named for the artifact; a partial download is never left under
///   that name.
/// - provides: [`Stored::Already`] without invoking `gh` when the directory
///   exists.
/// - fails: [`TimingError::Io`] when the store cannot be prepared or the
///   download renamed into place; [`TimingError::Gh`] when the download fails.
/// - panics: none.
///
/// # Errors
/// - [`TimingError::Io`] — the store could not be written.
/// - [`TimingError::Gh`] — `gh run download` failed.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` that writes reports, run twice: the second
///   report fetches nothing; a download left under a scratch name or repeated
///   for a stored run changes what the fake records.
/// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
#[spec(ensures: |ref ret| ret.is_err() || store.join(run.to_string()).is_dir())]
#[inline]
pub fn download(
    repository: &Repository,
    run: RunId,
    store: &Path,
) -> Result<Stored, TimingError>
{
    let destination = store.join(run.to_string());
    if destination.is_dir() {
        return Ok(Stored::Already);
    }
    let io = |path: &Path| {
        let path = path.to_owned();
        move |error: std::io::Error| TimingError::Io {
            path,
            message: error.to_string(),
        }
    };
    let scratch = store.join(format!(".partial-{run}"));
    if scratch.exists() {
        std::fs::remove_dir_all(&scratch).map_err(io(&scratch))?;
    }
    std::fs::create_dir_all(store).map_err(io(store))?;
    let mut command = Command::new("gh");
    command
        .args(["run", "download", &run.to_string(), "--repo", &repository.0])
        .args(["--pattern", "junit-*", "--dir"])
        .arg(&scratch);
    output(&mut command)?;
    std::fs::rename(&scratch, &destination).map_err(io(&destination))?;
    Ok(Stored::Fetched)
}

/// The runs held in `store`, newest first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every directory of `store` whose name is a run identifier, in
///   descending order; a missing store holds none.
/// - provides: the runs a report reads, fetched now or before.
/// - fails: [`TimingError::Io`] when the store exists and cannot be listed.
/// - panics: none.
///
/// # Errors
/// [`TimingError::Io`] — the store could not be listed.
///
/// # Adequacy
/// - hypothesis: L3 — a store with three runs, a scratch directory and a stray
///   file reports the three runs newest first; listing the scratch directory or
///   ascending order changes the report.
/// - witness: `tests::cli::a_report_reads_the_newest_stored_runs`
/// - witness: `tests::cli::an_empty_store_is_refused`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |runs| runs.is_sorted_by(|newer, older| newer > older)))]
#[inline]
pub fn stored_runs(store: &Path) -> Result<Vec<RunId>, TimingError>
{
    if !store.exists() {
        return Ok(Vec::new());
    }
    let refuse = |error: std::io::Error| TimingError::Io {
        path: store.to_owned(),
        message: error.to_string(),
    };
    let mut runs = Vec::new();
    for entry in std::fs::read_dir(store).map_err(refuse)? {
        let entry = entry.map_err(refuse)?;
        let is_dir = entry.file_type().map_err(refuse)?.is_dir();
        if let Some(id) = entry
            .file_name()
            .to_str()
            .and_then(|name| name.parse::<u64>().ok())
            && is_dir
        {
            runs.push(RunId(id));
        }
    }
    runs.sort_unstable_by(|left, right| right.cmp(left));
    Ok(runs)
}

/// Records every JUnit report of a stored run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each file named `junit.xml` anywhere under `store/<run>/<A>` is
///   read and recorded in `history` with lane `A`.
/// - provides: one run's samples, all lanes.
/// - fails: [`TimingError::Io`] when a directory or a report cannot be read;
///   the refusals of [`samples`] for an unreadable report.
/// - panics: none.
/// - executable: none — the outcome is the history's growth, state accumulated
///   across calls that only a traversal could check.
///
/// # Errors
/// - [`TimingError::Io`] — the run's directory or a report is unreadable.
/// - [`TimingError::Xml`], [`TimingError::TestCase`] — a report is not a JUnit
///   report nextest wrote.
///
/// # Adequacy
/// - hypothesis: L3 — a run with two lanes whose reports sit at different
///   depths is read whole, each report under its artifact's lane; a lane taken
///   from the wrong directory level or a report skipped changes the printed
///   table.
/// - witness: `tests::cli::a_report_reads_the_newest_stored_runs`
#[inline]
pub fn read_run(
    store: &Path,
    run: RunId,
    history: &mut History,
) -> Result<(), TimingError>
{
    let io = |path: &Path| {
        let path = path.to_owned();
        move |error: std::io::Error| TimingError::Io {
            path,
            message: error.to_string(),
        }
    };
    let root = store.join(run.to_string());
    let mut artifacts: Vec<PathBuf> = Vec::new();
    for entry in std::fs::read_dir(&root).map_err(io(&root))? {
        artifacts.push(entry.map_err(io(&root))?.path());
    }
    artifacts.sort_unstable();
    let mut pending: Vec<PathBuf> = Vec::new();
    for artifact in artifacts {
        let Some(lane) = artifact
            .file_name()
            .and_then(|name| name.to_str())
            .map(Lane::from)
        else {
            continue;
        };
        // The walk below drains the stack, so each artifact starts it empty.
        pending.push(artifact);
        while let Some(path) = pending.pop() {
            if path.is_dir() {
                for entry in std::fs::read_dir(&path).map_err(io(&path))? {
                    pending.push(entry.map_err(io(&path))?.path());
                }
            }
            else if path.file_name().is_some_and(|name| name == "junit.xml") {
                let text = std::fs::read_to_string(&path).map_err(io(&path))?;
                history.record(&lane, samples(ReportText::from(text.as_str()), &path)?);
            }
        }
    }
    Ok(())
}
