//! `hotpath-gate`: the allocation counts of a landing's tip, judged against
//! the counts of its base.
//!
//! `hotpath-gate --repository OWNER/NAME --base REV [--store DIR]` runs in the
//! checkout of the tip. For each series of [`SERIES`] it reads the report that
//! the store keeps for `HEAD`, or runs the bench of the series under the
//! profiler with `HOTPATH_ALLOC_METRIC=count` and keeps its report as
//! `<store>/<commit>/<series>.json`. A report is a function of the tree of its
//! commit, so a second run at one commit measures nothing again. Each series
//! is judged against the report that the store keeps for the base, under
//! `hotpath/<series>-policy.toml`
//! ([`gandr_workflow_hotpath_guard::judge`]). A base with no kept report
//! judges nothing for that series, and the gate says so. The counts of a
//! fixed workload repeat to within 0.1 %, so one run a side decides. A commit
//! between the base and the tip accepts a regressed series with the trailer
//! `Changes-hotpath: <series>`. The store keeps the reports of the newest
//! [`KEPT`] commits.
//!
//! # Exit codes
//!
//! - `0`: no series regressed, or a commit accepts each one that did; also
//!   `--help` and `--version`.
//! - `1`: a series regressed past its policy, and no commit accepts it.
//! - `2`: a refusal — a bench, `git` or a file that fails, an unreadable report
//!   or policy, a malformed argument; also a malformed invocation.

extern crate alloc;

use alloc::collections::BTreeSet;
use core::str::FromStr as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_hotpath_guard::CommitSha;
use gandr_workflow_hotpath_guard::GuardError;
use gandr_workflow_hotpath_guard::Repository;
use gandr_workflow_hotpath_guard::judge;

/// The exit code of a series that regressed and that no commit accepts.
const REGRESSED: u8 = 1;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// The commits whose reports the store keeps.
const KEPT: usize = 32;

/// The trailer with which a commit accepts a regressed series.
const TRAILER: &str = "Changes-hotpath";

/// A series: its name, and the package and the bench that measure it.
#[derive(Clone, Copy, Debug)]
struct Series
{
    /// The name, as `hotpath/<name>-policy.toml` and the trailer write it.
    name: &'static str,
    /// The package of the bench.
    package: &'static str,
    /// The bench target.
    bench: &'static str,
}

/// Each series that the gate judges.
const SERIES: [Series; 3] = [
    Series {
        name: "gandr",
        package: "gandr-lang",
        bench: "hotpath",
    },
    Series {
        name: "store",
        package: "gandr-storage-schema",
        bench: "store",
    },
    Series {
        name: "conversion",
        package: "gandr-lang",
        bench: "conversion",
    },
];

/// The allocation counts of a landing's tip judged against its base's.
#[derive(Debug, clap::Parser)]
#[command(name = "hotpath-gate", version, about)]
struct Cli
{
    /// The repository, `OWNER/NAME`, which the summary links.
    #[arg(long, env = "GITHUB_REPOSITORY")]
    repository: Repository,
    /// The base of the landing, as `git rev-parse` reads it.
    #[arg(long)]
    base: String,
    /// The store of the reports: one directory for each commit.
    #[arg(long, default_value = "target/hotpath/kept")]
    store: PathBuf,
}

/// Parses the invocation, judges and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` when no series regressed or a commit accepts each one
///   that did, and after help or version; exits `1` after naming each series
///   that regressed with no acceptance; exits `2` after printing a refusal or a
///   usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3. A clear tip, a regressed tip, an accepted one and a base
///   with no report. A swapped exit code changes the observed result.
/// - witness: `tests::gate::equal_counts_pass`
/// - witness: `tests::gate::a_regressed_series_refuses_the_tip`
/// - witness: `tests::gate::a_trailer_accepts_its_series`
/// - witness: `tests::gate::a_base_with_no_report_judges_nothing`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS
    || ret == ExitCode::from(REGRESSED)
    || ret == ExitCode::from(REFUSED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            return match (error.print(), error.use_stderr()) {
                (Ok(()), false) => ExitCode::SUCCESS,
                (Ok(()), true) | (Err(_), _) => ExitCode::from(REFUSED),
            };
        },
    };
    match run(&cli) {
        Ok(regressed) if regressed.is_empty() => ExitCode::SUCCESS,
        Ok(regressed) => match writeln!(
            std::io::stderr(),
            "hotpath-gate: {} regressed past its policy; a commit accepts a series with the \
             trailer `{TRAILER}: <series>`",
            regressed.join(", ")
        ) {
            Ok(()) | Err(_) => ExitCode::from(REGRESSED),
        },
        Err(error) => match writeln!(std::io::stderr(), "hotpath-gate: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Measures each series at the tip, judges it against the base and prunes the
/// store.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the store, an absolute path, holds a report of each series for
///   `HEAD`; standard output receives the summary of each series whose base has
///   a report, or a line that names the base it lacks; the result names each
///   series whose verdict is a failure and that no trailer accepts, in the
///   order of [`SERIES`]; the store keeps the newest [`KEPT`] commits, and
///   always the head and the base.
/// - provides: the whole command.
/// - fails: every refusal of [`commit`], [`accepted`], [`measure`], [`read`],
///   [`judge::Run::read`], [`judge::Policy::read`] and [`prune`];
///   [`GuardError::Output`] when standard output cannot be written;
///   [`GuardError::Input`] naming the store when it has no absolute path.
/// - panics: none.
/// - executable: none — the outcome is the files and the bytes written.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::gate::a_regressed_series_refuses_the_tip`
/// - witness: `tests::gate::a_base_with_no_report_judges_nothing`
/// - witness: `tests::gate::a_bench_in_the_directory_of_its_package_keeps_its_report`
///
/// # Cost
/// - allocation: the read reports, each verdict and its summary, diagnostic
fn run(cli: &Cli) -> Result<Vec<&'static str>, GuardError>
{
    let store = std::path::absolute(&cli.store).map_err(|error| GuardError::Input {
        path: cli.store.display().to_string(),
        message: error.to_string(),
    })?;
    let head = commit("HEAD")?;
    let base = commit(&cli.base)?;
    let accepted = accepted(&base, &head)?;
    let mut regressed = Vec::new();
    for series in SERIES {
        let report = kept(&store, &head, series);
        if !report.exists() {
            measure(series, &report)?;
        }
        let before = kept(&store, &base, series);
        if !before.exists() {
            say(&format!(
                "{}: the store keeps no report of the base {base}; nothing is judged\n",
                series.name
            ))?;
            continue;
        }
        let policy = PathBuf::from(format!("hotpath/{}-policy.toml", series.name));
        let verdict = judge::judge(
            &read(&policy, judge::Policy::read)?,
            judge::Scope::All,
            &[read(&before, judge::Run::read)?],
            &[read(&report, judge::Run::read)?],
        );
        say(&judge::Summary {
            subject: judge::Subject {
                repository: &cli.repository,
                head: &head,
                base: &base,
                benchmark: series.name,
            },
            verdict: &verdict,
        }
        .to_string())?;
        if verdict.conclusion() == judge::Conclusion::Failure {
            if accepted.contains(series.name) {
                say(&format!(
                    "{}: a commit accepts the regression with `{TRAILER}: {}`\n",
                    series.name, series.name
                ))?;
            }
            else {
                regressed.push(series.name);
            }
        }
    }
    prune(&store, [&head, &base])?;
    Ok(regressed)
}

/// Writes a text to standard output.
///
/// # Specification
/// - requires: nothing.
/// - ensures: standard output receives the text.
/// - provides: each line that the gate prints.
/// - fails: [`GuardError::Output`] when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the bytes written.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::gate::a_base_with_no_report_judges_nothing`
fn say(text: &str) -> Result<(), GuardError>
{
    write!(std::io::stdout(), "{text}").map_err(|error| GuardError::Output {
        message: error.to_string(),
    })
}

/// The commit that a revision names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the full name of the commit that `git rev-parse` gives the
///   revision.
/// - provides: the head and the base of the judgement.
/// - fails: [`GuardError::Command`] when `git` fails; [`GuardError::Sha`] when
///   its answer is not a commit.
/// - panics: none.
/// - executable: none — the outcome is the repository's answer.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`]; a base that names no commit refuses.
/// - witness: `tests::gate::a_base_that_names_no_commit_is_refused`
fn commit(revision: &str) -> Result<CommitSha, GuardError>
{
    let answer = git(&["rev-parse", "--verify", &format!("{revision}^{{commit}}")])?;
    CommitSha::from_str(answer.trim())
}

/// The series that the commits from the base to the head accept.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each name of each `Changes-hotpath` trailer of each commit
///   reachable from `head` and not from `base`; a trailer names one series or
///   several, separated by commas.
/// - provides: the acceptances of the judgement.
/// - fails: [`GuardError::Command`] when `git` fails.
/// - panics: none.
/// - executable: none — the outcome is the repository's answer.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a trailer that names the regressed series accepts it; a
///   lost trailer refuses the tip.
/// - witness: `tests::gate::a_trailer_accepts_its_series`
fn accepted(
    base: &CommitSha,
    head: &CommitSha,
) -> Result<BTreeSet<String>, GuardError>
{
    let answer = git(&[
        "log",
        &format!("--format=%(trailers:key={TRAILER},valueonly,separator=%x2C)"),
        &format!("{base}..{head}"),
    ])?;
    Ok(answer
        .split([',', '\n'])
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(str::to_owned)
        .collect())
}

/// Runs `git` in the current directory and gives its standard output.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the standard output of a `git` that exits with success.
/// - provides: each read of the repository.
/// - fails: [`GuardError::Command`] naming the command when `git` does not
///   start, exits with failure, or prints what is not UTF-8.
/// - panics: none.
/// - executable: none — the outcome is the process's output.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`commit`].
/// - witness: `tests::gate::a_base_that_names_no_commit_is_refused`
fn git(arguments: &[&str]) -> Result<String, GuardError>
{
    let refused = |message: String| GuardError::Command {
        command: format!("git {}", arguments.join(" ")),
        message,
    };
    let output = Command::new("git")
        .args(arguments)
        .output()
        .map_err(|error| refused(error.to_string()))?;
    if !output.status.success() {
        return Err(refused(
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| refused(error.to_string()))
}

/// The path of the report that the store keeps for a commit and a series.
///
/// # Specification
/// trivial.
fn kept(
    store: &Path,
    commit: &CommitSha,
    series: Series,
) -> PathBuf
{
    store
        .join(commit.to_string())
        .join(format!("{}.json", series.name))
}

/// Runs the bench of a series under the profiler and keeps its report.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `report` holds the allocation counts of the run; the report is
///   written beside it and renamed, so a run that dies keeps no partial report.
/// - provides: the tip's side of each judgement.
/// - fails: [`GuardError::Command`] when the bench fails or writes no report;
///   [`GuardError::Input`] naming the path when the store cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the file on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `cargo` writes the report from the directory of a
///   package, as a bench runs; a relative path puts the report there, and the
///   gate refuses.
/// - witness: `tests::gate::a_bench_in_the_directory_of_its_package_keeps_its_report`
fn measure(
    series: Series,
    report: &Path,
) -> Result<(), GuardError>
{
    let stored = |error: std::io::Error| GuardError::Input {
        path: report.display().to_string(),
        message: error.to_string(),
    };
    let arguments = [
        "test",
        "--locked",
        "--profile",
        "test",
        "--package",
        series.package,
        "--bench",
        series.bench,
        "--features",
        "hotpath",
    ];
    let refused = |message: String| GuardError::Command {
        command: format!("cargo {}", arguments.join(" ")),
        message,
    };
    if let Some(directory) = report.parent() {
        std::fs::create_dir_all(directory).map_err(stored)?;
    }
    let partial = report.with_extension("json.partial");
    let status = Command::new("cargo")
        .args(arguments)
        .env("HOTPATH_ALLOC_METRIC", "count")
        .env("HOTPATH_OUTPUT_FORMAT", "json")
        .env("HOTPATH_OUTPUT_PATH", &partial)
        .status()
        .map_err(|error| refused(error.to_string()))?;
    if !status.success() {
        return Err(refused(format!("the bench exited with {status}")));
    }
    if !partial.exists() {
        return Err(refused(format!(
            "the bench wrote no report to `{}`",
            partial.display()
        )));
    }
    std::fs::rename(&partial, report).map_err(stored)
}

/// Reads a file and parses it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the parse of the file's text, with the path as a refusal names
///   it.
/// - provides: each report and policy that the judgement reads.
/// - fails: [`GuardError::Input`] naming the path when it cannot be read; each
///   refusal of `parse`.
/// - panics: none.
/// - executable: none — the outcome is the file on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::gate::equal_counts_pass`
fn read<T>(
    path: &Path,
    parse: fn(judge::Input<'_>) -> Result<T, GuardError>,
) -> Result<T, GuardError>
{
    let shown = path.display().to_string();
    let text = std::fs::read_to_string(path).map_err(|error| GuardError::Input {
        path: shown.clone(),
        message: error.to_string(),
    })?;
    parse(judge::Input {
        path: &shown,
        text: &text,
    })
}

/// Removes the reports of each commit but the newest [`KEPT`] and the
/// commits of the judgement.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the store holds at most [`KEPT`] directories besides `keep`, the
///   newest by their time of change; each of `keep` stays.
/// - provides: the bound of the store.
/// - fails: [`GuardError::Input`] naming the path when the store cannot be read
///   or a directory cannot be removed.
/// - panics: none.
/// - executable: none — the outcome is the directory on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a store past its bound loses its oldest commit and keeps
///   the base.
/// - witness: `tests::gate::the_store_keeps_its_newest_commits_and_the_base`
fn prune(
    store: &Path,
    keep: [&CommitSha; 2],
) -> Result<(), GuardError>
{
    let refused = |path: &Path, error: std::io::Error| GuardError::Input {
        path: path.display().to_string(),
        message: error.to_string(),
    };
    let kept: BTreeSet<String> = keep.iter().map(ToString::to_string).collect();
    let mut commits = Vec::new();
    for entry in std::fs::read_dir(store).map_err(|error| refused(store, error))? {
        let entry = entry.map_err(|error| refused(store, error))?;
        let path = entry.path();
        let changed = entry
            .metadata()
            .and_then(|metadata| metadata.modified())
            .map_err(|error| refused(&path, error))?;
        if path.is_dir() && !kept.contains(&*entry.file_name().to_string_lossy()) {
            commits.push((changed, path));
        }
    }
    commits.sort_by_key(|&(changed, _)| core::cmp::Reverse(changed));
    for &(_, ref path) in commits.iter().skip(KEPT) {
        std::fs::remove_dir_all(path).map_err(|error| refused(path, error))?;
    }
    Ok(())
}
