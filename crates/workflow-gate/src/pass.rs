//! The records of the gates that passed on a tree.
//!
//! `pr:open` and `pr:land` must know that a gate passed on the tree of a head,
//! and which checks it ran. A gate that passes writes a record of its tree,
//! its commit, its checks and its time. The record is a file under the common
//! directory of git, so a gate in one worktree counts for the same tree in
//! another. A record of a gate on another host comes here by [`admit`].
//!
//! A record is keyed by the tree. A rebase that changes nothing, or a commit
//! with new words, keeps the tree, so its record still counts. The checks of
//! all the records on a tree count together, as each one passed there.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

use serde::Serialize;
use serde_json::Value;

use crate::call::Part;
use crate::call::Parts;
use crate::call::Program;
use crate::call::Variable;
use crate::error::GateError;
use crate::name::Check;
use crate::name::Commit;
use crate::record::End;

/// The checks that [`require`] asks of the gates on the tree of a head: the
/// cheap set of `landing`.
const SELECTED: [&str; 1] = ["check:landing"];

/// The most tests that the time of a record names.
const SLOWEST: usize = 20;

/// The seconds in each unit of a duration as mise prints it. A longer name
/// stands before its prefix, so `ms` reads before `m`.
const UNITS: [(&str, f64); 7] = [
    ("ns", 0.000_000_001),
    ("µs", 0.000_001),
    ("us", 0.000_001),
    ("ms", 0.001),
    ("h", 3600.0),
    ("m", 60.0),
    ("s", 1.0),
];

/// What a verb of the records prints, and how it ends.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Passing
{
    /// The lines for standard output.
    pub out: String,
    /// The lines for standard error.
    pub lines: String,
    /// How the run ends.
    pub end: End,
}

/// What the record of a passed gate asks.
#[derive(Clone, Debug)]
pub struct RecordRequest
{
    /// The name of the gate, as `check` or `gate all`.
    pub gate: String,
    /// The tree that the gate passed on.
    pub tree: Commit,
    /// The log of the gate.
    pub log: PathBuf,
    /// The wall time of the gate in seconds, as JSON.
    pub seconds: String,
    /// The wait of the gate for its lane and for its slot, as JSON.
    pub wait: String,
    /// The checks that the gate ran.
    pub checks: Vec<Check>,
}

/// What the check of the records of a head asks.
#[derive(Clone, Debug)]
pub struct RequireRequest
{
    /// The command that asks, which each line names.
    pub command: String,
    /// The head.
    pub commit: Commit,
}

/// What the admission of the records of a gate on another host asks.
#[derive(Clone, Debug)]
pub struct AdmitRequest
{
    /// The host whose gate passed.
    pub host: String,
    /// The head that the gate passed on.
    pub commit: Commit,
    /// The records that the host sent, as a stream of JSON values.
    pub records: String,
}

/// What the time of a gate reads: its log, its wall time and its wait.
#[derive(Clone, Debug)]
pub struct Timed
{
    /// The standard error of the gate.
    pub log: String,
    /// The wall time of the gate in seconds, from the moment that it holds its
    /// slot.
    pub seconds: Value,
    /// The wait of the gate for its lane's lock and for its slot, as `{lane,
    /// slot}` in seconds.
    pub wait: Option<Value>,
}

/// The time of a gate, as its log gives it.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Times
{
    /// The wall time of the gate, as the request gives it.
    pub seconds: Value,
    /// The wait of the gate, as the request gives it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wait: Option<Value>,
    /// The time of each task, the slowest first.
    pub tasks: Vec<TaskTime>,
    /// The count of the tests of each test task and their summed time, the
    /// slowest first.
    pub suites: Vec<Suite>,
    /// The slowest tests and their tasks, the slowest first.
    pub tests: Vec<TestTime>,
}

/// The time of one task.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TaskTime
{
    /// The task.
    pub task: String,
    /// Its longest time, in seconds to a tenth.
    pub seconds: Value,
}

/// The tests of one test task.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Suite
{
    /// The task.
    pub task: String,
    /// The count of its tests.
    pub tests: usize,
    /// The sum of their times, in seconds to a tenth.
    pub seconds: Value,
}

/// The time of one test.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TestTime
{
    /// The task that ran the test.
    pub task: String,
    /// The test.
    pub test: String,
    /// Its longest time, in seconds to a tenth.
    pub seconds: Value,
}

/// Whether the gates on a tree ran the checks that a head selects.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Passed
{
    /// A gate passed on the tree, and the gates ran each selected check.
    pub accepted: bool,
    /// The selected checks that no gate on the tree ran.
    pub missing: Vec<Check>,
}

/// One record of a passed gate, as a file holds it.
#[derive(Clone, Debug, Serialize)]
struct Record<'gate>
{
    /// The tree that the gate passed on.
    tree: &'gate str,
    /// The commit under the tree.
    commit: &'gate str,
    /// The name of the gate.
    gate: &'gate str,
    /// The checks that the gate ran.
    checks: &'gate [Check],
    /// Each `check:*` task that the tree holds.
    tasks: Vec<String>,
    /// When the gate passed, in UTC.
    at: String,
    /// The time of the gate, or null when its log gave none.
    time: Value,
}

/// Gives the tree of the work in this worktree: the index, the working tree
/// and each untracked path that git does not ignore.
///
/// # Specification
/// - requires: the working directory is in a worktree of git.
/// - ensures: the tree that `git write-tree` gives after `git add -A :/` on a
///   copy of the index. The index of the worktree does not change.
/// - provides: the tree that a gate passes on, before its commit exists.
/// - fails: [`GateError::Command`] when git fails.
/// - panics: none.
/// - intension: the copy keeps the stamps of the index, so `git add` reads only
///   the changed files.
/// - executable: none — the outcome is the external processes'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the path of the copy and the tree, setup
///
/// # Adequacy
/// - hypothesis: L3 — a worktree with a change that no commit holds; a tree of
///   the index alone changes the asserted tree.
/// - witness: `tests::pass::a_gate_records_its_pass_and_a_head_requires_it`
#[inline]
pub fn tree(parts: &Parts) -> Result<String, GateError>
{
    let here = Path::new(".");
    let index = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &["rev-parse", "--path-format=absolute", "--git-path", "index"],
        input: "",
    }
    .start(here)?
    .finish(parts)?;
    let index = PathBuf::from(String::from_utf8_lossy(index.as_ref()).trim());
    let copy = std::env::temp_dir().join(format!("gate-index-{}-{}", std::process::id(), nanos()));
    // A copy of the index keeps its file stamps, so `git add` reads only the
    // changed files. The copy also keeps the stamp of the index itself: git
    // reads an entry again by content when the entry is not older than the
    // index, and a copy stamped now hides that.
    if copied(&index, &copy).is_err() {
        let _gone = std::fs::remove_file(&copy);
    }
    let path = copy.to_string_lossy();
    let variables = [Variable {
        name: "GIT_INDEX_FILE",
        value: &path,
    }];
    let written = Program {
        part: Part::from("git add"),
        name: "git",
        arguments: &["add", "-A", ":/"],
        input: "",
    }
    .start_with(here, &variables)
    .and_then(|running| running.finish(parts))
    .and_then(|_added| {
        Program {
            part: Part::from("git write-tree"),
            name: "git",
            arguments: &["write-tree"],
            input: "",
        }
        .start_with(here, &variables)?
        .finish(parts)
    });
    let _gone = std::fs::remove_file(&copy);
    Ok(String::from_utf8_lossy(written?.as_ref()).trim().to_owned())
}

/// Writes the record of a gate that passed on the tree of `request`.
///
/// # Specification
/// - requires: the working directory is in a worktree of git, and `mise` is on
///   the path.
/// - ensures: when the work is the tree of the request, one file under
///   `gandr-gate/<tree>/` of the common directory of git. It holds the tree,
///   the commit of `HEAD`, the gate, its checks, each `check:*` task, the time
///   in UTC and the [`Times`] of the log. A log that gives no times leaves the
///   time null. Work that changed while the gate ran records nothing.
/// - provides: the pass of a gate that `pr:open` and `pr:land` read.
/// - fails: [`GateError::Command`] when git or mise fails, and
///   [`GateError::Read`] when the task list does not read or the file does not
///   write.
/// - panics: none.
/// - intension: the file appears whole, by a rename, or not at all.
/// - executable: none — the outcome is the file.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the times, the task list and the text of the record, durable
///   by the record
///
/// # Adequacy
/// - hypothesis: L3 — a gate that passes, and a gate whose work changed; a
///   record of changed work, or no record of a pass, changes what `require`
///   answers.
/// - witness: `tests::pass::a_gate_records_its_pass_and_a_head_requires_it`
#[inline]
pub fn record(
    request: &RecordRequest,
    parts: &Parts,
) -> Result<Passing, GateError>
{
    let here = Path::new(".");
    let gate = &request.gate;
    let tree_of: &str = request.tree.as_ref();
    let mut lines = String::new();
    if tree(parts)? != tree_of {
        let _written = writeln!(
            lines,
            "{gate}: the work changed while the gate ran, so no pass is recorded; run `mise run {gate}` \
             again before `pr:open` or `pr:land`"
        );
        return Ok(Passing {
            out: String::new(),
            lines,
            end: End::Held,
        });
    }
    let listing = Program {
        part: Part::from("mise tasks ls"),
        name: "mise",
        arguments: &["tasks", "ls", "--json"],
        input: "",
    }
    .start(here)?;
    let places = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &[
            "rev-parse",
            "--path-format=absolute",
            "HEAD",
            "--git-common-dir",
        ],
        input: "",
    }
    .start(here)?;
    let time = timed(request).map_or_else(
        || {
            let _written = writeln!(
                lines,
                "{gate}: the log {} gave no times, so the record holds none",
                request.log.display()
            );
            Value::Null
        },
        |times| serde_json::to_value(times).unwrap_or(Value::Null),
    );
    let listed = listing.finish(parts)?;
    let places = places.finish(parts)?;
    let places = String::from_utf8_lossy(places.as_ref());
    let mut place = places.lines();
    let commit = place.next().unwrap_or_default();
    let common = place.next().unwrap_or_default();
    let tasks: Vec<Value> =
        serde_json::from_slice(listed.as_ref()).map_err(|error| GateError::Read {
            what: "mise tasks ls".to_owned(),
            reason: error.to_string(),
        })?;
    let tasks = tasks
        .iter()
        .filter_map(|task| task.get("name").and_then(Value::as_str))
        .filter(|name| name.starts_with("check:"))
        .map(ToOwned::to_owned)
        .collect();
    let text = serde_json::to_string(&Record {
        tree: tree_of,
        commit,
        gate,
        checks: &request.checks,
        tasks,
        at: stamp(SystemTime::now()),
        time,
    })
    .map_err(|error| GateError::Read {
        what: "the record".to_owned(),
        reason: error.to_string(),
    })?;
    put(&Path::new(common).join("gandr-gate").join(tree_of), &text)?;
    Ok(Passing {
        out: format!(
            "{gate}: passed on the tree {tree_of}; `pr:open` and `pr:land` accept a head with this tree\n"
        ),
        lines,
        end: End::Held,
    })
}

/// Answers whether a gate passed on the tree of the commit of `request` and
/// ran the cheap set of `landing`.
///
/// # Specification
/// - requires: the working directory is in a repository of git.
/// - ensures: [`End::Held`] when the records of the tree ran each check of the
///   cheap set, by [`passed`]. Else [`End::Refused`], and a line that names the
///   command to run.
/// - provides: the gate of `pr:open` and `pr:land` on a head.
/// - fails: [`GateError::Command`] when git fails, and [`GateError::Read`] when
///   a record does not read.
/// - panics: none.
/// - executable: none — the outcome is the records'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the records of the tree, growth within the records
///
/// # Adequacy
/// - hypothesis: L3 — a head with a record of the cheap set, and one with no
///   record; an answer for the commit in place of its tree changes the status.
/// - witness: `tests::pass::a_gate_records_its_pass_and_a_head_requires_it`
#[inline]
pub fn require(
    request: &RequireRequest,
    parts: &Parts,
) -> Result<Passing, GateError>
{
    let command = &request.command;
    let commit: &str = request.commit.as_ref();
    let spec = format!("{commit}^{{tree}}");
    let places = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &[
            "rev-parse",
            "--path-format=absolute",
            "--git-common-dir",
            &spec,
        ],
        input: "",
    }
    .start(Path::new("."))?
    .finish(parts)?;
    let places = String::from_utf8_lossy(places.as_ref());
    let mut place = places.lines();
    let common = place.next().unwrap_or_default();
    let tree_of = place.next().unwrap_or_default();
    let records = held(&Path::new(common).join("gandr-gate").join(tree_of))?;
    let mut lines = String::new();
    if records.is_empty() {
        let _written = writeln!(
            lines,
            "{command}: no gate passed on the tree of {commit}; run `mise run check` on it, then \
             `{command}` again"
        );
        return Ok(Passing {
            out: String::new(),
            lines,
            end: End::Refused,
        });
    }
    let verdict = passed(&Commit::from(tree_of), &SELECTED.map(Check::from), &records);
    if verdict.accepted {
        return Ok(Passing {
            out: String::new(),
            lines,
            end: End::Held,
        });
    }
    let missing = verdict
        .missing
        .iter()
        .map(AsRef::<str>::as_ref)
        .collect::<Vec<&str>>()
        .join(", ");
    let _written = writeln!(
        lines,
        "{command}: the gates that passed on the tree of {commit} did not run {missing}; run `mise run \
         check` on it, then `{command}` again"
    );
    Ok(Passing {
        out: String::new(),
        lines,
        end: End::Refused,
    })
}

/// Writes here the newest record that a gate on another host wrote for the
/// commit of `request` on its tree, with the host added.
///
/// # Specification
/// - requires: the working directory is in a repository of git.
/// - ensures: the newest record of the stream whose tree and commit are the
///   head's and that carries no `carried`, written as [`record`] writes one,
///   with `host`. With none, [`End::Refused`] and a line that says why.
/// - provides: the pass of a far gate, which [`require`] reads as a local one.
/// - fails: [`GateError::Command`] when git fails, and [`GateError::Read`] when
///   the file does not write.
/// - panics: none.
/// - executable: none — the outcome is the file.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the records of the stream and the text of the record, durable
///   by the record
///
/// # Adequacy
/// - hypothesis: L3 — a stream of two records of the head and one of another
///   commit; the oldest record, or a record of another commit, changes the
///   asserted file.
/// - witness: `tests::pass::a_far_record_is_admitted_with_its_host`
#[inline]
pub fn admit(
    request: &AdmitRequest,
    parts: &Parts,
) -> Result<Passing, GateError>
{
    let host = &request.host;
    let given: &str = request.commit.as_ref();
    let commit_spec = format!("{given}^{{commit}}");
    let tree_spec = format!("{given}^{{tree}}");
    let places = Program {
        part: Part::from("git rev-parse"),
        name: "git",
        arguments: &[
            "rev-parse",
            "--path-format=absolute",
            "--git-common-dir",
            &commit_spec,
            &tree_spec,
        ],
        input: "",
    }
    .start(Path::new("."))?
    .finish(parts)?;
    let places = String::from_utf8_lossy(places.as_ref());
    let mut place = places.lines();
    let common = place.next().unwrap_or_default();
    let commit = place.next().unwrap_or_default();
    let tree_of = place.next().unwrap_or_default();
    let mut lines = String::new();
    let Some(chosen) = newest(&request.records, commit, tree_of, host)
    else {
        let _written = writeln!(
            lines,
            "gate:remote: {host} gave no pass of {commit} on its tree {tree_of}, so none is recorded"
        );
        return Ok(Passing {
            out: String::new(),
            lines,
            end: End::Refused,
        });
    };
    put(
        &Path::new(common).join("gandr-gate").join(tree_of),
        &chosen.to_string(),
    )?;
    Ok(Passing {
        out: format!(
            "gate:remote: the gate on {host} passed on the tree {tree_of}; `pr:open` and `pr:land` accept \
             a head with this tree\n"
        ),
        lines,
        end: End::Held,
    })
}

/// Gives the time of a gate from its log: each task's time, each test
/// task's count and summed time, and the slowest tests.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the lines `[<task>] <line>` of the log, with its colour codes
///   removed, read as mise and nextest print them. A task's time is its longest
///   `Finished in`, so a nested `mise run` under the task's name counts once. A
///   test that two lines name counts once at its longest time. Each time is in
///   seconds to a tenth, and a whole number is an integer.
/// - provides: the time of a gate beside its record, with no run added.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value, which the cases pin.
///
/// # Cost
/// - allocation: the log without its colour codes, the times and the tests,
///   growth within the log
///
/// # Adequacy
/// - hypothesis: L2 — a log of two test tasks with a slow test and a retry, a
///   log with no task, and a wait; a sum of both lines of a test changes the
///   pinned suite.
/// - witness: `tests::pass::a_log_gives_each_time_once_at_its_longest`
/// - witness: `tests::pass::a_log_with_no_task_gives_the_wall_time_alone`
/// - witness: `tests::pass::the_wait_rides_beside_the_wall_time`
#[inline]
#[must_use]
pub fn times(timed: &Timed) -> Times
{
    let plain = uncoloured(&timed.log);
    let mut tasks: BTreeMap<&str, f64> = BTreeMap::new();
    let mut tests: BTreeMap<(&str, &str), f64> = BTreeMap::new();
    for raw in plain.split('\n') {
        let Some((task, line)) = tagged(raw)
        else {
            continue;
        };
        if let Some(took) = line
            .strip_prefix("Finished in ")
            .filter(|took| !took.is_empty())
        {
            let seconds = tenths(duration(took));
            let longest = tasks.entry(task).or_insert(seconds);
            *longest = longest.max(seconds);
        }
        if let Some((test, seconds)) = passing(line) {
            let longest = tests.entry((task, test)).or_insert(seconds);
            *longest = longest.max(seconds);
        }
    }
    let mut task_times: Vec<(&str, f64)> = tasks.into_iter().collect();
    task_times.sort_by(|left, right| right.1.total_cmp(&left.1).then_with(|| left.0.cmp(right.0)));
    let mut suites: Vec<(&str, usize, f64)> = Vec::new();
    for (&(task, _test), &seconds) in &tests {
        match suites.last_mut() {
            Some(suite) if suite.0 == task => {
                suite.1 = suite.1.saturating_add(1);
                suite.2 += seconds;
            },
            Some(_) | None => suites.push((task, 1, seconds)),
        }
    }
    let mut suites: Vec<(&str, usize, f64)> = suites
        .into_iter()
        .map(|(task, count, seconds)| (task, count, tenths(seconds)))
        .collect();
    suites.sort_by(|left, right| right.2.total_cmp(&left.2).then_with(|| left.0.cmp(right.0)));
    let mut slowest: Vec<(&str, &str, f64)> = tests
        .into_iter()
        .map(|((task, test), seconds)| (task, test, seconds))
        .collect();
    slowest.sort_by(|left, right| {
        right
            .2
            .total_cmp(&left.2)
            .then_with(|| left.0.cmp(right.0))
            .then_with(|| left.1.cmp(right.1))
    });
    slowest.truncate(SLOWEST);
    Times {
        seconds: timed.seconds.clone(),
        wait: timed.wait.clone(),
        tasks: task_times
            .into_iter()
            .map(|(task, seconds)| TaskTime {
                task: task.to_owned(),
                seconds: number(seconds),
            })
            .collect(),
        suites: suites
            .into_iter()
            .map(|(task, tests_of, seconds)| Suite {
                task: task.to_owned(),
                tests: tests_of,
                seconds: number(seconds),
            })
            .collect(),
        tests: slowest
            .into_iter()
            .map(|(task, test, seconds)| TestTime {
                task: task.to_owned(),
                test: test.to_owned(),
                seconds: number(tenths(seconds)),
            })
            .collect(),
    }
}

/// Answers whether the gates of `records` on `tree` ran each check of
/// `selected`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `accepted` when one record or more holds the tree and their
///   checks together hold each selected check. `missing` lists each selected
///   check that no record on the tree holds, in the order of `selected`.
/// - provides: the rule of [`require`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value, which the cases pin.
///
/// # Cost
/// - allocation: the checks that ran and the missing checks, growth within the
///   records
///
/// # Adequacy
/// - hypothesis: L2 — a passed tree, another tree, a reworded commit, a skipped
///   check, two gates on one tree and a stacked head; a check of each record
///   alone in place of their union changes the pinned answer.
/// - witness: `tests::pass::a_tree_passes_by_the_checks_of_its_records`
#[inline]
#[must_use]
pub fn passed(
    tree_of: &Commit,
    selected: &[Check],
    records: &[Value],
) -> Passed
{
    let tree_of: &str = tree_of.as_ref();
    let on: Vec<&Value> = records
        .iter()
        .filter(|record| record.get("tree").and_then(Value::as_str) == Some(tree_of))
        .collect();
    let ran: BTreeSet<&str> = on
        .iter()
        .filter_map(|record| record.get("checks").and_then(Value::as_array))
        .flatten()
        .filter_map(Value::as_str)
        .collect();
    let missing: Vec<Check> = selected
        .iter()
        .filter(|check| !ran.contains(check.as_ref()))
        .cloned()
        .collect();
    Passed {
        accepted: !on.is_empty() && missing.is_empty(),
        missing,
    }
}

/// Copies the index at `from` to `to`, and keeps its stamp.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the paths and the metadata of the copy, setup
#[inline]
fn copied(
    from: &Path,
    to: &Path,
) -> std::io::Result<()>
{
    let _bytes = std::fs::copy(from, to)?;
    let modified = std::fs::metadata(from)?.modified()?;
    std::fs::File::options()
        .write(true)
        .open(to)?
        .set_modified(modified)
}

/// The nanoseconds of the clock, which make a name of this run unique.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "a count of nanoseconds is the clock's number"
    )
)]
fn nanos() -> u128
{
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |since| since.as_nanos())
}

/// Writes `text` and a newline as a new file of `dir`, whole or not at all.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `dir` exists, and it holds one new file `<name>.json` with the
///   text. The file appears by a rename, so a reader never sees a part of it.
/// - provides: the write of a record.
/// - fails: [`GateError::Read`] with the path when a write fails.
/// - panics: none.
/// - executable: none — the outcome is the file.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the paths and the text, durable by the record
///
/// # Adequacy
/// - hypothesis: L3 — a record that `require` then reads; a file with no
///   `.json` name changes what `require` answers.
/// - witness: `tests::pass::a_gate_records_its_pass_and_a_head_requires_it`
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the text of a record is JSON that serde gives as a string"
    )
)]
fn put(
    dir: &Path,
    text: &str,
) -> Result<(), GateError>
{
    let refused = |path: &Path, error: &std::io::Error| GateError::Read {
        what: path.display().to_string(),
        reason: error.to_string(),
    };
    std::fs::create_dir_all(dir).map_err(|error| refused(dir, &error))?;
    let name = format!("{:x}-{:x}", std::process::id(), nanos());
    let partial = dir.join(format!(".record.{name}"));
    let whole = dir.join(format!("{name}.json"));
    std::fs::write(&partial, format!("{text}\n")).map_err(|error| refused(&partial, &error))?;
    std::fs::rename(&partial, &whole).map_err(|error| refused(&whole, &error))
}

/// The records in `dir`, each `*.json` file one JSON value. A directory that
/// does not exist holds none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one value for each file whose name ends in `.json` and does not
///   start with a dot.
/// - provides: the records of a tree for [`require`].
/// - fails: [`GateError::Read`] with the file when a record does not read.
/// - panics: none.
/// - executable: none — the outcome is the files'.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the records, growth within the records of the tree
///
/// # Adequacy
/// - hypothesis: L3 — a tree with a record and a tree with none; a read of a
///   file that is not written whole changes the answer.
/// - witness: `tests::pass::a_gate_records_its_pass_and_a_head_requires_it`
#[inline]
fn held(dir: &Path) -> Result<Vec<Value>, GateError>
{
    let Ok(entries) = std::fs::read_dir(dir)
    else {
        return Ok(Vec::new());
    };
    let mut records = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with('.') || !name.ends_with(".json") {
            continue;
        }
        let refused = |reason: String| GateError::Read {
            what: path.display().to_string(),
            reason,
        };
        let text = std::fs::read(&path).map_err(|error| refused(error.to_string()))?;
        records.push(serde_json::from_slice(&text).map_err(|error| refused(error.to_string()))?);
    }
    Ok(records)
}

/// The newest record of `records` of `commit` on `tree_of`, carried from no
/// other tree, with `host` added; none when the stream does not read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: of the records whose `tree` and `commit` match and whose
///   `carried` is absent or null, the one with the greatest `at`, the last of
///   equals. A stream that is not JSON gives none.
/// - provides: the choice of [`admit`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Cost
/// - allocation: the values of the stream, growth within the stream
///
/// # Adequacy
/// - hypothesis: L3 — two records of the head and one of another commit; the
///   first of the two in place of the newest changes the asserted file.
/// - witness: `tests::pass::a_far_record_is_admitted_with_its_host`
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the stream, the commit, the tree and the host are the text that git and the far host give"
    )
)]
fn newest(
    records: &str,
    commit: &str,
    tree_of: &str,
    host: &str,
) -> Option<Value>
{
    let values: Result<Vec<Value>, serde_json::Error> = serde_json::Deserializer::from_str(records)
        .into_iter::<Value>()
        .collect();
    let mut chosen: Option<Value> = None;
    for value in values.ok()? {
        let matches = value.get("tree").and_then(Value::as_str) == Some(tree_of)
            && value.get("commit").and_then(Value::as_str) == Some(commit)
            && value.get("carried").is_none_or(Value::is_null);
        let later = chosen.as_ref().is_none_or(|best| {
            best.get("at").and_then(Value::as_str) <= value.get("at").and_then(Value::as_str)
        });
        if matches && later {
            chosen = Some(value);
        }
    }
    let mut chosen = chosen?;
    let _old = chosen
        .as_object_mut()?
        .insert("host".to_owned(), Value::from(host));
    Some(chosen)
}

/// The time of the gate of `request`, or none when its log, its wall time or
/// its wait does not read.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the log, growth within the log
#[inline]
fn timed(request: &RecordRequest) -> Option<Times>
{
    let log = std::fs::read(&request.log).ok()?;
    Some(times(&Timed {
        log: String::from_utf8_lossy(&log).into_owned(),
        seconds: serde_json::from_str(&request.seconds).ok()?,
        wait: Some(serde_json::from_str(&request.wait).ok()?),
    }))
}

/// `log` with each colour code of a terminal removed: an escape, `[`, digits
/// and `;`, then `m`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the text, growth within the log
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "the log is text")
)]
fn uncoloured(log: &str) -> String
{
    let mut plain = String::with_capacity(log.len());
    let mut rest = log;
    while let Some(at) = rest.find('\u{1b}') {
        let (before, from) = rest.split_at(at);
        plain.push_str(before);
        let code = from
            .strip_prefix("\u{1b}[")
            .map(|inner| inner.trim_start_matches(|c: char| c.is_ascii_digit() || c == ';'))
            .and_then(|inner| inner.strip_prefix('m'));
        if let Some(after) = code {
            rest = after;
        }
        else {
            plain.push('\u{1b}');
            rest = from.get(1 ..).unwrap_or_default();
        }
    }
    plain.push_str(rest);
    plain
}

/// The task and the line of a line `[<task>] <line>` of a log.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a line of a log is text")
)]
fn tagged(raw: &str) -> Option<(&str, &str)>
{
    let inner = raw.strip_prefix('[')?;
    let close = inner.find(']')?;
    let task = inner.get(.. close).filter(|task| !task.is_empty())?;
    let line = inner.get(close ..)?.strip_prefix("] ")?;
    Some((task, line))
}

/// The test and its seconds of a line of nextest that says that the test
/// passed or is slow: `PASS [  1.5s] (1/3) <test>`.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a line of a log is text")
)]
fn passing(line: &str) -> Option<(&str, f64)>
{
    let mut rest = line.trim_start();
    if let Some(after) = rest.strip_prefix("TRY ") {
        let count = after.trim_start_matches(|c: char| c.is_ascii_digit());
        if count.len() < after.len()
            && let Some(retried) = count.strip_prefix(' ')
        {
            rest = retried;
        }
    }
    let rest = rest
        .strip_prefix("PASS [")
        .or_else(|| rest.strip_prefix("SLOW ["))?
        .trim_start();
    let (took, rest) = decimal(rest)?;
    let rest = rest.strip_prefix("s]")?;
    let after = rest.trim_start();
    if after.len() == rest.len() {
        return None;
    }
    let named = counted(after)
        .filter(|test| !test.trim_end().is_empty())
        .unwrap_or(after);
    let test = named.trim_end();
    if test.is_empty() {
        return None;
    }
    Some((test, took.parse().ok()?))
}

/// The rest of `text` after a count of nextest, `(<n>/<m>)` and white space.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a line of a log is text")
)]
fn counted(text: &str) -> Option<&str>
{
    let inner = text.strip_prefix('(')?.trim_start();
    let over = inner.trim_start_matches(|c: char| c.is_ascii_digit());
    let total = over
        .strip_prefix('/')
        .filter(|_| over.len() < inner.len())?;
    let close = total.trim_start_matches(|c: char| c.is_ascii_digit());
    let after = close
        .strip_prefix(')')
        .filter(|_| close.len() < total.len())?;
    let rest = after.trim_start();
    (rest.len() < after.len()).then_some(rest)
}

/// The decimal number at the start of `text`, `<digits>[.<digits>]`, and the
/// rest.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a number of a log is text")
)]
fn decimal(text: &str) -> Option<(&str, &str)>
{
    let digits = |text: &str| {
        text.find(|c: char| !c.is_ascii_digit())
            .unwrap_or(text.len())
    };
    let whole = digits(text);
    if whole == 0 {
        return None;
    }
    let after = text.get(whole ..)?;
    let fraction = after.strip_prefix('.').map_or(0, digits);
    let end = if fraction > 0 {
        whole.saturating_add(1).saturating_add(fraction)
    }
    else {
        whole
    };
    Some((text.get(.. end)?, text.get(end ..)?))
}

/// The seconds in a duration as mise prints it: `259.4ms`, `11.82s` or `1m
/// 2.5s`. Each number with a unit adds its seconds, and a text with none
/// gives zero.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a duration of a log is text")
)]
fn duration(took: &str) -> f64
{
    let mut total = 0.0_f64;
    let mut at = 0_usize;
    while let Some(rest) = took.get(at ..) {
        if rest.is_empty() {
            break;
        }
        let read = decimal(rest).and_then(|(number, tail)| {
            UNITS
                .iter()
                .find(|&&(name, _)| tail.starts_with(name))
                .map(|&(name, scale)| (number, name, scale))
        });
        if let Some((number, name, scale)) = read {
            // The product and the sum round apart, as `jq` computes them.
            let seconds = number.parse::<f64>().unwrap_or_default() * scale;
            total += seconds;
            at = at.saturating_add(number.len()).saturating_add(name.len());
        }
        else {
            at = at.saturating_add(rest.chars().next().map_or(1, char::len_utf8));
        }
    }
    total
}

/// `seconds` to a tenth, with a half away from zero.
///
/// # Specification
/// trivial.
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a time in seconds is a float")
)]
fn tenths(seconds: f64) -> f64
{
    (seconds * 10.0).round() / 10.0
}

/// `seconds` as a JSON number: an integer when it is whole, as `jq` prints it.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the text of the number, setup
#[inline]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(primitive_signature, reason = "a time in seconds is a float")
)]
fn number(seconds: f64) -> Value
{
    serde_json::from_str(&seconds.to_string()).unwrap_or(Value::Null)
}

/// The time `now` in UTC, as `2026-11-21T15:41:07Z`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the date of the proleptic Gregorian calendar and the time of day
///   of `now`, to the second. A time before 1970 reads as 1970.
/// - provides: the `at` of a record, which `admit` sorts by.
/// - fails: never.
/// - panics: none.
/// - executable: none — the outcome is a value.
///
/// # Cost
/// - allocation: the text, setup
///
/// # Adequacy
/// - hypothesis: L2 — the epoch, a leap day and a time of 2023; a month off by
///   one changes the pinned text.
/// - witness: `tests::pass::a_stamp_reads_the_calendar_in_utc`
#[inline]
#[must_use]
#[expect(
    clippy::arithmetic_side_effects,
    clippy::integer_division,
    reason = "the civil date of a count of days divides whole eras, years and months; each value stays under \
              the days of u64 seconds times 400, far from an overflow"
)]
pub fn stamp(now: SystemTime) -> String
{
    let seconds = now
        .duration_since(UNIX_EPOCH)
        .map_or(0, |since| since.as_secs());
    let days = seconds / 86_400;
    let clock = seconds % 86_400;
    // The civil date of a count of days, by the eras of 400 years of the
    // proleptic Gregorian calendar, with a year that starts in March.
    let shifted = days + 719_468;
    let era = shifted / 146_097;
    let of_era = shifted - era * 146_097;
    let year_of_era = (of_era - of_era / 1460 + of_era / 36_524 - of_era / 146_096) / 365;
    let of_year = of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let shifted_month = (5 * of_year + 2) / 153;
    let day = of_year - (153 * shifted_month + 2) / 5 + 1;
    let month = if shifted_month < 10 {
        shifted_month + 3
    }
    else {
        shifted_month - 9
    };
    let year = year_of_era + era * 400 + u64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        clock / 3600,
        clock % 3600 / 60,
        clock % 60
    )
}
