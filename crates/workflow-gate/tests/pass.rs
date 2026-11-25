//! The records of passed gates: the rules of a time and of a pass, on the
//! cases of the scripts that this crate replaces, and the binary in a scratch
//! repository.

use core::time::Duration;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::time::UNIX_EPOCH;

use gandr_workflow_gate::Check;
use gandr_workflow_gate::Commit;
use gandr_workflow_gate::Timed;
use gandr_workflow_gate::passed;
use gandr_workflow_gate::stamp;
use gandr_workflow_gate::times;
use serde_json::Value;
use serde_json::json;

/// The time of the log `$log`, the wall time `$seconds` and the wait `$wait`,
/// as JSON.
macro_rules! timed {
    ($log:expr, $seconds:expr, $wait:expr $(,)?) => {
        serde_json::to_value(times(&Timed {
            log: ($log).to_owned(),
            seconds: $seconds,
            wait: $wait,
        }))
        .unwrap()
    };
}

/// The answer of the rule of a pass on the tree `$tree` for the checks
/// `$selected` and the records `$records`, as JSON.
macro_rules! pass {
    ($tree:expr, $selected:expr, $records:expr $(,)?) => {{
        let selected: Vec<Check> = $selected.iter().copied().map(Check::from).collect();
        let records: Value = $records;
        serde_json::to_value(passed(
            &Commit::from($tree),
            &selected,
            records.as_array().unwrap(),
        ))
        .unwrap()
    }};
}

/// A record of the gate `$gate` on the tree `$tree` at the commit `$commit`
/// that ran the checks `$checks`.
macro_rules! gated {
    ($tree:expr, $commit:expr, $gate:expr, $checks:expr $(,)?) => {
        json!({"tree": $tree, "commit": $commit, "gate": $gate, "checks": $checks})
    };
}

/// Runs `git` with `$args` in `$root`, and gives its trimmed output.
macro_rules! git {
    ($root:expr, $args:expr $(,)?) => {{
        let args: &[&str] = &$args;
        let output = Command::new("git")
            .args(args)
            .current_dir(&$root)
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("GIT_AUTHOR_NAME", "case")
            .env("GIT_AUTHOR_EMAIL", "case@example.invalid")
            .env("GIT_COMMITTER_NAME", "case")
            .env("GIT_COMMITTER_EMAIL", "case@example.invalid")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).trim().to_owned()
    }};
}

/// A fresh repository for the case `$name` with one commit, and beside it the
/// task list of the fake `mise`. Gives the repository's root.
macro_rules! scratch {
    ($name:literal) => {{
        let base = std::env::temp_dir().join(format!("gate-pass-{}-{}", std::process::id(), $name));
        if base.exists() {
            std::fs::remove_dir_all(&base).unwrap();
        }
        let root = base.join("repo");
        std::fs::create_dir_all(&root).unwrap();
        let _init = git!(root, ["init", "--quiet", "--object-format=sha1"]);
        std::fs::write(root.join("a"), "a\n").unwrap();
        let _added = git!(root, ["add", "-A"]);
        let _commit = git!(root, ["commit", "--quiet", "-m", "base"]);
        std::fs::write(
            base.join("tasks.json"),
            "[{\"name\":\"check\"},{\"name\":\"check:landing\"},{\"name\":\"check:prose\"},{\"name\":\"pr:open\"}]",
        )
        .unwrap();
        PathBuf::from(git!(root, ["rev-parse", "--show-toplevel"]))
    }};
}

/// Runs `gate pass` with `$args` in `$root`, the fakes first on the path,
/// with `$input` on standard input.
macro_rules! gate {
    ($root:expr, $args:expr, $input:expr $(,)?) => {{
        use std::io::Write as _;
        let root: &Path = &$root;
        let args: &[&str] = &$args;
        let input: &str = &$input;
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut paths = vec![manifest.join("tests/fakes")];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let mut child = Command::new(env!("CARGO_BIN_EXE_gate"))
            .arg("pass")
            .args(args)
            .current_dir(root)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("GIT_CONFIG_GLOBAL", "/dev/null")
            .env("GIT_CONFIG_SYSTEM", "/dev/null")
            .env("FAKE_MISE_TASKS", root.parent().unwrap().join("tasks.json"))
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(input.as_bytes())
            .unwrap();
        child.wait_with_output().unwrap()
    }};
}

/// The text of the stream `$stream` of an output.
macro_rules! text {
    ($stream:expr) => {
        String::from_utf8_lossy(&$stream).into_owned()
    };
}

/// The records under the tree `$tree` of the repository `$root`, each as
/// JSON.
macro_rules! records {
    ($root:expr, $tree:expr $(,)?) => {{
        let common = git!($root, [
            "rev-parse",
            "--path-format=absolute",
            "--git-common-dir"
        ]);
        let dir = Path::new(&common).join("gandr-gate").join($tree);
        std::fs::read_dir(dir).map_or_else(
            |_absent| Vec::new(),
            |entries| {
                entries
                    .map(|entry| {
                        serde_json::from_slice::<Value>(
                            &std::fs::read(entry.unwrap().path()).unwrap(),
                        )
                        .unwrap()
                    })
                    .collect::<Vec<Value>>()
            },
        )
    }};
}

const EMPTY: &str = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";
const FIRST: &str = "1566710c2a0b8f9e1d2c3b4a5968778695a4b3c2";

#[test]
#[expect(
    clippy::default_numeric_fallback,
    reason = "the JSON of the case states its numbers as a record holds them"
)]
fn a_log_gives_each_time_once_at_its_longest()
{
    let log = "[check:tests] $ .config/mise/gated cargo nextest run --workspace\n\
               [check:tests] Finished in 2.0s\n\
               [check:tests]     Finished `test` profile [optimized] target(s) in 0.04s\n\
               [check:tests]         PASS [   0.002s] (1/3) gandr-a tests::quick\n\
               [check:tests]         SLOW [> 30.000s] (2/3) gandr-b::tests sweeps::census\n\
               [check:tests]         PASS [  34.517s] (2/3) gandr-b::tests sweeps::census\n\
               [check:tests]         \u{1b}[32mPASS\u{1b}[0m [   7.250s] (3/3) gandr-b::tests sweeps::parity\n\
               [check:tests]      Summary [  34.600s] 3 tests run: 3 passed (1 slow), 0 skipped\n\
               [check:tests]         PASS [  34.517s] gandr-b::tests sweeps::census\n\
               [check:tests] Finished in 1m 2.5s\n\
               [check:tests-enforcing]         TRY 2 PASS [  12.040s] (1/1) gandr-b::tests sweeps::census\n\
               [check:tests-enforcing] Finished in 40.2s\n\
               [check:host-lock] host-lock check OK\n\
               [check:host-lock] Finished in 259.4ms\n\
               Finished in 1m 3s\n";
    assert_eq!(
        timed!(log, json!(63), None),
        json!({
            "seconds": 63,
            "tasks": [
                {"task": "check:tests", "seconds": 62.5},
                {"task": "check:tests-enforcing", "seconds": 40.2},
                {"task": "check:host-lock", "seconds": 0.3}
            ],
            "suites": [
                {"task": "check:tests", "tests": 3, "seconds": 41.8},
                {"task": "check:tests-enforcing", "tests": 1, "seconds": 12}
            ],
            "tests": [
                {"task": "check:tests", "test": "gandr-b::tests sweeps::census", "seconds": 34.5},
                {"task": "check:tests-enforcing", "test": "gandr-b::tests sweeps::census", "seconds": 12},
                {"task": "check:tests", "test": "gandr-b::tests sweeps::parity", "seconds": 7.3},
                {"task": "check:tests", "test": "gandr-a tests::quick", "seconds": 0}
            ]
        })
    );
}

#[test]
#[expect(
    clippy::default_numeric_fallback,
    reason = "the JSON of the case states its numbers as a record holds them"
)]
fn a_log_with_no_task_gives_the_wall_time_alone()
{
    assert_eq!(
        timed!("mise ERROR no task check:missing found\n", json!(2), None),
        json!({"seconds": 2, "tasks": [], "suites": [], "tests": []})
    );
}

#[test]
#[expect(
    clippy::default_numeric_fallback,
    reason = "the JSON of the case states its numbers as a record holds them"
)]
fn the_wait_rides_beside_the_wall_time()
{
    assert_eq!(
        timed!(
            "[check:host-lock] Finished in 0.3s\n",
            json!(40),
            Some(json!({"lane": 3, "slot": 125}))
        ),
        json!({
            "seconds": 40,
            "wait": {"lane": 3, "slot": 125},
            "tasks": [{"task": "check:host-lock", "seconds": 0.3}],
            "suites": [],
            "tests": []
        })
    );
}

#[test]
fn a_tree_passes_by_the_checks_of_its_records()
{
    let two = ["check:claims", "check:prose"];
    let three = ["check:claims", "check:corpus", "check:prose"];
    let one_gate = || json!([gated!(EMPTY, FIRST, "check", two)]);
    // A tree that a gate passed on.
    assert_eq!(
        pass!(EMPTY, two, one_gate()),
        json!({"accepted": true, "missing": []})
    );
    // A tree that no gate passed on, as a head that changed after its gate.
    assert_eq!(
        pass!("d1e2f3a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0", two, one_gate()),
        json!({"accepted": false, "missing": two})
    );
    // A commit with new words keeps its tree, so the gate on the first commit
    // counts.
    assert_eq!(
        pass!(
            EMPTY,
            two,
            json!([gated!(
                EMPTY,
                "77a97c432d1e0f9a8b7c6d5e4f3a2b1c0d9e8f7a",
                "check",
                two
            )])
        ),
        json!({"accepted": true, "missing": []})
    );
    // A gate that skipped a check that the head's change selects does not
    // count.
    assert_eq!(
        pass!(EMPTY, three, one_gate()),
        json!({"accepted": false, "missing": ["check:corpus"]})
    );
    // The checks of two gates on one tree count together.
    assert_eq!(
        pass!(
            EMPTY,
            three,
            json!([
                gated!(EMPTY, FIRST, "check", two),
                gated!(EMPTY, FIRST, "gate:all", [
                    "check:claims",
                    "check:corpus",
                    "check:prose",
                    "check:tests"
                ])
            ])
        ),
        json!({"accepted": true, "missing": []})
    );
    // A head that `pr:open` stacks on the top has a new tree, so the gate
    // before the stack does not count.
    let stacked = ["check:claims", "check:prose", "check:tests"];
    assert_eq!(
        pass!(
            "6eabb84fc6b88fa3285769e045d59bbe3a5d7f55",
            stacked,
            json!([gated!(
                "2bbc91270e3f5abb48364d069eb7a5fe7eac4cd0",
                "7134e2eae0000000000000000000000000000000",
                "check",
                stacked
            )])
        ),
        json!({"accepted": false, "missing": stacked})
    );
}

#[test]
fn a_stamp_reads_the_calendar_in_utc()
{
    let at = |seconds: u64| stamp(UNIX_EPOCH + Duration::from_secs(seconds));
    assert_eq!(at(0), "1970-01-01T00:00:00Z");
    assert_eq!(at(951_782_400), "2000-02-29T00:00:00Z");
    assert_eq!(at(951_868_800), "2000-03-01T00:00:00Z");
    assert_eq!(at(1_700_000_000), "2023-11-14T22:13:20Z");
}

#[test]
#[expect(
    clippy::default_numeric_fallback,
    reason = "the JSON of the time states its numbers as a record holds them"
)]
fn a_gate_records_its_pass_and_a_head_requires_it()
{
    let root = scratch!("record");
    // The work holds an untracked file, which the tree of the work holds and
    // the index does not.
    std::fs::write(root.join("b"), "b\n").unwrap();
    let work = gate!(root, ["tree"], "");
    assert_eq!(work.status.code(), Some(0_i32), "{}", text!(work.stderr));
    let tree = text!(work.stdout).trim().to_owned();
    assert_eq!(git!(root, ["status", "--porcelain"]), "?? b");
    let _added = git!(root, ["add", "-A"]);
    let _commit = git!(root, ["commit", "--quiet", "-m", "head"]);
    assert_eq!(git!(root, ["rev-parse", "HEAD:"]), tree);
    let head = git!(root, ["rev-parse", "HEAD"]);

    let refused = gate!(root, ["require", "pr:open", "HEAD"], "");
    assert_eq!(
        text!(refused.stderr),
        "pr:open: no gate passed on the tree of HEAD; run `mise run check` on it, then `pr:open` again\n"
    );
    assert_eq!(refused.status.code(), Some(2_i32));

    let log = root.parent().unwrap().join("check.log");
    std::fs::write(&log, "[check:landing] Finished in 1m 2.5s\n").unwrap();
    let log = log.to_string_lossy();
    let wait = json!({"lane": 3, "slot": 125}).to_string();
    // A gate whose work is another tree records nothing.
    let changed = gate!(
        root,
        ["record", "check", EMPTY, &log, "63", &wait, "check:landing"],
        ""
    );
    assert_eq!(
        text!(changed.stderr),
        "check: the work changed while the gate ran, so no pass is recorded; run `mise run check` again \
         before `pr:open` or `pr:land`\n"
    );
    assert_eq!(changed.status.code(), Some(0_i32));
    assert_eq!(records!(root, EMPTY), Vec::<Value>::new());
    // A gate of `check:prose` alone does not run the cheap set.
    let prose = gate!(
        root,
        ["record", "check", &tree, &log, "63", &wait, "check:prose"],
        ""
    );
    assert_eq!(
        text!(prose.stdout),
        format!(
            "check: passed on the tree {tree}; `pr:open` and `pr:land` accept a head with this tree\n"
        )
    );
    assert_eq!(prose.status.code(), Some(0_i32));
    let short = gate!(root, ["require", "pr:land", &head], "");
    assert_eq!(
        text!(short.stderr),
        format!(
            "pr:land: the gates that passed on the tree of {head} did not run check:landing; run `mise run \
             check` on it, then `pr:land` again\n"
        )
    );
    assert_eq!(short.status.code(), Some(2_i32));
    // The gate of the cheap set holds the head.
    let landing = gate!(
        root,
        ["record", "check", &tree, &log, "63", &wait, "check:landing"],
        ""
    );
    assert_eq!(
        landing.status.code(),
        Some(0_i32),
        "{}",
        text!(landing.stderr)
    );
    let held = gate!(root, ["require", "pr:open", "HEAD"], "");
    assert_eq!(text!(held.stderr), "");
    assert_eq!(held.status.code(), Some(0_i32));
    let mut written = records!(root, &tree);
    written.sort_by_key(|record| record["checks"].to_string());
    let record = written.first().unwrap();
    assert_eq!(record["tree"], json!(tree));
    assert_eq!(record["commit"], json!(head));
    assert_eq!(record["gate"], json!("check"));
    assert_eq!(record["checks"], json!(["check:landing"]));
    assert_eq!(record["tasks"], json!(["check:landing", "check:prose"]));
    assert_eq!(
        record["time"],
        json!({
            "seconds": 63,
            "wait": {"lane": 3, "slot": 125},
            "tasks": [{"task": "check:landing", "seconds": 62.5}],
            "suites": [],
            "tests": []
        })
    );
    assert_eq!(record["at"].as_str().map(str::len), Some(20));
}

#[test]
fn a_far_record_is_admitted_with_its_host()
{
    let root = scratch!("admit");
    let head = git!(root, ["rev-parse", "HEAD"]);
    let tree = git!(root, ["rev-parse", "HEAD:"]);
    let older = json!({"tree": tree, "commit": head, "gate": "check", "checks": ["check:landing"], "at": "2026-11-21T10:00:00Z"});
    let newer = json!({"tree": tree, "commit": head, "gate": "gate all", "checks": ["check:landing"], "at": "2026-11-21T11:00:00Z"});
    let carried = json!({"tree": tree, "commit": head, "gate": "check", "checks": [], "at": "2026-11-21T12:00:00Z", "carried": 7_i32});
    let other = json!({"tree": tree, "commit": EMPTY, "gate": "check", "checks": [], "at": "2026-11-21T13:00:00Z"});
    let stream = format!("{older}\n{newer}\n{carried}\n{other}\n");
    let admitted = gate!(root, ["admit", "far", "HEAD"], stream);
    assert_eq!(
        text!(admitted.stdout),
        format!(
            "gate:remote: the gate on far passed on the tree {tree}; `pr:open` and `pr:land` accept a head \
             with this tree\n"
        )
    );
    assert_eq!(admitted.status.code(), Some(0_i32));
    let mut expected = newer;
    expected["host"] = json!("far");
    assert_eq!(records!(root, &tree), vec![expected]);
    // A stream with no record of the head writes none.
    let none = gate!(root, ["admit", "far", "HEAD"], format!("{other}\n"));
    assert_eq!(
        text!(none.stderr),
        format!(
            "gate:remote: far gave no pass of {head} on its tree {tree}, so none is recorded\n"
        )
    );
    assert_eq!(none.status.code(), Some(2_i32));
}
