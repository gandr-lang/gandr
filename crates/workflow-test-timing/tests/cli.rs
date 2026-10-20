//! The report, the store and the exit codes, observed by spawning the binary.
//!
//! Each case builds a store and a configuration in its own scratch directory.
//! The fetching cases put a fake `gh` first on the path: it logs every
//! invocation, lists runs 9 and 7, and writes one enforcing report per
//! downloaded run whose test took twenty seconds per unit of the run's
//! identifier.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::path::PathBuf;
use std::process::Command;

/// The fake `gh`: logs its arguments to `FAKE_GH_LOG`, fails or prints
/// garbage as `FAKE_GH_MODE` says, and otherwise lists and downloads.
const FAKE_GH: &str = r#"#!/bin/sh
printf '%s\n' "$*" >> "$FAKE_GH_LOG"
case "$FAKE_GH_MODE" in
  fail) echo 'HTTP 401: Bad credentials' >&2; exit 1 ;;
  garbage) echo 'abc'; exit 0 ;;
esac
case "$1 $2" in
  'run list') printf '9\n7\n' ;;
  'run download')
    for dir; do :; done
    mkdir -p "$dir/junit-cargo-test-enforcing/ci-enforcing"
    printf '<testsuites><testsuite name="s"><testcase classname="gandr-a" name="slow::t" time="%s"/></testsuite></testsuites>\n' "$(( $3 * 20 ))" > "$dir/junit-cargo-test-enforcing/ci-enforcing/junit.xml" ;;
  *) echo "unexpected: $*" >&2; exit 2 ;;
esac
"#;

/// One report holding `slow::t`, `parse::was_slow` and `fast::t`, with
/// `slow::t` taking the placeholder's seconds.
const ENFORCING: &str = "<testsuites><testsuite name=\"s\">\
        <testcase classname=\"gandr-a\" name=\"slow::t\" time=\"SLOW\"/>\
        <testcase classname=\"gandr-a\" name=\"parse::was_slow\" time=\"2.0\"/>\
        <testcase classname=\"gandr-a\" name=\"fast::t\" time=\"0.1\"/>\
        </testsuite></testsuites>";

/// The configuration every case compares against.
const CONFIG: &str = "[[profile.default.overrides]]\n\
        filter = \"test(=parse::was_slow)\"\npriority = 90\n";

#[test]
fn a_report_reads_the_newest_stored_runs()
{
    let root = std::env::temp_dir().join(format!("test-timing-{}-newest", std::process::id()));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    let store = root.join("store");
    for (run, slow) in [("101", "1000.0"), ("102", "170.0"), ("103", "160.0")] {
        let lane = store
            .join(run)
            .join("junit-cargo-test-enforcing")
            .join("ci-enforcing");
        std::fs::create_dir_all(&lane).unwrap();
        std::fs::write(lane.join("junit.xml"), ENFORCING.replace("SLOW", slow)).unwrap();
        let plain = store.join(run).join("junit-cargo-test-plain");
        std::fs::create_dir_all(&plain).unwrap();
        std::fs::write(
                plain.join("junit.xml"),
                "<testsuites><testcase classname=\"gandr-a\" name=\"slow::t\" time=\"1.0\"/></testsuites>",
            )
            .unwrap();
    }
    std::fs::create_dir_all(store.join(".partial-104")).unwrap();
    std::fs::write(store.join("notes"), "not a run").unwrap();
    let config = root.join("nextest.toml");
    std::fs::write(&config, CONFIG).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_test-timing"))
        .args(["--offline", "--runs", "2", "--store"])
        .arg(&store)
        .arg("--config")
        .arg(&config)
        .output()
        .unwrap();
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "",
        "nothing on standard error"
    );
    assert!(output.status.success(), "exit 0");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "runs: 103, 102\n\n\
                 test             median  fastest  slowest  runs  current  proposed  lane\n\
                 slow::t           160.0    160.0    170.0     2        0       100  junit-cargo-test-enforcing\n\
                 parse::was_slow     2.0      2.0      2.0     2       90         0  junit-cargo-test-enforcing\n\
                 \n\
                 # Proposed priority overrides: these replace the `[[profile.default.overrides]]`\n\
                 # tables of {} that set `priority`.\n\
                 \n\
                 [[profile.default.overrides]]\n\
                 filter = \"test(=slow::t)\"\n\
                 priority = 100\n\
                 \n",
            config.display()
        ),
        "the two newest runs: `slow::t` by its enforcing lane, the stale override dropped"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn an_empty_store_is_refused()
{
    let root = std::env::temp_dir().join(format!("test-timing-{}-empty", std::process::id()));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    std::fs::create_dir_all(&root).unwrap();
    let store = root.join("store");
    let output = Command::new(env!("CARGO_BIN_EXE_test-timing"))
        .args(["--offline", "--store"])
        .arg(&store)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32), "exit 2");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!(
            "test-timing: {}: no stored run to report on\n",
            store.display()
        ),
        "the refusal names the store"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "",
        "nothing on standard output"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_malformed_invocation_exits_two()
{
    let output = Command::new(env!("CARGO_BIN_EXE_test-timing"))
        .args(["--runs", "0"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(2_i32),
        "zero runs is not a count"
    );
    assert!(
        !output.stderr.is_empty(),
        "the usage message goes to standard error"
    );
    let help = Command::new(env!("CARGO_BIN_EXE_test-timing"))
        .arg("--help")
        .output()
        .unwrap();
    assert!(help.status.success(), "help exits 0");
    assert!(
        String::from_utf8_lossy(&help.stdout).contains("--offline"),
        "help goes to standard output"
    );
}

/// A scratch directory holding the fake `gh`, its log and a store.
#[cfg(unix)]
#[repr(transparent)]
#[derive(Debug)]
struct Fake
{
    /// The scratch directory.
    root: PathBuf,
}

#[cfg(unix)]
impl Fake
{
    /// Installs the fake `gh` in a fresh scratch directory.
    ///
    /// # Specification
    /// - requires: a single-component `case` unique to the calling test.
    /// - ensures: `root/bin/gh` is the executable fake and `root` holds nothing
    ///   else.
    /// - provides: an isolated fake for one case.
    /// - fails: never.
    /// - panics: when the scratch directory cannot be prepared.
    /// - executable: none — the outcome is the filesystem, read back by the
    ///   cases that run the fake.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a case that runs the fake observes its log; a missing
    ///   or non-executable fake fails that case's first run.
    /// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
    fn new(case: &std::path::Path) -> Self
    {
        use std::os::unix::fs::PermissionsExt as _;
        let root = std::env::temp_dir()
            .join(format!("test-timing-{}", std::process::id()))
            .join(case);
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        std::fs::create_dir_all(root.join("bin")).unwrap();
        let gh = root.join("bin").join("gh");
        std::fs::write(&gh, FAKE_GH).unwrap();
        std::fs::set_permissions(&gh, std::fs::Permissions::from_mode(0o755)).unwrap();
        std::fs::write(root.join("nextest.toml"), CONFIG).unwrap();
        Self { root }
    }

    /// The binary, with the fake first on the path and its log and store
    /// in the scratch directory.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a command that runs the binary online against this scratch
    ///   directory's store and configuration.
    /// - provides: the invocation every fetching case makes.
    /// - fails: never.
    /// - panics: when the inherited path cannot be joined with the fake's.
    /// - executable: none — the outcome is a command not yet run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fetching cases observe the fake's log, so a
    ///   command that missed the fake would leave it empty.
    /// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
    fn command(&self) -> Command
    {
        let path = std::env::join_paths(core::iter::once(self.root.join("bin")).chain(
            std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()),
        ))
        .unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_test-timing"));
        command
            .env("PATH", path)
            .env("FAKE_GH_LOG", self.root.join("gh.log"))
            .args(["--repo", "o/r", "--store"])
            .arg(self.root.join("store"))
            .arg("--config")
            .arg(self.root.join("nextest.toml"));
        command
    }
}

#[cfg(unix)]
#[test]
fn fetched_runs_are_stored_and_read_back()
{
    let fake = Fake::new(std::path::Path::new("fetch"));
    let first = fake.command().output().unwrap();
    assert_eq!(
        String::from_utf8_lossy(&first.stderr),
        "",
        "nothing on standard error"
    );
    assert!(first.status.success(), "exit 0");
    let stdout = String::from_utf8_lossy(&first.stdout).into_owned();
    assert!(
        stdout.starts_with("runs: 9, 7\n"),
        "both listed runs, newest first: {stdout}"
    );
    assert!(
        stdout.ends_with("filter = \"test(=slow::t)\"\npriority = 90\n\n"),
        "a median of 140 s enters 90 and falls short of 100's 150 s: {stdout}"
    );
    let mut stored: Vec<String> = std::fs::read_dir(fake.root.join("store"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    stored.sort_unstable();
    assert_eq!(
        stored,
        ["7", "9"],
        "each run stored under its identifier, no scratch left"
    );
    let second = fake.command().output().unwrap();
    assert!(second.status.success(), "the second report exits 0");
    assert_eq!(
        second.stdout, first.stdout,
        "the same report from the stored runs"
    );
    let log = std::fs::read_to_string(fake.root.join("gh.log")).unwrap();
    let invocations: Vec<&str> = log
        .lines()
        .map(|line| {
            line.match_indices(' ')
                .nth(2)
                .map_or(line, |(at, _)| line.split_at(at).0)
        })
        .collect();
    assert_eq!(
        invocations,
        [
            "run list --repo",
            "run download 9",
            "run download 7",
            "run list --repo"
        ],
        "the second report lists runs and downloads none"
    );
    std::fs::remove_dir_all(&fake.root).unwrap();
}

#[cfg(unix)]
#[test]
fn a_failing_gh_is_reported_with_its_message()
{
    let fake = Fake::new(std::path::Path::new("failing"));
    let failed = fake.command().env("FAKE_GH_MODE", "fail").output().unwrap();
    assert_eq!(
        failed.status.code(),
        Some(2_i32),
        "a failed listing exits 2"
    );
    assert_eq!(
        String::from_utf8_lossy(&failed.stderr),
        "test-timing: `gh run list --repo o/r --workflow ci.yml --event merge_group --status \
             success --limit 5 --json databaseId --jq .[].databaseId` failed: HTTP 401: Bad \
             credentials\n",
        "the invocation and what gh wrote to standard error"
    );
    let garbage = fake
        .command()
        .env("FAKE_GH_MODE", "garbage")
        .output()
        .unwrap();
    assert_eq!(
        garbage.status.code(),
        Some(2_i32),
        "a listing that is not numbers exits 2"
    );
    assert_eq!(
        String::from_utf8_lossy(&garbage.stderr),
        "test-timing: `gh run list` failed: `abc` is not a run identifier: invalid digit found \
             in string\n",
        "the line that is not a run identifier"
    );
    assert!(!fake.root.join("store").exists(), "nothing stored");
    std::fs::remove_dir_all(&fake.root).unwrap();
}
