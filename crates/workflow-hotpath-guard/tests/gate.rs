//! The landing gate's exit codes and store, observed by spawning
//! `hotpath-gate` in a scratch repository whose store already holds the
//! reports of the tip, so no case runs a bench.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// The allocation policy of each series, as `hotpath/<series>-policy.toml`
/// writes it.
const POLICY: &str = "pr_check = \"fail\"\n\n[functions]\nmin_percent_total = 1\n\n[functions.alloc]\njudged = true\nfail_check = true\nmin_percent_change = 2\nmetrics = [\"avg\", \"total\"]\nmin_calls = 1\n\n[functions.timing]\njudged = false\n";

/// Each series that the gate judges.
const SERIES: [&str; 3] = ["gandr", "store", "conversion"];

/// The policy in bytes of the `gandr` series: one budget of the first row.
const BUDGET: &str = "[functions.alloc]\njudged = false\n\n[[functions.budgets]]\nmatch = \"gandr_core::first\"\nalloc = { avg = \"1 KB\" }\nmessage = \"the first stays small\"\n";

/// The exit code of a tip that passes.
const PASSED: Option<i32> = Some(0_i32);

/// The exit code of a tip with a series that regressed.
const REGRESSED: Option<i32> = Some(1_i32);

/// The exit code of a refusal.
const REFUSED: Option<i32> = Some(2_i32);

/// The commits that the store keeps besides the head and the base, and one
/// more.
const PAST_THE_BOUND: u32 = 33;

/// A case: its scratch directory's name, the message of the tip's commit, and
/// the allocation count of the `gandr` series' first row on each side; absent
/// for a side with no kept report. A tip with no kept report runs the fake
/// `cargo` of `tests/fakes`, which writes the base's count.
struct Case
{
    /// The scratch directory's name.
    name: &'static str,
    /// The message of the tip's commit.
    message: &'static str,
    /// The base's count.
    base: Option<u32>,
    /// The tip's count.
    head: Option<u32>,
}

/// What a case's run left: the process's output and the scratch repository.
struct Ran
{
    /// The gate's exit status and streams.
    output: Output,
    /// The scratch repository.
    root: PathBuf,
    /// The base commit.
    base: String,
}

/// Runs `git` in the scratch repository with no configuration of the host.
///
/// # Specification
/// trivial.
fn git(
    root: &Path,
    arguments: &[&str],
) -> String
{
    let output = Command::new("git")
        .current_dir(root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .args([
            "-c",
            "user.name=gate",
            "-c",
            "user.email=gate@example.invalid",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(arguments)
        .output()
        .unwrap();
    assert!(output.status.success(), "git {arguments:?}: {output:?}");
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

/// A report of one series: two rows, the first with `count` allocations in
/// one call.
///
/// # Specification
/// trivial.
fn report(count: u32) -> String
{
    format!(
        r#"{{"functions_alloc": {{"data": [{{"name": "gandr_core::first", "calls": 1, "avg": "{count}", "total": "{count}", "percent_total": "60.00%"}}, {{"name": "gandr_core::second", "calls": 1, "avg": "4000", "total": "4000", "percent_total": "40.00%"}}]}}}}"#
    )
}

/// A report in bytes of one series: one row that allocates `avg` in one call.
///
/// # Specification
/// trivial.
fn bytes_report(avg: &str) -> String
{
    format!(
        r#"{{"functions_alloc": {{"profiling_mode": "alloc-bytes", "data": [{{"name": "gandr_core::first", "calls": 1, "avg": "{avg}", "total": "{avg}", "percent_total": "100.00%"}}]}}}}"#
    )
}

/// Runs the gate again in a case's repository, with the policy in bytes of
/// the `gandr` series. The store keeps a run in bytes of the tip whose row
/// allocates `avg`; with no `avg`, the fake `cargo` writes a run of 512 B.
///
/// # Specification
/// trivial.
fn budgeted(
    ran: &Ran,
    avg: Option<&str>,
) -> Output
{
    std::fs::write(ran.root.join("hotpath/gandr-bytes-policy.toml"), BUDGET).unwrap();
    if let Some(avg) = avg {
        let head = git(&ran.root, &["rev-parse", "HEAD"]);
        std::fs::write(
            ran.root
                .join("target/hotpath/kept")
                .join(head)
                .join("gandr-bytes.json"),
            bytes_report(avg),
        )
        .unwrap();
    }
    let mut paths = vec![Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fakes")];
    paths.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap()));
    Command::new(env!("CARGO_BIN_EXE_hotpath-gate"))
        .current_dir(&ran.root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("PATH", std::env::join_paths(paths).unwrap())
        .env("GATE_REPORT", report(6000))
        .env("GATE_REPORT_BYTES", bytes_report("512 B"))
        .args(["--repository", "gandr-lang/gandr", "--base", "main~1"])
        .output()
        .unwrap()
}

/// Writes the case's repository, its two commits and its store, then runs the
/// gate in it.
///
/// # Specification
/// trivial.
fn gate(case: &Case) -> Ran
{
    let root =
        std::env::temp_dir().join(format!("hotpath-gate-{}-{}", std::process::id(), case.name));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    std::fs::create_dir_all(root.join("hotpath")).unwrap();
    for series in SERIES {
        std::fs::write(root.join(format!("hotpath/{series}-policy.toml")), POLICY).unwrap();
    }
    drop(git(&root, &["init", "--quiet", "--initial-branch=main"]));
    drop(git(&root, &["add", "hotpath"]));
    drop(git(&root, &["commit", "--quiet", "-m", "base"]));
    drop(git(&root, &[
        "commit",
        "--quiet",
        "--allow-empty",
        "-m",
        case.message,
    ]));
    let base = git(&root, &["rev-parse", "HEAD~1"]);
    let head = git(&root, &["rev-parse", "HEAD"]);
    let store = root.join("target/hotpath/kept");
    for (commit, count) in [(&base, case.base), (&head, case.head)] {
        let Some(count) = count
        else {
            continue;
        };
        std::fs::create_dir_all(store.join(commit)).unwrap();
        for series in SERIES {
            let count = if series == "gandr" { count } else { 6000 };
            std::fs::write(
                store.join(commit).join(format!("{series}.json")),
                report(count),
            )
            .unwrap();
        }
    }
    let mut paths = vec![Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fakes")];
    paths.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap()));
    let output = Command::new(env!("CARGO_BIN_EXE_hotpath-gate"))
        .current_dir(&root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("PATH", std::env::join_paths(paths).unwrap())
        .env("GATE_REPORT", report(case.base.unwrap_or(6000)))
        .args(["--repository", "gandr-lang/gandr", "--base", "main~1"])
        .output()
        .unwrap();
    Ran { output, root, base }
}

#[test]
fn equal_counts_pass()
{
    let ran = gate(&Case {
        name: "equal",
        message: "head",
        base: Some(6000),
        head: Some(6000),
    });
    let stdout = String::from_utf8_lossy(&ran.output.stdout);
    assert_eq!(ran.output.status.code(), PASSED, "{:?}", ran.output);
    assert_eq!(stdout.matches("no regression").count(), 3, "{stdout}");
}

#[test]
fn a_regressed_series_refuses_the_tip()
{
    let ran = gate(&Case {
        name: "regressed",
        message: "head",
        base: Some(6000),
        head: Some(6300),
    });
    let stdout = String::from_utf8_lossy(&ran.output.stdout);
    let stderr = String::from_utf8_lossy(&ran.output.stderr);
    assert_eq!(ran.output.status.code(), REGRESSED, "{:?}", ran.output);
    assert!(stdout.contains("### `gandr` · ⚠️ 1 regression"), "{stdout}");
    assert!(stdout.contains("gandr_core::first"), "{stdout}");
    assert_eq!(
        stderr.trim(),
        "hotpath-gate: gandr regressed past its policy; a commit accepts a series with the \
         trailer `Changes-hotpath: <series>`"
    );
}

#[test]
fn a_change_under_the_margin_passes()
{
    let ran = gate(&Case {
        name: "margin",
        message: "head",
        base: Some(6000),
        head: Some(6100),
    });
    assert_eq!(ran.output.status.code(), PASSED, "{:?}", ran.output);
}

#[test]
fn a_trailer_accepts_its_series()
{
    let ran = gate(&Case {
        name: "accepted",
        message: "head\n\nChanges-hotpath: store, gandr",
        base: Some(6000),
        head: Some(6300),
    });
    let stdout = String::from_utf8_lossy(&ran.output.stdout);
    assert_eq!(ran.output.status.code(), PASSED, "{:?}", ran.output);
    assert!(
        stdout.contains("gandr: a commit accepts the regression with `Changes-hotpath: gandr`"),
        "{stdout}"
    );
}

#[test]
fn a_trailer_of_another_series_accepts_nothing()
{
    let ran = gate(&Case {
        name: "other",
        message: "head\n\nChanges-hotpath: store",
        base: Some(6000),
        head: Some(6300),
    });
    assert_eq!(ran.output.status.code(), REGRESSED, "{:?}", ran.output);
}

#[test]
fn a_base_with_no_report_judges_nothing()
{
    let ran = gate(&Case {
        name: "unjudged",
        message: "head",
        base: None,
        head: Some(9000),
    });
    let stdout = String::from_utf8_lossy(&ran.output.stdout);
    assert_eq!(ran.output.status.code(), PASSED, "{:?}", ran.output);
    assert_eq!(
        stdout,
        format!(
            "gandr: the store keeps no report of the base {base}; nothing is judged\nstore: the \
             store keeps no report of the base {base}; nothing is judged\nconversion: the store \
             keeps no report of the base {base}; nothing is judged\n",
            base = ran.base
        )
    );
}

#[test]
fn a_base_that_names_no_commit_is_refused()
{
    let ran = gate(&Case {
        name: "unnamed",
        message: "head",
        base: Some(6000),
        head: Some(6000),
    });
    let output = Command::new(env!("CARGO_BIN_EXE_hotpath-gate"))
        .current_dir(&ran.root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .args(["--repository", "gandr-lang/gandr", "--base", "nowhere"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), REFUSED, "{output:?}");
    assert!(
        stderr.starts_with("hotpath-gate: `git rev-parse --verify nowhere^{commit}`: "),
        "{stderr}"
    );
}

#[test]
fn the_store_keeps_its_newest_commits_and_the_base()
{
    let ran = gate(&Case {
        name: "pruned",
        message: "head",
        base: Some(6000),
        head: Some(6000),
    });
    let store = ran.root.join("target/hotpath/kept");
    let fillers: Vec<PathBuf> = (0 .. PAST_THE_BOUND)
        .map(|index| store.join(format!("{index:040x}")))
        .collect();
    for filler in &fillers {
        std::fs::create_dir_all(filler).unwrap();
        std::thread::sleep(core::time::Duration::from_millis(5));
    }
    let output = Command::new(env!("CARGO_BIN_EXE_hotpath-gate"))
        .current_dir(&ran.root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .args(["--repository", "gandr-lang/gandr", "--base", "main~1"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), PASSED, "{output:?}");
    assert!(!fillers[0].exists(), "the oldest commit stays");
    assert!(fillers[1 ..].iter().all(|filler| filler.exists()));
    assert!(store.join(&ran.base).exists(), "the base is removed");
}

#[test]
fn a_bench_in_the_directory_of_its_package_keeps_its_report()
{
    let ran = gate(&Case {
        name: "measured",
        message: "head",
        base: Some(6000),
        head: None,
    });
    let stdout = String::from_utf8_lossy(&ran.output.stdout);
    let head = git(&ran.root, &["rev-parse", "HEAD"]);
    assert_eq!(ran.output.status.code(), PASSED, "{:?}", ran.output);
    assert_eq!(stdout.matches("no regression").count(), 3, "{stdout}");
    for series in SERIES {
        assert!(
            ran.root
                .join("target/hotpath/kept")
                .join(&head)
                .join(format!("{series}.json"))
                .exists(),
            "{series}"
        );
    }
}

#[test]
fn a_broken_budget_refuses_the_tip()
{
    let ran = gate(&Case {
        name: "budget",
        message: "head",
        base: Some(6000),
        head: Some(6000),
    });
    let output = budgeted(&ran, Some("1.5 KB"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), REGRESSED, "{output:?}");
    assert!(
        stdout.contains(
            "gandr-bytes: ⛔ gandr_core::first: alloc.avg 1.5 KB, over budget 1.0 KB: the first \
             stays small · fails the check\n"
        ),
        "{stdout}"
    );
    assert_eq!(
        stderr.trim(),
        "hotpath-gate: gandr-bytes regressed past its policy; a commit accepts a series with the \
         trailer `Changes-hotpath: <series>`"
    );
}

#[test]
fn a_trailer_accepts_a_broken_budget()
{
    let ran = gate(&Case {
        name: "budget-accepted",
        message: "head\n\nChanges-hotpath: gandr-bytes",
        base: Some(6000),
        head: Some(6000),
    });
    let output = budgeted(&ran, Some("1.5 KB"));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), PASSED, "{output:?}");
    assert!(
        stdout.contains(
            "gandr-bytes: a commit accepts the regression with `Changes-hotpath: gandr-bytes`"
        ),
        "{stdout}"
    );
}

#[test]
fn a_run_in_bytes_is_measured_and_kept()
{
    let ran = gate(&Case {
        name: "budget-measured",
        message: "head",
        base: Some(6000),
        head: Some(6000),
    });
    let output = budgeted(&ran, None);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let head = git(&ran.root, &["rev-parse", "HEAD"]);
    assert_eq!(output.status.code(), PASSED, "{output:?}");
    assert!(
        stdout.contains("gandr-bytes: no budget of 1 is broken\n"),
        "{stdout}"
    );
    assert_eq!(
        std::fs::read_to_string(
            ran.root
                .join("target/hotpath/kept")
                .join(head)
                .join("gandr-bytes.json")
        )
        .unwrap(),
        bytes_report("512 B")
    );
}
