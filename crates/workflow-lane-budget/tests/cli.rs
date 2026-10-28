//! The report, the issue filing and the exit codes, observed by spawning the
//! binary with the fake `gh` of `tests/fakes` first on the path.
//!
//! The fake lists runs 3, 2 and 1; run `N` holds a Clippy job of `N`00
//! seconds and a five-second detection job. Run 3's base is deep (its
//! compare names a kernel file), run 2's surface; with the cone `unbased`,
//! run 3 is a push with no base to compare against. Its issue listing is
//! `FAKE_GH_ISSUES`; it logs every invocation to `FAKE_GH_LOG` and the last
//! body it was fed to `FAKE_GH_BODY`.
//!
//! The fake is a file of the tree, never written per case: macOS assesses an
//! executable the first time it runs, one at a time across the machine, and a
//! fresh fake per case queued past the 30-second limit in a whole-workspace
//! test run (#1574).
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::process::Command;

/// The report over runs 3 and 2 with Clippy's budget `BUDGET`, standing
/// `STANDING` and the table's summary `SUMMARY`.
const REPORT: &str = "This report holds each CI lane's median job time against its budget in \
                          `nightly.yml`.\n\nThe table holds each lane's median over the last 2 \
                          merge-queue and pull-request runs of `ci.yml`. The cone a landing \
                          touches gives each lane its class.\n\n\
                          <details><summary>SUMMARY</summary>\n\n\
                          | lane | class | median | budget | jobs | standing |\n\
                          | --- | --- | ---: | ---: | ---: | --- |\n\
                          | check Clippy wall | surface | 3m 20s | BUDGET | 2 | STANDING |\n\
                          \nThe table reads runs 3, 2.\n\n</details>\n";

/// A fresh scratch directory for the case `$name`, for the fake's log and body.
macro_rules! scratch {
    ($name:literal) => {{
        let root =
            std::env::temp_dir().join(format!("lane-budget-{}-{}", std::process::id(), $name));
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        std::fs::create_dir_all(&root).unwrap();
        root
    }};
}

/// Runs the binary with `$args`, the fake first on the path, its log and body
/// in `$root`, the issue listing `$issues`, the fake's mode `$mode` and its
/// cone `$cone`, after clearing the fake's log.
macro_rules! run {
    ($root:expr, $args:expr, $issues:expr, $mode:expr, $cone:expr) => {{
        let root: &std::path::Path = &$root;
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut paths = vec![std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fakes")];
        paths.extend(std::env::split_paths(&path));
        std::fs::write(root.join("log"), "").unwrap();
        Command::new(env!("CARGO_BIN_EXE_lane-budget"))
            .args($args)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("FAKE_GH_LOG", root.join("log"))
            .env("FAKE_GH_BODY", root.join("body"))
            .env("FAKE_GH_ISSUES", $issues)
            .env("FAKE_GH_MODE", $mode)
            .env("FAKE_GH_CONE", $cone)
            .output()
            .unwrap()
    }};
}

/// The invocations the fake in `$root` logged, one per line.
macro_rules! log {
    ($root:expr) => {
        std::fs::read_to_string($root.join("log")).unwrap()
    };
}

#[test]
fn an_over_budget_lane_opens_the_issue()
{
    let scratch = scratch!("open");
    let output = run!(
        scratch,
        [
            "--runs",
            "2",
            "--budget",
            "check Clippy wall=150",
            "--issue",
            "CI lane budgets",
        ],
        "[]",
        "",
        "all"
    );
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    let report = REPORT
        .replace("BUDGET", "2m 30s")
        .replace("STANDING", "**over**")
        .replace("SUMMARY", "1 lane — over: 1 over, 0 unmeasured");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!("{report}\nOpened https://example.invalid/issues/7.\n")
    );
    assert_eq!(
        std::fs::read_to_string(scratch.join("body")).unwrap(),
        report
    );
    let log = log!(scratch);
    assert!(log.contains("/runs/3/jobs"), "{log}");
    assert!(log.contains("/runs/2/jobs"), "{log}");
    assert!(!log.contains("/runs/1/jobs"), "{log}");
    assert!(
        log.contains("issue create --title CI lane budgets --body-file - --label collector"),
        "{log}"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn an_issue_follows_the_budget_both_ways()
{
    let scratch = scratch!("follow");
    let issues = |state: &str| {
        format!(
            r#"[{{"number":9,"state":"OPEN","title":"CI lane budgets (old)"}},{{"number":4,"state":"{state}","title":"CI lane budgets"}}]"#
        )
    };
    let budget = |seconds: &str| {
        [
            "--runs".to_owned(),
            "2".to_owned(),
            "--budget".to_owned(),
            format!("check Clippy wall={seconds}"),
            "--issue".to_owned(),
            "CI lane budgets".to_owned(),
        ]
    };
    for (seconds, state, filed, invocations) in [
        (
            "250",
            "OPEN",
            "Closed #4: every lane is within budget.",
            &[
                "issue edit 4 --body-file - --add-label collector",
                "issue close 4",
            ][..],
        ),
        (
            "150",
            "CLOSED",
            "Reopened #4.",
            &[
                "issue edit 4 --body-file - --add-label collector",
                "issue reopen 4",
            ][..],
        ),
        (
            "150",
            "OPEN",
            "Updated #4.",
            &["issue edit 4 --body-file - --add-label collector"][..],
        ),
        (
            "250",
            "CLOSED",
            "Every lane is within budget; no issue is open.",
            &[][..],
        ),
    ] {
        let owned = budget(seconds);
        let args = owned.iter().map(String::as_str).collect::<Vec<_>>();
        let output = run!(scratch, &args, issues(state), "", "all");
        assert!(output.status.success(), "{seconds} {state}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.ends_with(&format!("\n{filed}\n")), "{stdout}");
        let log = log!(scratch);
        let issue_calls = log
            .lines()
            .filter(|line| line.starts_with("issue ") && !line.starts_with("issue list"))
            .collect::<Vec<_>>();
        assert_eq!(issue_calls, invocations, "{seconds} {state}");
    }
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_failing_gh_is_reported_with_its_message()
{
    let scratch = scratch!("fail");
    let output = run!(
        scratch,
        ["--budget", "check Clippy wall=150"],
        "[]",
        "fail",
        "all"
    );
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("lane-budget: `") && stderr.ends_with("HTTP 401: Bad credentials\n"),
        "{stderr}"
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_malformed_budget_exits_two()
{
    let scratch = scratch!("malformed");
    let output = run!(scratch, ["--budget", "check Clippy wall"], "[]", "", "all");
    assert_eq!(output.status.code(), Some(2_i32));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("`check Clippy wall` is not a job name, `=`, and a whole number of seconds"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(log!(scratch), "", "no gh call before the arguments parse");
    let output = run!(
        scratch,
        [
            "--budget",
            "check Clippy wall=150",
            "--daily",
            "mutate the night's crate (linux):deep=840",
        ],
        "[]",
        "",
        "all"
    );
    assert_eq!(output.status.code(), Some(2_i32));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "`mutate the night's crate (linux):deep=840` names the deep cone; a scheduled lane \
             is held to one budget over its scheduled runs"
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(log!(scratch), "", "no gh call before the arguments parse");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_daily_lane_is_sampled_over_the_scheduled_runs()
{
    let scratch = scratch!("daily");
    let output = run!(
        scratch,
        [
            "--runs",
            "2",
            "--budget",
            "check Clippy wall=250",
            "--daily",
            "mutate the night's crate (linux)=75",
        ],
        "[]",
        "",
        "all"
    );
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Runs 3 and 2 hold the landing lane; the scheduled runs 9 and 8 hold
    // the daily one, at 90 and 80 seconds. Every run's jobs list both, and
    // each table reads only its own window.
    assert!(
        stdout.contains(
            "| check Clippy wall | surface | 3m 20s | 4m 10s | 2 | within |\n\nThe table reads runs 3, 2.\n\n</details>\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "The table holds the daily lanes' medians over the last 2 scheduled runs of \
             `ci.yml`.\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "| mutate the night's crate (linux) | daily | 1m 20s | 1m 15s | 2 | **over** |\n\nThe table reads runs 9, 8.\n\n</details>\n"
        ),
        "{stdout}"
    );
    let log = log!(scratch);
    assert!(log.contains("event=schedule"), "{log}");
    assert!(log.contains("/runs/9/jobs"), "{log}");
    assert!(log.contains("/runs/8/jobs"), "{log}");
    assert!(
        !log.contains("actions/runs/9 "),
        "a scheduled run is not cone-classified: {log}"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_nightly_lane_is_sampled_over_the_nightly_runs()
{
    let scratch = scratch!("nightly");
    let output = run!(
        scratch,
        [
            "--runs",
            "2",
            "--budget",
            "check Clippy wall=250",
            "--daily",
            "mutate the night's crate (linux)=75",
            "--nightly",
            "check Clippy wall=550",
        ],
        "[]",
        "",
        "all"
    );
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // The nightly workflow's scheduled runs 6 and 5 hold a Clippy job of 600
    // and 500 seconds; the landing runs hold one of 300 and 200. Each table
    // reads its own window, the nightly one after the daily one.
    assert!(
        stdout.contains(
            "| check Clippy wall | surface | 3m 20s | 4m 10s | 2 | within |\n\nThe table reads runs 3, 2.\n\n</details>\n"
        ),
        "{stdout}"
    );
    assert!(
        stdout.ends_with(
            "\nThe table reads runs 9, 8.\n\n</details>\n\nThe table holds the nightly lanes' \
             medians over the last 2 scheduled runs of `nightly.yml`.\n\n<details><summary>1 \
             lane — within: 0 over, 0 unmeasured</summary>\n\n| lane | class | median | budget | \
             jobs | standing |\n| --- | --- | ---: | ---: | ---: | --- |\n| check Clippy wall | \
             nightly | 8m 20s | 9m 10s | 2 | within |\n\nThe table reads runs 6, 5.\n\n</details>\n"
        ),
        "{stdout}"
    );
    let log = log!(scratch);
    assert!(log.contains("workflows/nightly.yml/runs"), "{log}");
    assert!(log.contains("/runs/6/jobs"), "{log}");
    assert!(log.contains("/runs/5/jobs"), "{log}");
    assert!(!log.contains("/runs/4/jobs"), "{log}");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_run_is_classified_by_the_cone_it_touched()
{
    let scratch = scratch!("cone");
    let output = run!(
        scratch,
        [
            "--runs",
            "2",
            "--budget",
            "check Clippy wall=250",
            "--budget",
            "check Clippy wall:deep=250",
        ],
        "[]",
        "",
        "mixed"
    );
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Run 3's compare names a kernel file: its 300 s sample is deep.
    // Run 2's is surface. Each class is held to its own budget: the
    // surface median is within, the deep one over.
    assert!(
        stdout.contains("| check Clippy wall | surface | 3m 20s | 4m 10s | 1 | within |"),
        "{stdout}"
    );
    assert!(
        stdout.contains("| check Clippy wall | deep | 5m 0s | 4m 10s | 1 | **over** |"),
        "{stdout}"
    );
    let log = log!(scratch);
    assert!(log.contains("compare/1111111111111111111111111111111111111111...3333333333333333333333333333333333333333"), "{log}");
    assert!(log.contains("compare/2222222222222222222222222222222222222222...4444444444444444444444444444444444444444"), "{log}");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_run_without_a_base_is_held_deep()
{
    let scratch = scratch!("unbased");
    let output = run!(
        scratch,
        [
            "--runs",
            "2",
            "--budget",
            "check Clippy wall=250",
            "--budget",
            "check Clippy wall:deep=250",
        ],
        "[]",
        "",
        "unbased"
    );
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Run 3 names no base: nothing is compared and its 300 s sample is
    // deep, where a comparison against nothing would read it surface.
    assert!(
        stdout.contains("| check Clippy wall | deep | 5m 0s | 4m 10s | 1 | **over** |"),
        "{stdout}"
    );
    assert!(
        stdout.contains("| check Clippy wall | surface | 3m 20s | 4m 10s | 1 | within |"),
        "{stdout}"
    );
    let log = log!(scratch);
    assert!(
        !log.contains("...3333333333333333333333333333333333333333"),
        "{log}"
    );
    assert!(log.contains("compare/2222222222222222222222222222222222222222...4444444444444444444444444444444444444444"), "{log}");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_summed_budget_tables_every_workflow()
{
    let scratch = scratch!("summed");
    let output = run!(
        scratch,
        [
            "--runs",
            "2",
            "--budget",
            "check Clippy wall=1000",
            "--summed",
            "Nightly=500/600",
            "--issue",
            "CI lane budgets",
        ],
        "[]",
        "",
        "all"
    );
    // The nightly's newest run, 6, passed its ceiling: the report is printed
    // and filed whole, then the command refuses (#3013).
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "lane-budget: the newest run passed its ceiling: Nightly run 6: 11m 5s summed, past its \
         10m 0s ceiling\n"
    );
    assert_eq!(output.status.code(), Some(2_i32));
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Every lane is within; the nightly's summed times, 665 s and 555 s, put
    // its median past the budget and run 6 past the ceiling, so the report
    // is over and the issue opens. Run 6's Clippy job grew the most past its
    // median over the two nights.
    assert!(
        stdout.ends_with(
            "\nThe table holds each workflow's summed job time and wall time over its last 2 \
             completed runs against the summed budgets in `nightly.yml`.\n\n\
             <details><summary>2 workflows — over: 1 over, 0 unmeasured</summary>\n\n\
             | workflow | runs | wall median | wall max | summed median | past budget | past \
             ceiling | standing |\n\
             | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |\n\
             | CI | 2 | 13m 20s | 15m 0s | 3m 45s | — | — | unbudgeted |\n\
             | Nightly | 2 | 10m 50s | 11m 40s | 9m 15s | 2 past 8m 20s | 1 past 10m 0s | \
             **over** |\n\
             \nThe table gives each run past its ceiling and the job that grew the most in \
             it.\n\n| workflow | run | summed | ceiling | job | time | median |\n\
             | --- | ---: | ---: | ---: | --- | ---: | ---: |\n\
             | Nightly | 6 | 11m 5s | 10m 0s | `check Clippy wall` | 10m 0s | 8m 20s |\n\
             \nThe Actions cache holds 10.0 GiB in 144 caches.\n\n</details>\n\
             \nOpened https://example.invalid/issues/7.\n"
        ),
        "{stdout}"
    );
    let log = log!(scratch);
    assert!(
        log.contains("actions/workflows/12/runs -f status=completed -f per_page=2"),
        "{log}"
    );
    assert!(log.contains("/runs/5/jobs"), "{log}");
    assert!(!log.contains("/runs/4/jobs"), "{log}");
    std::fs::remove_dir_all(&scratch).unwrap();
}
