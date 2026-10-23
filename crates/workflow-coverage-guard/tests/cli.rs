//! The comparison, the issue filing and the exit codes, observed by spawning
//! the binary with the fake `curl` and the fake `gh` of `tests/fakes` first on
//! the path.
//!
//! The fake Codecov lists `main`'s uploads as the head `bbbb…`, an upload
//! `cccc…` still pending, and `aaaa…`, the baseline. `aaaa…` covers crates
//! `a`, `b` and `gone`; the head covers `a`, `b` and `new`. `FAKE_COVERAGE`
//! chooses the head's numbers: `drop` (94.50 % to 87.90 %) or `steady`
//! (94.50 % to 94.60 %). `FAKE_HEAD` set to `pending` keeps the head
//! processing; `FAKE_LISTING` set to `unlisted` or `nobase` drops the head
//! or the baseline from the listing; `FAKE_CURL` set to `fail` refuses every
//! request. The fake `gh`'s issue listing is `FAKE_GH_ISSUES`; it logs every
//! invocation to `FAKE_GH_LOG` and the last body it was fed to
//! `FAKE_GH_BODY`, and fails every invocation under `FAKE_GH=fail`.
//!
//! The fakes are files of the tree, never written per case: macOS assesses an
//! executable the first time it runs, one at a time across the machine, so a
//! fake written fresh for every case queued behind every other first run of a
//! whole-workspace test run and passed the 30-second limit (#1574). A file of
//! the checkout is assessed once.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::process::Command;

/// The head's full name.
const HEAD: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

/// The report of the drop.
const DROP: &str = r"Main's coverage moved from 94.50 % at [aaaaaaa](https://app.codecov.io/github/gandr-lang/gandr/commit/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) to 87.90 % at [bbbbbbb](https://app.codecov.io/github/gandr-lang/gandr/commit/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb): -6.60 points, against a threshold of 0.50.
The upload covers 3 files; the one before covered 3.

**Dropped**: a fall over the threshold or fewer files. A second drop updates this issue.

<details><summary>4 crates moved — dropped</summary>

| crate | before | after | change | missed before | missed after |
| --- | ---: | ---: | ---: | ---: | ---: |
| gone | 93.33 % | — | gone | 20 | — |
| a | 95.00 % | 75.00 % | -20.00 | 20 | 100 |
| b | 95.00 % | 96.66 % | +1.66 | 15 | 10 |
| new | — | 96.33 % | new | — | 11 |

</details>
";

/// The report of the steady upload.
const STEADY: &str = r"Main's coverage moved from 94.50 % at [aaaaaaa](https://app.codecov.io/github/gandr-lang/gandr/commit/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) to 94.60 % at [bbbbbbb](https://app.codecov.io/github/gandr-lang/gandr/commit/bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb): +0.10 points, against a threshold of 0.50.
The upload covers 3 files; the one before covered 3.

Steady: within the threshold, no file lost.

<details><summary>1 crate moved — steady</summary>

| crate | before | after | change | missed before | missed after |
| --- | ---: | ---: | ---: | ---: | ---: |
| a | 95.00 % | 95.25 % | +0.25 | 20 | 19 |

</details>
";

/// A fresh scratch directory for the case `$name`, holding the fake `gh`'s log.
macro_rules! scratch {
    ($name:literal) => {{
        let root =
            std::env::temp_dir().join(format!("coverage-guard-{}-{}", std::process::id(), $name));
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join("log"), "").unwrap();
        root
    }};
}

/// Runs the binary over the head with `$args` after the repository and the
/// commit, the fakes first on the path, the `gh` log and body in `$root`, and
/// each `($key, $value)` of `$env` set.
macro_rules! run {
    ($root:expr, $args:expr, $env:expr) => {{
        let root: &std::path::Path = &$root;
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut paths = vec![std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fakes")];
        paths.extend(std::env::split_paths(&path));
        let mut command = Command::new(env!("CARGO_BIN_EXE_coverage-guard"));
        command
            .args(["--repository", "gandr-lang/gandr", "--sha", HEAD])
            .args($args)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("FAKE_GH_LOG", root.join("log"))
            .env("FAKE_GH_BODY", root.join("body"))
            .env_remove("GITHUB_REPOSITORY")
            .env_remove("GITHUB_SHA");
        for (key, value) in $env {
            command.env(key, value);
        }
        command.output().unwrap()
    }};
}

/// The `gh` invocations the fake in `$root` logged, one per line.
macro_rules! log {
    ($root:expr) => {
        std::fs::read_to_string($root.join("log")).unwrap()
    };
}

#[test]
fn a_drop_opens_the_issue()
{
    let scratch = scratch!("open");
    let output = run!(scratch, ["--threshold", "0.5", "--file-issue"], [
        ("FAKE_COVERAGE", "drop"),
        ("FAKE_GH_ISSUES", "[]")
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!("{DROP}\nOpened https://example.invalid/issues/7.\n")
    );
    assert_eq!(std::fs::read_to_string(scratch.join("body")).unwrap(), DROP);
    let log = log!(scratch);
    assert!(
        log.contains(
            "issue create --title coverage: main dropped from 94.50 to 87.90 (bbbbbbb) \
             --body-file - --label kind:defect --label area:ci"
        ),
        "{log}"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_second_drop_updates_the_open_issue()
{
    let scratch = scratch!("update");
    let issues = r#"[{"number":9,"title":"coverage: the lsp crate's witnesses"},{"number":4,"title":"coverage: main dropped from 94.47 to 87.94 (f6b04ae)"}]"#;
    let output = run!(scratch, ["--threshold", "0.5", "--file-issue"], [
        ("FAKE_COVERAGE", "drop"),
        ("FAKE_GH_ISSUES", issues)
    ]);
    assert!(output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stdout).ends_with("\nUpdated #4.\n"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let log = log!(scratch);
    let writes = log
        .lines()
        .filter(|line| !line.starts_with("issue list"))
        .collect::<Vec<_>>();
    assert_eq!(writes, [
        "issue edit 4 --title coverage: main dropped from 94.50 to 87.90 (bbbbbbb) --body-file -"
    ]);
    assert_eq!(std::fs::read_to_string(scratch.join("body")).unwrap(), DROP);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_steady_upload_files_nothing()
{
    let scratch = scratch!("steady");
    let output = run!(scratch, ["--threshold", "0.5", "--file-issue"], [
        ("FAKE_COVERAGE", "steady"),
        ("FAKE_GH", "fail")
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!("{STEADY}\nCoverage held; no issue filed.\n")
    );
    assert_eq!(log!(scratch), "", "no gh call when the coverage held");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_failing_request_is_reported_with_its_address()
{
    let scratch = scratch!("curl-fail");
    let output = run!(scratch, ["--threshold", "0.5"], [("FAKE_CURL", "fail")]);
    assert_eq!(output.status.code(), Some(2_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!(
            "coverage-guard: `https://api.codecov.io/api/v2/github/gandr-lang/repos/gandr/commits/{HEAD}/` \
             failed: exit status: 22: curl: (22) The requested URL returned error: 404\n"
        )
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_failing_gh_is_reported_with_its_message()
{
    let scratch = scratch!("gh-fail");
    let output = run!(scratch, ["--threshold", "0.5", "--file-issue"], [
        ("FAKE_COVERAGE", "drop"),
        ("FAKE_GH", "fail")
    ]);
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("coverage-guard: `") && stderr.ends_with("HTTP 401: Bad credentials\n"),
        "{stderr}"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_pending_upload_is_refused_once_the_wait_ends()
{
    let scratch = scratch!("pending");
    let output = run!(scratch, ["--threshold", "0.5", "--wait", "0"], [
        ("FAKE_COVERAGE", "drop"),
        ("FAKE_HEAD", "pending")
    ]);
    assert_eq!(output.status.code(), Some(2_i32));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!(
            "coverage-guard: Codecov has not processed the upload of {HEAD}: its state is `pending`\n"
        )
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn an_unlisted_head_or_a_missing_baseline_is_refused()
{
    let scratch = scratch!("baseline");
    for (listing, refusal) in [
        (
            "unlisted",
            format!("{HEAD} is not among the uploads Codecov lists for main"),
        ),
        (
            "nobase",
            format!("no processed upload of main precedes {HEAD}"),
        ),
    ] {
        let output = run!(scratch, ["--threshold", "0.5"], [
            ("FAKE_COVERAGE", "drop"),
            ("FAKE_LISTING", listing)
        ]);
        assert_eq!(output.status.code(), Some(2_i32), "{listing}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("coverage-guard: {refusal}\n"),
            "{listing}"
        );
    }
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_malformed_threshold_exits_two()
{
    let scratch = scratch!("malformed");
    let output = run!(scratch, ["--threshold", "0.125"], [("FAKE_CURL", "fail")]);
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("`0.125` is not a number of points with at most two decimals"),
        "{stderr}"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}
