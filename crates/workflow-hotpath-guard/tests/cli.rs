//! The report, the filing on each function's issue and the exit codes,
//! observed by spawning the binary with the fake `gh` of `tests/fakes` first
//! on the path.
//!
//! The fake answers the check-run query with `FAKE_CHECKS`, one JSON object a
//! line, the pull-request query with `FAKE_PULLS` and the issue listing with
//! `FAKE_GH_ISSUES`. It logs every invocation to `FAKE_GH_LOG` and writes each
//! body it is fed to `FAKE_GH_BODY.<verb>-<issue>`; a created issue and a
//! posted comment are numbered by the log's length. It fails every
//! invocation under `FAKE_GH=fail`.
//!
//! The fake is a file of the tree, never written per case: macOS assesses an
//! executable the first time it runs, one at a time across the machine, and a
//! fresh fake per case queued past the 30-second limit in a whole-workspace
//! test run (#1574).
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::process::Command;

/// The head of a pull request whose hotpath checks failed.
const HEAD: &str = "914a768fb32501be92e5cb4d28ce6613dfa01022";

/// That pull request's failed `gandr` check's summary, trimmed to two sites.
const GANDR: &str = "<!-- hotpath:benchmark=gandr -->
### `gandr` · ⚠️ 2 regressions

[`76dd52f`](https://github.com/gandr-lang/gandr/commit/76dd52f) (`theory-model-record`) vs [`71dc603`](https://github.com/gandr-lang/gandr/commit/71dc603)
Wall time `401.60 ms → 510.60 ms` **+27%**

**Functions · allocations**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%**, total `452181 → 813738` **+80%** · fails the check
⚠️ [`lsp keystroke`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/surface-driver/benches/hotpath.rs#L177): avg `59331 → 61258` **+3.2%**, total **+3.2%** · fails the check

**Related metrics**

| Allocations | Calls | Avg |
|:--|--:|--:|
| [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009) | 313 → 318 +1.6% | 1444 → 2558 +77% |
";

/// Its failed `gandr-timing` check's summary.
const TIMING: &str = "<!-- hotpath:benchmark=gandr-timing -->
### `gandr-timing` · ⚠️ 1 regression

Wall time `401.84 ms → 510.08 ms` **+27%**

**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `284.34 µs → 411.59 µs` **+45%** · fails the check
";

/// A failed `gandr` check naming `decide` alone.
const DECIDE: &str = "**Functions · allocations**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%** · fails the check
";

/// #1516's failed `gandr-timing` check: the wall time +28 %, `decide` +31 %,
/// its calls unchanged.
const SHIFTED: &str = "Wall time `313.23 ms → 401.90 ms` **+28%**

**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/e6f58bf/crates/core-checker/src/module.rs#L1009): avg `179.28 µs → 235.30 µs` **+31%** · fails the check

| Timing | Calls | Avg |
|:--|--:|--:|
| [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/e6f58bf/crates/core-checker/src/module.rs#L1009) | 319 → 319 | 179.28 µs → 235.30 µs +31% |
";

/// The report its two failed checks print and comment.
const BODY: &str = "A hotpath check failed on [#1358](https://github.com/gandr-lang/gandr/pull/1358) (`theory-model-record`) at [`914a768`](https://github.com/gandr-lang/gandr/commit/914a768fb32501be92e5cb4d28ce6613dfa01022).
The check is not required, so nothing waited for it. The index above holds this regression's row.

## `hotpath / gandr`

[The run](https://github.com/gandr-lang/gandr/runs/119144034179). Wall time `401.60 ms → 510.60 ms` **+27%**

**Functions · allocations**

- [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%**, total `452181 → 813738` **+80%**
- [`lsp keystroke`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/surface-driver/benches/hotpath.rs#L177): avg `59331 → 61258` **+3.2%**, total **+3.2%**

## `hotpath / gandr-timing`

[The run](https://github.com/gandr-lang/gandr/runs/119144057632). Wall time `401.84 ms → 510.08 ms` **+27%**

**Functions · timing**

- [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `284.34 µs → 411.59 µs` **+45%**
";

/// The body of `decide`'s issue before its rows.
const DECIDE_HEAD: &str = "The hotpath guard's regressions of `gandr_core_checker::module::decide` (`crates/core-checker`), as the `hotpath / <series>` checks measure it: this body is the index, one row per pull request and series; each new regression's report is a comment below. The guard rewrites the rows and keeps the rest of this body as written.

## Index

| pull request | commit | series | metric | delta | status | report |
| --- | --- | --- | --- | --- | --- | --- |
";

/// The body of every guard-opened issue after its rows.
const TAIL: &str = "
## Lint

Owed once for the function, by the first fix that lands under this issue: whether a quenchant dylint could have refused the pattern that regressed, as the rule it would check.

## Close

The guard closes this issue when every row is `fixed`, `accepted` or `runner shift`, and reopens it on the next `open` row. A `runner shift` row proposes a policy change to the owner; the guard never applies one.
";

/// The commit cell of [`HEAD`].
const COMMIT: &str = "[`914a768`](https://github.com/gandr-lang/gandr/commit/914a768fb32501be92e5cb4d28ce6613dfa01022)";

/// `decide`'s issue body holding `$rows`, each a row's line.
macro_rules! index {
    ($($row:expr),* $(,)?) => {{
        let rows: Vec<String> = vec![$($row.to_string()),*];
        format!("{DECIDE_HEAD}{}{TAIL}", rows.iter().map(|row| format!("{row}\n")).collect::<String>())
    }};
}

/// A listing of one issue numbered `$number`, titled `$title`, in `$state`,
/// with `$body`.
macro_rules! issue {
    ($number:expr, $title:expr, $state:expr, $body:expr) => {
        serde_json::json!({
            "number": $number,
            "title": $title,
            "state": $state,
            "body": $body,
        })
    };
}

/// One check run named `$name`, completed with `$conclusion`, whose page is
/// run `$id` and whose summary is `$summary`.
macro_rules! check {
    ($name:expr, $status:expr, $conclusion:expr, $id:expr, $summary:expr) => {
        serde_json::json!({
            "name": $name,
            "status": $status,
            "conclusion": $conclusion,
            "html_url": format!("https://github.com/gandr-lang/gandr/runs/{}", $id),
            "summary": $summary,
        })
        .to_string()
    };
}

/// The commit's check runs: its two failed hotpath checks, the passing
/// `store` one, a pending one and a failed check of another name.
macro_rules! checks {
    () => {
        [
            check!(
                "hotpath / store",
                "completed",
                Some("success"),
                119144191482_u64,
                ""
            ),
            check!(
                "hotpath / gandr",
                "completed",
                Some("failure"),
                119144034179_u64,
                GANDR
            ),
            check!("CodeRabbit", "completed", Some("failure"), 1_u64, GANDR),
            check!(
                "hotpath / gandr-later",
                "in_progress",
                None::<&str>,
                2_u64,
                GANDR
            ),
            check!(
                "hotpath / gandr-timing",
                "completed",
                Some("failure"),
                119144057632_u64,
                TIMING
            ),
        ]
        .join("\n")
    };
}

/// The pull requests GitHub associates with the head: pull request `$number`,
/// which it heads.
macro_rules! pulls {
    ($number:expr) => {
        format!(
            r#"[{{"number":{0},"html_url":"https://github.com/gandr-lang/gandr/pull/{0}","head":{{"ref":"theory-model-record","sha":"{HEAD}"}}}}]"#,
            $number
        )
    };
}

/// A fresh scratch directory for the case `$name`, holding the fake's log.
macro_rules! scratch {
    ($name:literal) => {{
        let root =
            std::env::temp_dir().join(format!("hotpath-guard-{}-{}", std::process::id(), $name));
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(root.join("log"), "").unwrap();
        root
    }};
}

/// Runs the binary over `$sha` with `$args` after the repository and the
/// commit, the fake first on the path, its log and bodies in `$root`, and
/// each `($key, $value)` of `$env` set.
macro_rules! run {
    ($root:expr, $sha:expr, $args:expr, $env:expr) => {{
        let root: &std::path::Path = &$root;
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut paths = vec![std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fakes")];
        paths.extend(std::env::split_paths(&path));
        let mut command = Command::new(env!("CARGO_BIN_EXE_hotpath-guard"));
        command
            .args(["--repository", "gandr-lang/gandr", "--sha", $sha])
            .args($args)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .env("FAKE_GH_LOG", root.join("log"))
            .env("FAKE_GH_BODY", root.join("body"))
            .env_remove("GITHUB_REPOSITORY");
        for (key, value) in $env {
            command.env(key, value);
        }
        command.output().unwrap()
    }};
}

/// The `gh` invocations the fake in `$root` logged that write an issue.
macro_rules! writes {
    ($root:expr) => {
        std::fs::read_to_string($root.join("log"))
            .unwrap()
            .lines()
            .filter(|line| line.starts_with("issue ") && !line.starts_with("issue list"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
}

/// The body the fake in `$root` was fed by `$verb` on issue `$number`.
macro_rules! body {
    ($root:expr, $verb:literal, $number:expr) => {
        std::fs::read_to_string($root.join(format!("body.{}-{}", $verb, $number))).unwrap()
    };
}

#[test]
fn a_failed_check_opens_one_issue_per_function()
{
    let scratch = scratch!("open");
    let checks = checks!();
    let pulls = pulls!(1358_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "{BODY}\nOpened https://example.invalid/issues/4 (perf: \
             gandr_core_checker::module::decide), open.\n\nOpened \
             https://example.invalid/issues/7 (perf: lsp keystroke), open.\n"
        )
    );
    assert_eq!(writes!(scratch), [
        "issue create --title perf: gandr_core_checker::module::decide --body-file - --label \
         kind:performance --label area:core",
        "issue comment 4 --body-file -",
        "issue edit 4 --body-file - --add-label kind:performance --add-label area:core",
        "issue create --title perf: lsp keystroke --body-file - --label kind:performance \
         --label area:surface",
        "issue comment 7 --body-file -",
        "issue edit 7 --body-file - --add-label kind:performance --add-label area:surface",
    ]);
    assert_eq!(body!(scratch, "comment", 4_u64), BODY);
    let with = "<!-- with: gandr_core_checker::module::decide, lsp keystroke -->";
    assert_eq!(body!(scratch, "edit", 4_u64), index![
        format!(
            "| #1358 | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%**, total \
                 `452181 → 813738` **+80%** | open | \
                 [run](https://github.com/gandr-lang/gandr/runs/119144034179), \
                 [comment](https://example.invalid/issues/4#issuecomment-5) {with} |"
        ),
        format!(
            "| #1358 | {COMMIT} | `gandr-timing` | timing | avg `284.34 µs → 411.59 µs` \
                 **+45%** | open | [run](https://github.com/gandr-lang/gandr/runs/119144057632), \
                 [comment](https://example.invalid/issues/4#issuecomment-5) {with} |"
        ),
    ]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn only_a_completed_failed_hotpath_check_is_filed()
{
    let scratch = scratch!("only");
    let checks = checks!();
    let pulls = pulls!(1358_u64);
    let output = run!(scratch, HEAD, core::iter::empty::<&str>(), [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str())
    ]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        BODY,
        "the passing, pending and foreign checks are left out"
    );
    assert!(
        writes!(scratch).is_empty(),
        "no filing without --file-issue"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

/// `decide`'s row for pull request `$number` in `gandr`, open, its comment
/// `$comment` naming `decide` alone.
macro_rules! open_row {
    ($number:expr, $comment:expr) => {
        format!(
            "| #{} | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%** | open | \
             [run](https://github.com/gandr-lang/gandr/runs/1), \
             [comment](https://example.invalid/issues/4#issuecomment-{}) <!-- with: \
             gandr_core_checker::module::decide --> |",
            $number, $comment
        )
    };
}

#[test]
fn a_second_pull_request_adds_a_row_and_a_comment()
{
    let scratch = scratch!("second");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let issues = serde_json::json!([issue!(
        4_u64,
        "perf: gandr_core_checker::module::decide",
        "OPEN",
        index![open_row!(1358_u64, 1_u64)]
    )])
    .to_string();
    let pulls = pulls!(1400_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(writes!(scratch), [
        "issue comment 4 --body-file -",
        "issue edit 4 --body-file - --add-label kind:performance --add-label area:core",
    ]);
    assert_eq!(
        body!(scratch, "edit", 4_u64),
        index![
            open_row!(1358_u64, 1_u64),
            format!(
                "| #1400 | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%** | open \
                 | [run](https://github.com/gandr-lang/gandr/runs/9), \
                 [comment](https://example.invalid/issues/4#issuecomment-4) <!-- with: \
                 gandr_core_checker::module::decide --> |"
            ),
        ],
        "two pull requests, two rows, each with its comment"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_later_run_updates_its_row_without_a_comment()
{
    let scratch = scratch!("rerun");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let issues = serde_json::json!([issue!(
        4_u64,
        "perf: gandr_core_checker::module::decide",
        "OPEN",
        index![open_row!(1358_u64, 1_u64)]
    )])
    .to_string();
    let pulls = pulls!(1358_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(
        String::from_utf8_lossy(&output.stdout).ends_with("\nUpdated #4, open.\n"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(writes!(scratch), [
        "issue edit 4 --body-file - --add-label kind:performance --add-label area:core"
    ]);
    assert_eq!(
        body!(scratch, "edit", 4_u64),
        index![open_row!(1358_u64, 1_u64).replace("runs/1)", "runs/9)")],
        "the row names the later run and keeps its comment"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_passing_run_marks_its_row_fixed_without_a_comment()
{
    let scratch = scratch!("fixed");
    let checks = [
        check!("hotpath / gandr", "completed", Some("success"), 11_u64, ""),
        check!(
            "hotpath / gandr-timing",
            "completed",
            Some("success"),
            12_u64,
            ""
        ),
    ]
    .join("\n");
    let shift = format!(
        "| #1400 | {COMMIT} | `gandr-timing` | timing | avg `179.28 µs → 235.30 µs` **+31%** | \
         runner shift — moved together | [run](https://github.com/gandr-lang/gandr/runs/3) |"
    );
    let other = "| #1358 | x | `gandr` | allocations | +3% | fixed — earlier | #1493 |";
    let issues = serde_json::json!([
        issue!(
            4_u64,
            "perf: gandr_core_checker::module::decide",
            "OPEN",
            index![open_row!(1358_u64, 1_u64), shift]
        ),
        issue!(5_u64, "perf: lsp keystroke", "OPEN", index![other]),
        issue!(
            6_u64,
            "perf: #1358 regresses module::decide",
            "OPEN",
            "the earlier shape"
        ),
    ])
    .to_string();
    let pulls = pulls!(1358_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(
        String::from_utf8_lossy(&output.stdout).ends_with("\nUpdated #4, closed.\n"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        writes!(scratch),
        [
            "issue edit 4 --body-file - --add-label kind:performance",
            "issue close 4"
        ],
        "only the issue with the pull request's open row; every row settled closes it"
    );
    let fixed = open_row!(1358_u64, 1_u64).replace(
        "| open |",
        "| fixed — `hotpath / gandr` passed at [`914a768`](https://github.com/gandr-lang/gandr/runs/11) |",
    );
    assert_eq!(body!(scratch, "edit", 4_u64), index![fixed, shift]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_uniform_shift_is_a_runner_shift_row_without_a_comment()
{
    let scratch = scratch!("shift");
    let checks = [
        check!("hotpath / gandr", "completed", Some("success"), 11_u64, ""),
        check!(
            "hotpath / gandr-timing",
            "completed",
            Some("failure"),
            12_u64,
            SHIFTED
        ),
    ]
    .join("\n");
    let pulls = pulls!(1496_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(writes!(scratch), [
        "issue create --title perf: gandr_core_checker::module::decide --body-file - --label \
         kind:performance --label area:core",
        "issue close 4",
    ]);
    assert_eq!(body!(scratch, "create", 4_u64), index![format!(
        "| #1496 | {COMMIT} | `gandr-timing` | timing | avg `179.28 µs → 235.30 µs` **+31%** \
             | runner shift — the wall time and every regressed function moved +28 to +31 % \
             together, calls unchanged, allocations clean; proposed to the owner: raise the \
             policy's `min_percent_change` by 2.5 | \
             [run](https://github.com/gandr-lang/gandr/runs/12) |"
    )]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_new_regression_reopens_a_settled_issue()
{
    let scratch = scratch!("reopen");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let settled = "| #1300 | x | `gandr` | allocations | +3% | fixed — earlier | #1458 |";
    let issues = serde_json::json!([issue!(
        4_u64,
        "perf: gandr_core_checker::module::decide",
        "CLOSED",
        index![settled]
    )])
    .to_string();
    let pulls = pulls!(1358_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(writes!(scratch), [
        "issue comment 4 --body-file -",
        "issue edit 4 --body-file - --add-label kind:performance --add-label area:core",
        "issue reopen 4",
    ]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_commit_without_a_pull_request_is_filed_by_its_sha()
{
    let scratch = scratch!("bare");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", "[]")
    ]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.starts_with(
            "A hotpath check failed at [`914a768`](https://github.com/gandr-lang/gandr/commit/\
             914a768fb32501be92e5cb4d28ce6613dfa01022), which no pull request carries.\n"
        ),
        "{stdout}"
    );
    assert!(
        body!(scratch, "edit", 4_u64).contains(&format!("\n| `914a768` | {COMMIT} | `gandr` |")),
        "the row is keyed by the commit"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_clear_commit_files_nothing()
{
    let scratch = scratch!("clear");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("success"),
        3_u64,
        "### `gandr` · ✅ no regressions"
    );
    let pulls = pulls!(1358_u64);
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "No hotpath check failed at [`914a768`](https://github.com/gandr-lang/gandr/commit/\
         914a768fb32501be92e5cb4d28ce6613dfa01022).\n\nNo function regressed and no row was \
         fixed.\n"
    );
    assert!(
        writes!(scratch).is_empty(),
        "a passing run with no open row writes nothing"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_failing_gh_is_reported_with_its_message()
{
    let scratch = scratch!("gh-fail");
    let output = run!(scratch, HEAD, ["--file-issue"], [("FAKE_GH", "fail")]);
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("hotpath-guard: `") && stderr.ends_with("HTTP 401: Bad credentials\n"),
        "{stderr}"
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout), "");
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_malformed_commit_exits_two()
{
    let scratch = scratch!("malformed");
    let output = run!(
        scratch,
        "main",
        core::iter::empty::<&str>(),
        core::iter::empty::<(&str, &str)>()
    );
    assert_eq!(output.status.code(), Some(2_i32));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("`main` is not a commit: seven to forty lowercase hexadecimal digits"),
        "{stderr}"
    );
    assert_eq!(std::fs::read_to_string(scratch.join("log")).unwrap(), "");
    std::fs::remove_dir_all(&scratch).unwrap();
}
