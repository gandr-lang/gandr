//! The report, the filing on each function's issue and the exit codes,
//! observed by spawning the binary with the fake `gh` of `tests/fakes` first
//! on the path.
//!
//! The fake answers the check-run query with `FAKE_CHECKS`, one JSON object a
//! line, the pull-request query with `FAKE_PULLS` (or `FAKE_PULL` for one
//! named by `--pull`), an issue's comment listing with `FAKE_COMMENTS`, one
//! JSON object a line, and the issue listing with `FAKE_GH_ISSUES`. An
//! artifact `<name>` exists, kept by run 7, when `FAKE_REPORTS/<name>` is a
//! directory, and downloading it copies that directory's files. It logs every
//! invocation to `FAKE_GH_LOG` and writes each body it is fed to
//! `FAKE_GH_BODY.<verb>-<issue>`, or `FAKE_GH_BODY.patch-<comment>` for an
//! edited comment; a created issue and a posted comment are numbered by the
//! log's length. It fails every invocation under `FAKE_GH=fail`.
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

/// The base of [`SPREAD`]'s check.
const BASE: &str = "71dc6038d0f6e7c8a1f2b3c4d5e6f7a8b9c0d1e2";

/// A failed `gandr-timing` check against [`BASE`] naming `decide` at +40 %
/// and `normalize` at +8 %.
const SPREAD: &str = "[`76dd52f`](https://github.com/gandr-lang/gandr/commit/76dd52f) (`theory-model-record`) vs [`71dc603`](https://github.com/gandr-lang/gandr/commit/71dc6038d0f6e7c8a1f2b3c4d5e6f7a8b9c0d1e2)
Wall time `100.00 ms → 102.00 ms` **+2.0%**

**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `100 µs → 140 µs` **+40%** · fails the check
⚠️ [`gandr_theory_coherent_resolutions::rewrite::normalize`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/theory-coherent-resolutions/src/rewrite.rs#L171): avg `100 µs → 108 µs` **+8.0%** · fails the check
";

/// The head whose `gandr-timing` check #1545 left open, filed under no pull
/// request.
const REPLAYED_HEAD: &str = "73f2e468d48dfd25332b479e7ee451195301e227";

/// [`REPLAYED_HEAD`]'s failed `gandr-timing` check, its related metrics
/// dropped: the wall time +28 % and three functions +23 to +32 % against
/// `ac58445`.
const REPLAYED_TIMING: &str = "<!-- hotpath:benchmark=gandr-timing -->
### `gandr-timing` · ⚠️ 3 regressions

[`def8465`](https://github.com/gandr-lang/gandr/commit/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7) (`theory-1886-native-j`) vs [`ac58445`](https://github.com/gandr-lang/gandr/commit/ac58445989aee8c21905b9d91d7f9d18b0ab5427) (newest on `main`; the branch point [`871d623`](https://github.com/gandr-lang/gandr/commit/871d62326a92b16d78d12de7c1a8f10cb9bca7c4) has no report)
Wall time `412.30 ms → 528.87 ms` **+28%**

**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/core-checker/src/module.rs#L1045): avg `190.88 µs → 251.64 µs` **+32%** · fails the check
⚠️ [`gandr_theory_coherent_resolutions::rewrite::normalize`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/theory-coherent-resolutions/src/rewrite.rs#L171): avg `7.76 µs → 9.79 µs` **+26%** · fails the check
⚠️ [`gandr_theory_coherent_resolutions::overlap::interior_overlaps_between`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/theory-coherent-resolutions/src/overlap.rs#L1054): avg `6.74 µs → 8.30 µs` **+23%** · fails the check
";

/// [`REPLAYED_HEAD`]'s failed `gandr` check, its related metrics dropped:
/// `rule completion`'s allocations +4.1 %.
const REPLAYED_GANDR: &str = "<!-- hotpath:benchmark=gandr -->
### `gandr` · ⚠️ 1 regression, 🚀 1 improvement

[`def8465`](https://github.com/gandr-lang/gandr/commit/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7) (`theory-1886-native-j`) vs [`ac58445`](https://github.com/gandr-lang/gandr/commit/ac58445989aee8c21905b9d91d7f9d18b0ab5427) (newest on `main`; the branch point [`871d623`](https://github.com/gandr-lang/gandr/commit/871d62326a92b16d78d12de7c1a8f10cb9bca7c4) has no report)
Wall time `411.23 ms → 531.93 ms` **+29%**

**Functions · allocations**
⚠️ [`rule completion`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/surface-driver/benches/hotpath.rs#L288): avg `36509 → 37991` **+4.1%**, total **+4.1%** · fails the check
🚀 [`gandr_surface_lowering::coincide::decide`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/surface-lowering/src/coincide.rs#L827): avg `29848 → 24089` **-19%**
";

/// The report its two failed checks print and comment.
const BODY: &str = "A hotpath check failed on [#1358](https://github.com/gandr-lang/gandr/pull/1358) (`theory-model-record`) at [`914a768`](https://github.com/gandr-lang/gandr/commit/914a768fb32501be92e5cb4d28ce6613dfa01022).
The check is not required, so nothing waited for it. The index above holds this regression's row.
Its body carries no settled `hotpath: accepted — <benchmark> …` verdict for `gandr`, `gandr-timing`: the hotpath verdict is missing.

## `hotpath / gandr`

[The run](https://github.com/gandr-lang/gandr/runs/119144034179). Wall time `401.60 ms → 510.60 ms` **+27%**

<details><summary>Functions · allocations — 2 sites regressed</summary>

- [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%**, total `452181 → 813738` **+80%**
- [`lsp keystroke`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/surface-driver/benches/hotpath.rs#L177): avg `59331 → 61258` **+3.2%**, total **+3.2%**

</details>

## `hotpath / gandr-timing`

[The run](https://github.com/gandr-lang/gandr/runs/119144057632). Wall time `401.84 ms → 510.08 ms` **+27%**

<details><summary>Functions · timing — 1 site regressed</summary>

- [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `284.34 µs → 411.59 µs` **+45%**

</details>
";

/// The body of `decide`'s issue before its table.
const DECIDE_HEAD: &str = "The hotpath guard's regressions of `gandr_core_checker::module::decide` (`crates/core-checker`), as the `hotpath / <series>` checks measure it: this body is the index, one row per pull request and series; each pull request's report is one comment below, edited by its later runs. The guard rewrites the rows and keeps the rest of this body as written.

## Index

";

/// The index table's heading and alignment rows.
const HEADING: &str = "| pull request | commit | series | metric | delta | status | report |
| --- | --- | --- | --- | --- | --- | --- |
";

/// The body of every guard-opened issue after its rows.
const TAIL: &str = "
## Lint

Owed once for the function, by the first fix that lands under this issue: whether a quenchant dylint could have refused the pattern that regressed, as the rule it would check.

## Close

The guard closes this issue when every row is `fixed`, `accepted` or `runner shift`, and reopens it on the next `open` row. A `runner shift` row states the run's global shift: the median move of every function both timing reports measure, and how many they are.
";

/// The commit cell of [`HEAD`].
const COMMIT: &str = "[`914a768`](https://github.com/gandr-lang/gandr/commit/914a768fb32501be92e5cb4d28ce6613dfa01022)";

/// `decide`'s issue body holding `$rows`, each a row's line, collapsed under
/// the summary counting them and their open rows.
macro_rules! index {
    ($($row:expr),* $(,)?) => {{
        let rows: Vec<String> = vec![$($row.to_string()),*];
        let open = rows
            .iter()
            .filter(|row| row.split(" | ").nth(5).is_some_and(|status| status.starts_with("open")))
            .count();
        let standing = if open > 0 { format!("{open} open") } else { String::from("settled") };
        let regressions = if rows.len() == 1 { "regression" } else { "regressions" };
        format!(
            "{DECIDE_HEAD}<details><summary>{} {regressions} — {standing}</summary>\n\n{HEADING}{}\n</details>\n{TAIL}",
            rows.len(),
            rows.iter().map(|row| format!("{row}\n")).collect::<String>()
        )
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
            .args([
                "--policies",
                concat!(env!("CARGO_MANIFEST_DIR"), "/../../hotpath"),
            ])
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

/// The `gh` invocations the fake in `$root` logged that write an issue or
/// edit a comment.
macro_rules! writes {
    ($root:expr) => {
        std::fs::read_to_string($root.join("log"))
            .unwrap()
            .lines()
            .filter(|line| {
                (line.starts_with("issue ") && !line.starts_with("issue list"))
                    || line.starts_with("api --method")
            })
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
}

/// The marker of pull request 1358's report comment.
const MARKER: &str = "<!-- hotpath: pr=1358 -->";

/// The comment listing of an issue holding pull request 1358's marked
/// report as comment 1, pull request 1400's as comment 2, and a person's
/// comment quoting 1358's marker on a later line as comment 3.
///
/// # Specification
/// trivial.
fn comments() -> String
{
    [
        (1_u64, format!("{MARKER}\nthe earlier report")),
        (
            2_u64,
            "<!-- hotpath: pr=1400 -->\nanother pull request's report".to_owned(),
        ),
        (3_u64, format!("A person, quoting:\n{MARKER}")),
    ]
    .into_iter()
    .map(|(id, body)| {
        serde_json::json!({
            "id": id,
            "html_url": format!("https://example.invalid/issues/4#issuecomment-{id}"),
            "body": body,
        })
        .to_string()
    })
    .collect::<Vec<_>>()
    .join("\n")
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
    assert_eq!(
        body!(scratch, "comment", 4_u64),
        format!("{MARKER}\n{BODY}")
    );
    assert_eq!(body!(scratch, "edit", 4_u64), index![
        format!(
            "| #1358 | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%**, total \
                 `452181 → 813738` **+80%** | open | \
                 [run](https://github.com/gandr-lang/gandr/runs/119144034179), \
                 [comment](https://example.invalid/issues/4#issuecomment-5) |"
        ),
        format!(
            "| #1358 | {COMMIT} | `gandr-timing` | timing | avg `284.34 µs → 411.59 µs` \
                 **+45%** | open | [run](https://github.com/gandr-lang/gandr/runs/119144057632), \
                 [comment](https://example.invalid/issues/4#issuecomment-5) |"
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

/// `decide`'s row for pull request `$number` in `gandr`, open, linking its
/// comment `$comment`.
macro_rules! open_row {
    ($number:expr, $comment:expr) => {
        format!(
            "| #{} | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%** | open | \
             [run](https://github.com/gandr-lang/gandr/runs/1), \
             [comment](https://example.invalid/issues/4#issuecomment-{}) |",
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
    let comments = comments()
        .lines()
        .filter(|line| !line.contains("pr=1400"))
        .collect::<Vec<_>>()
        .join("\n");
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str()),
        ("FAKE_COMMENTS", comments.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(writes!(scratch), [
        "issue comment 4 --body-file -",
        "issue edit 4 --body-file - --add-label kind:performance --add-label area:core",
    ]);
    assert!(
        body!(scratch, "comment", 4_u64).starts_with("<!-- hotpath: pr=1400 -->\n"),
        "the second pull request's comment carries its own marker"
    );
    assert_eq!(
        body!(scratch, "edit", 4_u64),
        index![
            open_row!(1358_u64, 1_u64),
            format!(
                "| #1400 | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%** | open \
                 | [run](https://github.com/gandr-lang/gandr/runs/9), \
                 [comment](https://example.invalid/issues/4#issuecomment-5) |"
            ),
        ],
        "two pull requests, two rows, each with its comment"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_later_run_edits_its_comment_and_row()
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
    let comments = comments();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str()),
        ("FAKE_COMMENTS", comments.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(
        String::from_utf8_lossy(&output.stdout).ends_with("\nUpdated #4, open.\n"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        writes!(scratch),
        [
            "api --method PATCH repos/gandr-lang/gandr/issues/comments/1 -F body=@- --silent",
            "issue edit 4 --body-file - --add-label kind:performance --add-label area:core"
        ],
        "the pull request's own marked comment is edited; none is posted"
    );
    let edited = body!(scratch, "patch", 1_u64);
    assert!(
        edited.starts_with(&format!("{MARKER}\nA hotpath check failed on [#1358]")),
        "{edited}"
    );
    assert!(
        edited.contains("(https://github.com/gandr-lang/gandr/runs/9)"),
        "the comment names the later run: {edited}"
    );
    assert_eq!(
        body!(scratch, "edit", 4_u64),
        index![open_row!(1358_u64, 1_u64).replace("runs/1)", "runs/9)")],
        "one row, naming the later run and linking the one comment"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn the_event_s_pull_request_names_a_force_pushed_commit()
{
    let scratch = scratch!("force-pushed");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let pull = r#"{"number":1358,"html_url":"https://github.com/gandr-lang/gandr/pull/1358","head":{"ref":"theory-model-record","sha":"b52c58585c2365b2e677525bc33723d1019aa2c5"}}"#;
    let output = run!(scratch, HEAD, ["--pull", "1358", "--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", "[]"),
        ("FAKE_PULL", pull)
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(
        String::from_utf8_lossy(&output.stdout).starts_with("A hotpath check failed on [#1358]"),
        "the restack moved the head on, and the event still names the pull request: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        body!(scratch, "comment", 4_u64).starts_with(&format!("{MARKER}\n")),
        "filed under the pull request, not the bare commit"
    );
    assert!(
        std::fs::read_to_string(scratch.join("log"))
            .unwrap()
            .contains("api repos/gandr-lang/gandr/pulls/1358\n"),
        "read by its number"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_passing_run_edits_its_comment_and_marks_its_row_fixed()
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
    let comments = comments();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str()),
        ("FAKE_COMMENTS", comments.as_str())
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
            "api --method PATCH repos/gandr-lang/gandr/issues/comments/1 -F body=@- --silent",
            "issue edit 4 --body-file - --add-label kind:performance",
            "issue close 4"
        ],
        "only the issue with the pull request's open row: its comment edited, none posted; \
         every row settled closes it"
    );
    assert_eq!(
        body!(scratch, "patch", 1_u64),
        format!(
            "{MARKER}\nNo hotpath check failed at \
             [`914a768`](https://github.com/gandr-lang/gandr/commit/{HEAD}).\n"
        ),
        "the green run says so in the comment"
    );
    let fixed = open_row!(1358_u64, 1_u64).replace(
        "| open |",
        "| fixed — `hotpath / gandr` passed at [`914a768`](https://github.com/gandr-lang/gandr/runs/11) |",
    );
    assert_eq!(body!(scratch, "edit", 4_u64), index![fixed, shift]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_benchmark_both_failed_and_passed_fixes_only_the_rows_it_did_not_regress()
{
    let scratch = scratch!("rerun-passed");
    let checks = [
        check!(
            "hotpath / gandr",
            "completed",
            Some("failure"),
            9_u64,
            DECIDE
        ),
        check!("hotpath / gandr", "completed", Some("success"), 11_u64, ""),
    ]
    .join("\n");
    let issues = serde_json::json!([
        issue!(
            4_u64,
            "perf: gandr_core_checker::module::decide",
            "OPEN",
            index![open_row!(1358_u64, 1_u64)]
        ),
        issue!(5_u64, "perf: lsp keystroke", "OPEN", index![open_row!(
            1358_u64, 2_u64
        )]),
    ])
    .to_string();
    let pulls = pulls!(1358_u64);
    let comments = comments();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str()),
        ("FAKE_COMMENTS", comments.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(
        writes!(scratch),
        [
            "api --method PATCH repos/gandr-lang/gandr/issues/comments/1 -F body=@- --silent",
            "issue edit 4 --body-file - --add-label kind:performance --add-label area:core",
            "api --method PATCH repos/gandr-lang/gandr/issues/comments/1 -F body=@- --silent",
            "issue edit 5 --body-file - --add-label kind:performance",
            "issue close 5"
        ],
        "the function the failed check names stays open; the other, which the pass touches, \
         closes; each edits the pull request's comment and posts none"
    );
    assert_eq!(
        body!(scratch, "edit", 4_u64),
        index![open_row!(1358_u64, 1_u64).replace("runs/1)", "runs/9)")],
        "the regressed row names the failed run and is not fixed by the passing one"
    );
    let fixed = open_row!(1358_u64, 2_u64).replace(
        "| open |",
        "| fixed — `hotpath / gandr` passed at [`914a768`](https://github.com/gandr-lang/gandr/runs/11) |",
    );
    assert_eq!(body!(scratch, "edit", 5_u64), index![fixed]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

/// A ticked accepted verdict for `gandr`, as the obligations section holds it.
const ACCEPTED: &str = "hotpath: accepted — gandr exercises record literals; 31 allocations per \
                        record; an arena per record was considered and loses to the shared one";

/// The pull requests GitHub associates with the head: pull request 1358,
/// whose body carries [`ACCEPTED`] ticked.
///
/// # Specification
/// trivial.
fn accepting_pull() -> String
{
    serde_json::json!([{
        "number": 1358,
        "html_url": "https://github.com/gandr-lang/gandr/pull/1358",
        "head": {"ref": "theory-model-record", "sha": HEAD},
        "body": format!(
            "## Re-verification\n\n### Hotpath\n\n- [x] {ACCEPTED} <!-- ack hotpath-verdict -->\n"
        ),
    }])
    .to_string()
}

#[test]
fn a_landing_with_an_accepted_verdict_files_no_issue()
{
    let scratch = scratch!("accepted");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let pulls = accepting_pull();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", "[]")
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(
            "\nIts body accepts this growth with a settled hotpath verdict, so its rows read \
             `accepted`.\n"
        ) && stdout.ends_with(
            "\nNo issue was filed: no regression stands unaccepted and no row was fixed.\n"
        ),
        "{stdout}"
    );
    assert_eq!(
        writes!(scratch),
        Vec::<String>::new(),
        "an accepted regression opens no issue"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn an_unaccepted_benchmark_beside_an_accepted_one_still_files()
{
    let scratch = scratch!("accepted-settles");
    let checks = [
        check!(
            "hotpath / gandr",
            "completed",
            Some("failure"),
            9_u64,
            DECIDE
        ),
        check!(
            "hotpath / gandr-timing",
            "completed",
            Some("failure"),
            10_u64,
            TIMING
        ),
    ]
    .join("\n");
    let earlier = "| #1300 | x | `gandr` | allocations | +3% | fixed — earlier | #1493 |";
    let issues = serde_json::json!([issue!(
        4_u64,
        "perf: gandr_core_checker::module::decide",
        "CLOSED",
        index![earlier]
    )])
    .to_string();
    let pulls = accepting_pull();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(
        String::from_utf8_lossy(&output.stdout).contains(
            "\nIts body carries no settled `hotpath: accepted — <benchmark> …` verdict for \
             `gandr-timing`: the hotpath verdict is missing.\n"
        ),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let writes = writes!(scratch);
    assert_eq!(
        writes.first().map(String::as_str),
        Some("issue comment 4 --body-file -"),
        "the unaccepted timing regression owes the comment: {writes:?}"
    );
    assert_eq!(
        writes.get(1 ..).unwrap_or_default(),
        [
            "issue edit 4 --body-file - --add-label kind:performance --add-label area:core",
            "issue reopen 4"
        ],
        "its open timing row reopens the issue"
    );
    // The commit's comment, owed by the timing row, is linked from both rows.
    let accepted = format!(
        "| #1358 | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%** | accepted — \
         {} | [run](https://github.com/gandr-lang/gandr/runs/9), [comment]",
        ACCEPTED.trim_start_matches("hotpath: accepted — ")
    );
    let body = body!(scratch, "edit", 4_u64);
    assert!(
        body.contains(&format!("{earlier}\n{accepted}"))
            && body.contains(
                "| `gandr-timing` | timing | avg `284.34 µs → 411.59 µs` **+45%** | open |"
            ),
        "the accepted row beside the open timing one: {body}"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn an_accepted_landing_settles_its_issue_without_a_comment()
{
    let scratch = scratch!("accepted-alone");
    let checks = check!(
        "hotpath / gandr",
        "completed",
        Some("failure"),
        9_u64,
        DECIDE
    );
    let earlier = "| #1300 | x | `gandr` | allocations | +3% | fixed — earlier | #1493 |";
    let issues = serde_json::json!([issue!(
        4_u64,
        "perf: gandr_core_checker::module::decide",
        "CLOSED",
        index![earlier]
    )])
    .to_string();
    let pulls = accepting_pull();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_GH_ISSUES", issues.as_str())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(
        writes!(scratch),
        ["issue edit 4 --body-file - --add-label kind:performance --add-label area:core"],
        "no comment, and the issue stays closed"
    );
    let accepted = format!(
        "| #1358 | {COMMIT} | `gandr` | allocations | avg `1444 → 2558` **+77%** | accepted — \
         {} | [run](https://github.com/gandr-lang/gandr/runs/9) |",
        ACCEPTED.trim_start_matches("hotpath: accepted — ")
    );
    assert_eq!(body!(scratch, "edit", 4_u64), index![earlier, accepted]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

/// #2546: `73f2e46`'s `gandr-timing` check, replayed over the two full
/// reports hotpath Cloud's diff of its run lists (16 functions, `ac58445`
/// against `73f2e46`), reads as a runner shift. Read from the summary alone,
/// its three functions spread +23 to +32 % and a call count moved, and the
/// same commit's allocation failure on `rule completion` blocked the reading,
/// so the guard left `decide`'s row `open`. Beside the global shift of
/// +27.2 %, `decide` moved +3.7 %; the allocation failure files on its own.
#[test]
fn a_runner_shift_is_read_over_every_function()
{
    let scratch = scratch!("replayed");
    let checks = [
        check!(
            "hotpath / store",
            "completed",
            Some("success"),
            120_189_597_702_u64,
            ""
        ),
        check!(
            "hotpath / gandr-timing",
            "completed",
            Some("failure"),
            120_189_503_764_u64,
            REPLAYED_TIMING
        ),
        check!(
            "hotpath / gandr",
            "completed",
            Some("failure"),
            120_189_487_942_u64,
            REPLAYED_GANDR
        ),
    ]
    .join("\n");
    let output = run!(scratch, REPLAYED_HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        (
            "FAKE_REPORTS",
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/reports")
        )
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(writes!(scratch), [
        "issue create --title perf: gandr_core_checker::module::decide --body-file - --label \
         kind:performance --label area:core",
        "issue close 8",
        "issue create --title perf: \
         gandr_theory_coherent_resolutions::overlap::interior_overlaps_between --body-file - \
         --label kind:performance --label area:theory",
        "issue close 10",
        "issue create --title perf: gandr_theory_coherent_resolutions::rewrite::normalize \
         --body-file - --label kind:performance --label area:theory",
        "issue close 12",
        "issue create --title perf: rule completion --body-file - --label kind:performance \
         --label area:surface",
        "issue comment 14 --body-file -",
        "issue edit 14 --body-file - --add-label kind:performance --add-label area:surface",
    ]);
    let commit = format!("[`73f2e46`](https://github.com/gandr-lang/gandr/commit/{REPLAYED_HEAD})");
    assert_eq!(body!(scratch, "create", 8_u64), index![format!(
        "| `73f2e46` | {commit} | `gandr-timing` | timing | avg `190.88 µs → 251.64 µs` **+32%** \
         | runner shift — the 16 functions both reports time moved +27.2 % at the median, and \
         none moved past the policy's threshold beside it | \
         [run](https://github.com/gandr-lang/gandr/runs/120189503764) |"
    )]);
    assert!(
        body!(scratch, "edit", 14_u64).contains(&format!(
            "| `73f2e46` | {commit} | `gandr` | allocations | avg `36509 → 37991` **+4.1%**, \
             total **+4.1%** | open | [run](https://github.com/gandr-lang/gandr/runs/120189487942), \
             [comment](https://example.invalid/issues/14#issuecomment-15) |"
        )),
        "the allocation failure files on its own function"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn one_function_past_a_quiet_runner_files_alone()
{
    let scratch = scratch!("quiet");
    // Writes `sha`'s full timing report: `decide`, `normalize` and twelve other
    // functions at the given averages in µs, each called 50 times, and a wall
    // time of `wall` milliseconds.
    let side = |sha: &str, decide: u64, normalize: u64, others: u64, wall: u64| {
        let mut rows = vec![
            ("gandr_core_checker::module::decide".to_owned(), decide),
            (
                "gandr_theory_coherent_resolutions::rewrite::normalize".to_owned(),
                normalize,
            ),
        ];
        rows.extend((0_u8 .. 12).map(|index| (format!("function {index}"), others)));
        let data = rows
            .iter()
            .map(|&(ref name, avg)| {
                serde_json::json!({
                    "name": name,
                    "calls": 50_u64,
                    "avg": format!("{avg} µs"),
                    "total": format!("{} µs", avg.checked_mul(50).unwrap()),
                    "percent_total": "1.00%",
                })
            })
            .collect::<Vec<_>>();
        let report = serde_json::json!({
            "functions_timing": {
                "total_elapsed_ns": wall.checked_mul(1_000_000).unwrap(),
                "data": data,
            },
        });
        let dir = scratch.join(format!("reports/hotpath-{sha}"));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("gandr-timing.json"), report.to_string()).unwrap();
    };
    side(BASE, 100, 100, 100, 100);
    side(HEAD, 140, 108, 102, 102);
    let checks = check!(
        "hotpath / gandr-timing",
        "completed",
        Some("failure"),
        21_u64,
        SPREAD
    );
    let pulls = pulls!(1358_u64);
    let reports = scratch.join("reports");
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", pulls.as_str()),
        ("FAKE_REPORTS", reports.to_str().unwrap())
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert_eq!(
        writes!(scratch),
        [
            "issue create --title perf: gandr_core_checker::module::decide --body-file - --label \
             kind:performance --label area:core",
            "issue comment 8 --body-file -",
            "issue edit 8 --body-file - --add-label kind:performance --add-label area:core",
        ],
        "`normalize` at +8 % is +5.9 % beside the +2 % shift, under 7.5 %"
    );
    assert_eq!(body!(scratch, "edit", 8_u64), index![format!(
        "| #1358 | {COMMIT} | `gandr-timing` | timing | avg `100 µs → 140 µs` **+40%** | open | \
         [run](https://github.com/gandr-lang/gandr/runs/21), \
         [comment](https://example.invalid/issues/8#issuecomment-9) |"
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
         914a768fb32501be92e5cb4d28ce6613dfa01022).\n\nNo issue was filed: no regression \
         stands unaccepted and no row was fixed.\n"
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
