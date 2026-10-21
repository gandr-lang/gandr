//! The report, the issue filing and the exit codes, observed by spawning the
//! binary with a fake `gh` first on the path.
//!
//! The fake answers the check-run query with `FAKE_CHECKS`, one JSON object a
//! line, and the pull-request query with `FAKE_PULLS`. Its issue listing is
//! `FAKE_GH_ISSUES`; it logs every invocation to `FAKE_GH_LOG` and the last
//! body it was fed to `FAKE_GH_BODY`, and fails every invocation under
//! `FAKE_GH=fail`.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::process::Command;

/// The fake `gh`.
const FAKE_GH: &str = r#"#!/bin/sh
printf '%s\n' "$*" >> "$FAKE_GH_LOG"
if [ "$FAKE_GH" = fail ]; then echo 'HTTP 401: Bad credentials' >&2; exit 1; fi
case "$1 $2" in
  'api --paginate') printf '%s\n' "$FAKE_CHECKS" ;;
  'api repos/'*) printf '%s' "${FAKE_PULLS:-[]}" ;;
  'issue list') printf '%s' "${FAKE_GH_ISSUES:-[]}" ;;
  'issue create') cat > "$FAKE_GH_BODY"; echo 'https://example.invalid/issues/7' ;;
  'issue edit') cat > "$FAKE_GH_BODY" ;;
  *) echo "unexpected: $*" >&2; exit 2 ;;
esac
"#;

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

/// The body its two failed checks file.
const BODY: &str = "A hotpath check failed on [#1358](https://github.com/gandr-lang/gandr/pull/1358) (`theory-model-record`) at [`914a768`](https://github.com/gandr-lang/gandr/commit/914a768fb32501be92e5cb4d28ce6613dfa01022).
The check is not required, so nothing waited for it. The triage lane routes this issue to the authoring lane; a later failed run updates it.

## `hotpath / gandr`

[The run](https://github.com/gandr-lang/gandr/runs/119144034179). Wall time `401.60 ms → 510.60 ms` **+27%**

**Functions · allocations**

- [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%**, total `452181 → 813738` **+80%**
- [`lsp keystroke`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/surface-driver/benches/hotpath.rs#L177): avg `59331 → 61258` **+3.2%**, total **+3.2%**

## `hotpath / gandr-timing`

[The run](https://github.com/gandr-lang/gandr/runs/119144057632). Wall time `401.84 ms → 510.08 ms` **+27%**

**Functions · timing**

- [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `284.34 µs → 411.59 µs` **+45%**

## Lint

The fix states whether a quenchant dylint could have refused the pattern that regressed, as the rule it would check. When it could, the lint lands in quenchant and on gandr's lint wall at once and is named here; when it could not, one sentence says why.
";

/// The title its two failed checks file.
const TITLE: &str = "perf: #1358 regresses module::decide, lsp keystroke";

/// The commit's check runs: its two failed hotpath checks, the passing
/// `store` one, a pending one and a failed check of another name.
macro_rules! checks {
    () => {{
        let check = |name: &str, status: &str, conclusion: Option<&str>, id: u64, summary: &str| {
            serde_json::json!({
                "name": name,
                "status": status,
                "conclusion": conclusion,
                "html_url": format!("https://github.com/gandr-lang/gandr/runs/{id}"),
                "summary": summary,
            })
            .to_string()
        };
        [
            check("hotpath / store", "completed", Some("success"), 119144191482, ""),
            check("hotpath / gandr", "completed", Some("failure"), 119144034179, GANDR),
            check("CodeRabbit", "completed", Some("failure"), 1, GANDR),
            check("hotpath / gandr-later", "in_progress", None, 2, GANDR),
            check("hotpath / gandr-timing", "completed", Some("failure"), 119144057632, TIMING),
        ]
        .join("\n")
    }};
}

/// The pull requests GitHub associates with the head: the one it heads,
/// labelled `area:theory` and `kind:feature`.
const PULLS: &str = r#"[{"number":1358,"html_url":"https://github.com/gandr-lang/gandr/pull/1358","head":{"ref":"theory-model-record","sha":"914a768fb32501be92e5cb4d28ce6613dfa01022"},"labels":[{"name":"area:theory"},{"name":"kind:feature"}]}]"#;

/// A fresh scratch directory for the case `$name` holding the fake.
macro_rules! scratch {
    ($name:literal) => {{
        let root =
            std::env::temp_dir().join(format!("hotpath-guard-{}-{}", std::process::id(), $name));
        if root.exists() {
            std::fs::remove_dir_all(&root).unwrap();
        }
        std::fs::create_dir_all(&root).unwrap();
        let path = root.join("gh");
        std::fs::write(&path, FAKE_GH).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        std::fs::write(root.join("log"), "").unwrap();
        root
    }};
}

/// Runs the binary over `$sha` with `$args` after the repository and the
/// commit, the fake in `$root` first on the path, and each `($key, $value)`
/// of `$env` set.
macro_rules! run {
    ($root:expr, $sha:expr, $args:expr, $env:expr) => {{
        let root: &std::path::Path = &$root;
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut paths = vec![root.to_path_buf()];
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
            .filter(|line| line.starts_with("issue create") || line.starts_with("issue edit"))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
}

#[test]
fn a_failed_check_opens_the_issue()
{
    let scratch = scratch!("open");
    let checks = checks!();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", PULLS)
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!("{BODY}\nOpened https://example.invalid/issues/7.\n")
    );
    assert_eq!(std::fs::read_to_string(scratch.join("body")).unwrap(), BODY);
    assert_eq!(writes!(scratch), [format!(
        "issue create --title {TITLE} --body-file - --label kind:performance --label \
         area:core --label area:surface --label area:theory"
    )]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn only_a_completed_failed_hotpath_check_is_filed()
{
    let scratch = scratch!("only");
    let checks = checks!();
    let output = run!(scratch, HEAD, core::iter::empty::<&str>(), [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", PULLS)
    ]);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout, BODY,
        "the passing, pending and foreign checks are left out"
    );
    assert!(
        writes!(scratch).is_empty(),
        "no filing without --file-issue"
    );
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_later_run_updates_the_pull_request_issue()
{
    let scratch = scratch!("update");
    let checks = checks!();
    let issues = r#"[{"number":9,"title":"perf: #135 regresses eval::step"},{"number":4,"title":"perf: #1358 regresses module::decide"}]"#;
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", PULLS),
        ("FAKE_GH_ISSUES", issues)
    ]);
    assert!(output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stdout).ends_with("\nUpdated #4.\n"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(writes!(scratch), [format!(
        "issue edit 4 --title {TITLE} --body-file - --add-label kind:performance --add-label \
         area:core --add-label area:surface --add-label area:theory"
    )]);
    assert_eq!(std::fs::read_to_string(scratch.join("body")).unwrap(), BODY);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_commit_without_a_pull_request_is_filed_by_its_sha()
{
    let scratch = scratch!("bare");
    let checks = checks!();
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
    assert_eq!(writes!(scratch), [
        "issue create --title perf: 914a768 regresses module::decide, lsp keystroke \
         --body-file - --label kind:performance --label area:core --label area:surface"
    ]);
    std::fs::remove_dir_all(&scratch).unwrap();
}

#[test]
fn a_clear_commit_files_nothing()
{
    let scratch = scratch!("clear");
    let checks = serde_json::json!({
        "name": "hotpath / gandr",
        "status": "completed",
        "conclusion": "success",
        "html_url": "https://github.com/gandr-lang/gandr/runs/3",
        "summary": "### `gandr` · ✅ no regressions",
    })
    .to_string();
    let output = run!(scratch, HEAD, ["--file-issue"], [
        ("FAKE_CHECKS", checks.as_str()),
        ("FAKE_PULLS", PULLS)
    ]);
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "No hotpath check failed at [`914a768`](https://github.com/gandr-lang/gandr/commit/\
         914a768fb32501be92e5cb4d28ce6613dfa01022).\n\nNo hotpath check failed; no issue filed.\n"
    );
    let log = std::fs::read_to_string(scratch.join("log")).unwrap();
    assert!(
        log.lines().all(|line| line.starts_with("api ")),
        "only the two reads when nothing failed: {log}"
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
