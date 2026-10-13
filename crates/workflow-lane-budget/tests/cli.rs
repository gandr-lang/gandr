//! The report, the issue filing and the exit codes, observed by spawning the
//! binary with a fake `gh` first on the path.
//!
//! The fake lists runs 3, 2 and 1; run `N` holds a Clippy job of `N`00
//! seconds and a five-second detection job. Its issue listing is
//! `FAKE_GH_ISSUES`; it logs every invocation to `FAKE_GH_LOG` and the last
//! body it was fed to `FAKE_GH_BODY`.

/// The process-level cases, in a `cfg(test)` module so the crate's lint wall
/// reads them as test code rather than as shipping code.
#[cfg(test)]
mod cli
{
    use std::process::Command;

    /// The fake `gh`.
    const FAKE_GH: &str = r#"#!/bin/sh
printf '%s\n' "$*" >> "$FAKE_GH_LOG"
if [ "$FAKE_GH_MODE" = fail ]; then echo 'HTTP 401: Bad credentials' >&2; exit 1; fi
case "$1 $2" in
  'api --method')
    case "$4" in
      */workflows/ci.yml/runs) printf '3\n2\n1\n' ;;
      */runs/*/jobs) run=${4%/jobs}; run=${run##*/}; printf '%s00\tcheck Clippy wall\n5\tdetect changed-file categories\n' "$run" ;;
      *) echo "unexpected route: $4" >&2; exit 2 ;;
    esac ;;
  'issue list') printf '%s' "${FAKE_GH_ISSUES:-[]}" ;;
  'issue create') cat > "$FAKE_GH_BODY"; echo 'https://example.invalid/issues/7' ;;
  'issue edit') cat > "$FAKE_GH_BODY" ;;
  'issue reopen'|'issue close') ;;
  *) echo "unexpected: $*" >&2; exit 2 ;;
esac
"#;

    /// The report over runs 3 and 2 with Clippy's budget `BUDGET` and
    /// standing `STANDING`.
    const REPORT: &str = "Median job time over the last 2 merge-queue and pull-request runs of \
                          `ci.yml`, against the budgets in `nightly.yml`.\n\n\
                          | lane | median | budget | jobs | standing |\n\
                          | --- | ---: | ---: | ---: | --- |\n\
                          | check Clippy wall | 3m 20s | BUDGET | 2 | STANDING |\n\
                          \nRuns: 3, 2.\n";

    /// A fresh scratch directory for the case `$name` holding the fake `gh`.
    macro_rules! scratch {
        ($name:literal) => {{
            let root =
                std::env::temp_dir().join(format!("lane-budget-{}-{}", std::process::id(), $name));
            if root.exists() {
                std::fs::remove_dir_all(&root).unwrap();
            }
            std::fs::create_dir_all(&root).unwrap();
            let gh = root.join("gh");
            std::fs::write(&gh, FAKE_GH).unwrap();
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;
                std::fs::set_permissions(&gh, std::fs::Permissions::from_mode(0o755)).unwrap();
            }
            root
        }};
    }

    /// Runs the binary with `$args`, the fake in `$root` first on the path,
    /// the issue listing `$issues` and the fake's mode `$mode`, after
    /// clearing the fake's log.
    macro_rules! run {
        ($root:expr, $args:expr, $issues:expr, $mode:expr) => {{
            let root: &std::path::Path = &$root;
            let path = std::env::var_os("PATH").unwrap_or_default();
            let mut paths = vec![root.to_path_buf()];
            paths.extend(std::env::split_paths(&path));
            std::fs::write(root.join("log"), "").unwrap();
            Command::new(env!("CARGO_BIN_EXE_lane-budget"))
                .args($args)
                .env("PATH", std::env::join_paths(paths).unwrap())
                .env("FAKE_GH_LOG", root.join("log"))
                .env("FAKE_GH_BODY", root.join("body"))
                .env("FAKE_GH_ISSUES", $issues)
                .env("FAKE_GH_MODE", $mode)
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
            ""
        );
        assert_eq!(String::from_utf8_lossy(&output.stderr), "");
        assert!(output.status.success());
        let report = REPORT
            .replace("BUDGET", "2m 30s")
            .replace("STANDING", "**over**");
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
            log.contains("issue create --title CI lane budgets --body-file -"),
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
                &["issue edit 4 --body-file -", "issue close 4"][..],
            ),
            (
                "150",
                "CLOSED",
                "Reopened #4.",
                &["issue edit 4 --body-file -", "issue reopen 4"][..],
            ),
            (
                "150",
                "OPEN",
                "Updated #4.",
                &["issue edit 4 --body-file -"][..],
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
            let output = run!(scratch, &args, issues(state), "");
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
        let output = run!(scratch, ["--budget", "check Clippy wall=150"], "[]", "fail");
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
        let output = run!(scratch, ["--budget", "check Clippy wall"], "[]", "");
        assert_eq!(output.status.code(), Some(2_i32));
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(
                "`check Clippy wall` is not a job name, `=`, and a whole number of seconds"
            ),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(log!(scratch), "", "no gh call before the arguments parse");
        std::fs::remove_dir_all(&scratch).unwrap();
    }
}
