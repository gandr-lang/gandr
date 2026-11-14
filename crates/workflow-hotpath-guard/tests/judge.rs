//! The judge's check body and exit codes, observed by spawning
//! `hotpath-judge` over report files written per case.

use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// The `store-timing` policy as `ci:hotpath` writes it.
const POLICY: &str = "pr_check = \"fail\"\n\n[functions]\nmin_percent_total = 1\n\n[functions.timing]\njudged = true\nfail_check = true\nmin_percent_change = 5\nmetrics = [\"avg\"]\nmin_calls = 20\n";

/// A case: its scratch directory's name and each side's `delete_part`
/// averages, one run each, in nanoseconds; that row is 0.65 % of the run.
struct Case
{
    /// The scratch directory's name.
    name: &'static str,
    /// The base's runs.
    base: &'static [u32],
    /// The commit's runs.
    head: &'static [u32],
    /// The first set's check, when the case is a second set.
    first: Option<&'static str>,
}

/// What a case's run left: the process's output and its scratch directory.
struct Ran
{
    /// The judge's exit status and streams.
    output: Output,
    /// Where the case's files live.
    root: PathBuf,
}

/// Writes the case's reports and policy, then runs the judge over them.
/// The check body is written to `check.json`.
///
/// # Specification
/// trivial.
fn judge(case: &Case) -> Ran
{
    let root = std::env::temp_dir().join(format!(
        "hotpath-judge-{}-{}",
        std::process::id(),
        case.name
    ));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(root.join("policy.toml"), POLICY).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_hotpath-judge"));
    command.args([
        "--repository",
        "gandr-lang/gandr",
        "--head",
        "17756fc17",
        "--base",
        "8d13f30c8",
        "--benchmark",
        "store-timing-push",
    ]);
    command.arg("--policy").arg(root.join("policy.toml"));
    command.arg("--output").arg(root.join("check.json"));
    if let Some(first) = case.first {
        std::fs::write(root.join("first.json"), first).unwrap();
        command.arg("--confirm").arg(root.join("first.json"));
    }
    for (flag, side, runs) in [
        ("--base-run", "base", case.base),
        ("--head-run", "head", case.head),
    ] {
        for (index, ns) in runs.iter().enumerate() {
            let path = root.join(format!("{side}-{index}.json"));
            std::fs::write(
                &path,
                format!(
                    r#"{{"functions_timing": {{"total_elapsed_ns": 5144385, "data": [{{"name": "gandr_storage_schema::store::edit::Store::delete_part", "calls": 384, "avg": "{ns} ns", "total": "31.2 µs", "percent_total": "0.65%", "location": {{"file": "crates/storage-schema/src/store/edit.rs", "line": 212}}}}]}}}}"#
                ),
            )
            .unwrap();
            command.arg(flag).arg(path);
        }
    }
    Ran {
        output: command.output().unwrap(),
        root,
    }
}

/// The check body a run wrote.
///
/// # Specification
/// trivial.
fn check(ran: &Ran) -> serde_json::Value
{
    serde_json::from_str(&std::fs::read_to_string(ran.root.join("check.json")).unwrap()).unwrap()
}

#[test]
fn a_regressed_push_writes_a_neutral_check()
{
    let ran = judge(&Case {
        name: "regressed",
        base: &[81, 78, 83],
        head: &[89, 88, 90],
        first: None,
    });
    assert!(ran.output.status.success(), "{:?}", ran.output);
    let body = check(&ran);
    assert_eq!(body["name"], "hotpath / store-timing-push");
    assert_eq!(
        body["conclusion"], "neutral",
        "one set of runs fails no row: {body}"
    );
    assert_eq!(
        body["suspects"],
        serde_json::json!(["Timing gandr_storage_schema::store::edit::Store::delete_part"])
    );
    let summary = body["output"]["summary"].as_str().unwrap();
    assert!(
        summary.contains("⚠️ [`gandr_storage_schema::store::edit::Store::delete_part`]"),
        "{summary}"
    );
    assert_eq!(
        String::from_utf8_lossy(&ran.output.stdout),
        summary,
        "standard output carries the summary"
    );
    let table = body["table"].as_str().unwrap();
    assert!(
        table.contains("|`gandr_storage_schema::store::edit::Store::delete_part`|avg|")
            && table.contains("|suspect: a second set decides|\n"),
        "one set's finding reads as a suspect in the comment's table: {table}"
    );
}

#[test]
fn a_second_set_fails_only_a_row_both_sets_find()
{
    let flagged =
        r#"{"suspects": ["Timing gandr_storage_schema::store::edit::Store::delete_part"]}"#;
    let confirmed = judge(&Case {
        name: "confirmed",
        base: &[81, 78, 83],
        head: &[89, 88, 90],
        first: Some(flagged),
    });
    assert!(confirmed.output.status.success(), "{:?}", confirmed.output);
    let body = check(&confirmed);
    assert_eq!(body["conclusion"], "failure", "both sets find delete_part");
    let table = body["table"].as_str().unwrap();
    assert!(
        table.contains("|fails: two sets find it|\n"),
        "a finding of both sets reads as failing in the comment's table: {table}"
    );
    let cleared = judge(&Case {
        name: "cleared",
        base: &[81, 78, 91],
        head: &[89, 88, 90],
        first: Some(flagged),
    });
    assert_eq!(
        check(&cleared)["conclusion"],
        "success",
        "the second set's runs overlap the base's"
    );
    let unflagged = judge(&Case {
        name: "unflagged",
        base: &[81, 78, 83],
        head: &[89, 88, 90],
        first: Some(r#"{"suspects": []}"#),
    });
    assert_eq!(
        check(&unflagged)["conclusion"],
        "success",
        "the first set flagged no row"
    );
}

#[test]
fn a_clear_push_writes_a_passed_check()
{
    let ran = judge(&Case {
        name: "clear",
        base: &[81, 78, 91],
        head: &[89, 88, 90],
        first: None,
    });
    assert!(ran.output.status.success(), "{:?}", ran.output);
    assert_eq!(check(&ran)["conclusion"], "success", "overlapping runs");
}

#[test]
fn a_missing_report_exits_two()
{
    let root = std::env::temp_dir().join(format!("hotpath-judge-{}-missing", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(root.join("policy.toml"), POLICY).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_hotpath-judge"))
        .args([
            "--repository",
            "gandr-lang/gandr",
            "--head",
            "17756fc17",
            "--base",
            "8d13f30c8",
            "--benchmark",
            "store-timing-band",
            "--base-run",
            "absent.json",
            "--head-run",
            "absent.json",
        ])
        .arg("--policy")
        .arg(root.join("policy.toml"))
        .arg("--output")
        .arg(root.join("check.json"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2_i32), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("hotpath-judge: `absent.json`: "),
        "{stderr}"
    );
    assert!(
        !root.join("check.json").exists(),
        "a refusal writes no check"
    );
}
