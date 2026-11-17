//! The comparison, the refusals and the exit codes of `spec-cost-ratio`,
//! observed by spawning the binary.
//!
//! `ratio/plain.xml` and `ratio/enforcing.xml` are a recorded pair: tests cut
//! from one workspace run's plain and enforcing nextest reports, timings
//! unchanged. They hold a test with a high ratio but under the floor, three
//! tests flagged, two tests that are not, and one test each report times
//! alone.
//!
//! The process-level cases, in a `cfg(test)` module so the crate's lint wall
//! reads them as test code rather than as shipping code.

use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// The directory of the recorded reports.
///
/// # Specification
/// trivial.
fn recorded() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("ratio")
}

/// Runs the binary with `arguments` after the baseline it names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the binary's output and exit status, run with the baseline
///   `5956d6f`, seven hours old, then `arguments`.
/// - provides: the invocation every case makes.
/// - fails: never.
/// - panics: when the binary cannot be spawned.
/// - executable: none — the outcome is the spawned process's.
///
/// # Adequacy
/// - hypothesis: L3 — every case reads the baseline back from the output or
///   depends on the binary running.
/// - witness: `tests::ratio::a_recorded_pair_reports_each_test_against_the_baseline`
fn run(arguments: &[&std::ffi::OsStr]) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_spec-cost-ratio"))
        .args(["--baseline-commit", "5956d6f", "--baseline-age-hours", "7"])
        .args(arguments)
        .output()
        .unwrap()
}

#[test]
fn a_recorded_pair_reports_each_test_against_the_baseline()
{
    let plain = recorded().join("plain.xml");
    let enforcing = recorded().join("enforcing.xml");
    let output = run(&[
        "--plain".as_ref(),
        plain.as_os_str(),
        "--enforcing".as_ref(),
        enforcing.as_os_str(),
    ]);
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "",
        "nothing on standard error"
    );
    assert!(output.status.success(), "exit 0 with flagged tests");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "### Specification cost per test\n\nEach test's time with its specifications enforced \
             over its time without them: this run's enforcing report over the plain baseline of \
             `main` at `5956d6f`, 7 h old. A ratio of 4.00× or more on a test taking at least \
             0.250 s enforcing is flagged.\n\n\
             | Test | Plain | Enforcing | Ratio | |\n\
             | --- | ---: | ---: | ---: | --- |\n\
             | `gandr-surface-parser::tests acceptance::run_binder_annotation_molds_clean` | \
             0.009 s | 0.778 s | 86.44× | flagged |\n\
             | `gandr-surface-parser parse::tests::arbitrary_source_parses_by_form_as_whole` | \
             0.128 s | 7.020 s | 54.84× | flagged |\n\
             | `gandr-surface-parser parse::tests::hostile_edits_reuse_only_equal_units` | 0.303 \
             s | 2.831 s | 9.34× | flagged |\n\
             | `gandr-core-nbe::teardown \
             teardown::a_spinal_deep_overlay_duplicates_and_tears_down_inside_a_small_stack` | \
             0.980 s | 2.304 s | 2.35× |  |\n\
             | `gandr-lang::cli cli::lsp_clients_share_one_engine_hub` | 2.117 s | 2.118 s | \
             1.00× |  |\n\n\
             6 tests in both reports: 3.562 s plain, 15.101 s enforcing, 4.23× overall; 3 \
             flagged. 1 only in the enforcing report, 1 only in the plain baseline.\n",
        "the 2× test under the floor is counted in the totals but not listed"
    );
}

#[test]
fn a_missing_report_is_refused_by_its_path()
{
    let plain = recorded().join("plain.xml");
    let missing = recorded().join("absent.xml");
    let output = run(&[
        "--plain".as_ref(),
        plain.as_os_str(),
        "--enforcing".as_ref(),
        missing.as_os_str(),
    ]);
    assert_eq!(output.status.code(), Some(2_i32), "a refusal exits 2");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "",
        "nothing printed"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .starts_with(&format!("spec-cost-ratio: {}: ", missing.display())),
        "the refusal names the report"
    );
}

#[test]
fn a_malformed_threshold_exits_two()
{
    let plain = recorded().join("plain.xml");
    let enforcing = recorded().join("enforcing.xml");
    let output = run(&[
        "--plain".as_ref(),
        plain.as_os_str(),
        "--enforcing".as_ref(),
        enforcing.as_os_str(),
        "--threshold".as_ref(),
        "2.505".as_ref(),
    ]);
    assert_eq!(output.status.code(), Some(2_i32), "a usage error exits 2");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "",
        "nothing printed"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("`2.505` is not a ratio with at most two decimals"),
        "clap reports the parse refusal"
    );
}
