use std::path::Path;
use std::process::Command;
use std::process::Output;

/// Run the binary with `arguments` at the workspace `root`.
///
/// # Specification
/// trivial.
fn run(
    root: &Path,
    arguments: &[&str],
) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_twin-census"))
        .args(arguments)
        .arg("--root")
        .arg(root)
        .output()
        .expect("the binary runs")
}

/// The committed census is the census of this workspace, so a change of a
/// dependency of the emitter or of the crates fails this test until the
/// census is written again.
#[test]
fn the_committed_census_is_the_census_of_the_workspace()
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = run(&root, &["--check", "--cost"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "the committed census is the workspace's: {stderr}"
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).starts_with("crates under the emitter: "),
        "the run prints its counts"
    );
    assert!(
        stderr.contains("twin-census: cargo metadata: 1 call, "),
        "the cost names each part: {stderr}"
    );
}

/// The census of a fixture workspace has a changed row: the check exits one
/// and names the crate of that row.
#[test]
fn a_changed_row_exits_one_and_names_its_crate()
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/workspace");
    let output = run(&root, &["--check"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(1_i32),
        "a stale census exits one: {stderr}"
    );
    assert!(
        stderr.ends_with("The rows that differ: near\n"),
        "the refusal names the crate: {stderr}"
    );
}
