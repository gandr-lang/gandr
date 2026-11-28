//! The `artifacts` binary over a small git tree.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// A list with an output and a record.
const LIST: &str = r#"[
  {"name": "the census", "kind": "output", "paths": ["ledger/census.md"]},
  {"name": "the crate table", "kind": "record", "paths": ["crates/README.md"], "reason": "a person writes it"}
]"#;

/// Runs `git` with `arguments` in `root`, with an identity of this test and
/// no signature, and asserts that it succeeds.
///
/// # Specification
/// trivial.
fn git(
    root: &Path,
    arguments: &[&str],
)
{
    let status = Command::new("git")
        .arg("-C")
        .arg(root)
        .args([
            "-c",
            "user.name=test",
            "-c",
            "user.email=test@example.invalid",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(arguments)
        .status()
        .expect("git runs");
    assert!(status.success(), "git {arguments:?}");
}

/// A git tree of this test's own under the system's temporary directory,
/// with `files` written and committed.
///
/// # Specification
/// trivial.
fn tree(files: &[(&str, &str)]) -> PathBuf
{
    let root = std::env::temp_dir().join(format!("artifacts-cli-{}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&root);
    for &(path, text) in files {
        let path = root.join(path);
        std::fs::create_dir_all(path.parent().expect("a file has a directory"))
            .expect("the directory");
        std::fs::write(path, text).expect("the file");
    }
    git(&root, &["init", "-q"]);
    git(&root, &["add", "-A"]);
    git(&root, &["commit", "-q", "-m", "the tree"]);
    root
}

/// Runs `artifacts <command>` over `root`, with `--cost`.
///
/// # Specification
/// trivial.
fn run(
    command: &str,
    root: &Path,
) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_artifacts"))
        .arg(command)
        .arg("--root")
        .arg(root)
        .arg("--cost")
        .output()
        .expect("the binary runs")
}

/// A tree that keeps the list passes both commands. A tracked output exits
/// one for `tracked` and names its row. A file that a run writes, and a
/// changed record, exit one for `clean`.
#[test]
fn the_gate_refuses_a_tracked_output_and_an_unclean_checkout()
{
    let mut files = vec![
        (".config/replay/artifacts.json", LIST),
        ("crates/README.md", "# crates\n"),
        ("crates/demo/src/lib.rs", "//! The crate.\n"),
    ];
    let root = tree(&files);
    let output = run("tracked", &root);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "the tree keeps the list: {stderr}");
    assert_eq!(
        "artifacts tracked OK: 3 tracked files, no file of an output or a ratchet but the 0 rows that wait for their unit\n",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        stderr.contains("artifacts: tree: 3 files, 2 rows, 1 crates, "),
        "the cost names the tree: {stderr}"
    );
    let output = run("clean", &root);
    assert!(output.status.success(), "a committed tree is clean");
    std::fs::write(root.join("crates/README.md"), "# crates, changed\n").expect("the change");
    std::fs::write(root.join("stray.log"), "a run wrote it\n").expect("the stray file");
    let output = run("clean", &root);
    assert_eq!(
        Some(1_i32),
        output.status.code(),
        "an unclean checkout exits one"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("crates/README.md: it changed after the gates; the row `the crate table` of .config/replay/artifacts.json holds it\nstray.log: git does not know it and does not ignore it after the gates, and no row of .config/replay/artifacts.json holds it; add the row of its writer\n"),
        "the findings name each file: {stderr}"
    );
    files.push(("ledger/census.md", "# census\n"));
    let root = tree(&files);
    let output = run("tracked", &root);
    assert_eq!(
        Some(1_i32),
        output.status.code(),
        "a tracked output exits one"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("ledger/census.md: the tree tracks it, and the row `the census` of .config/replay/artifacts.json gives it as an output"),
        "the finding names the file and its row: {stderr}"
    );
    std::fs::remove_dir_all(&root).expect("the tree is removed");
}
