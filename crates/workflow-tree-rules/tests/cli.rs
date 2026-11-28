//! The exit codes and the findings of `tree-rules`, observed by spawning it in
//! a scratch repository that holds the files of the rules of the tree.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// The files of the rules, from the root of the tree.
const RULES: [&str; 5] = [
    ".config/merge-residue/patterns",
    ".config/merge-residue/names",
    ".config/local-paths/patterns",
    ".config/local-paths/placeholders",
    ".config/markdown/readmes",
];

/// Writes a scratch repository with the files of the rules and `files`, adds
/// each file to the index, and gives its root.
///
/// # Specification
/// trivial.
fn tree(
    name: &str,
    files: &[(&str, &[u8])],
) -> PathBuf
{
    let root = std::env::temp_dir().join(format!("tree-rules-{}-{name}", std::process::id()));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let rules: Vec<(&str, Vec<u8>)> = RULES
        .iter()
        .map(|&path| (path, std::fs::read(source.join(path)).unwrap()))
        .collect();
    for (path, bytes) in rules
        .iter()
        .map(|&(path, ref bytes)| (path, bytes.as_slice()))
        .chain(files.iter().copied())
    {
        let file = root.join(path);
        std::fs::create_dir_all(file.parent().unwrap()).unwrap();
        std::fs::write(file, bytes).unwrap();
    }
    let status = Command::new("git")
        .current_dir(&root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .args(["init", "--quiet"])
        .status()
        .unwrap();
    assert!(status.success());
    let status = Command::new("git")
        .current_dir(&root)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .args(["add", "--all"])
        .status()
        .unwrap();
    assert!(status.success());
    root
}

/// Runs `tree-rules` in `root` with `arguments`.
///
/// # Specification
/// trivial.
fn run(
    root: &Path,
    arguments: &[&str],
) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_tree-rules"))
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .arg("--root")
        .arg(root)
        .args(arguments)
        .output()
        .unwrap()
}

#[test]
fn a_clean_tree_passes()
{
    let root = tree("clean", &[
        ("README.md", b"# A project\n".as_slice()),
        ("src/lib.rs", b"//! A crate.\nconst X: u8 = 1;\n".as_slice()),
    ]);
    let output = run(&root, &[]);
    assert_eq!(output.status.code(), Some(0_i32), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "tree rules OK: 7 tracked files keep the rules residue, paths, markdown\n"
    );
}

#[test]
fn the_gate_names_each_finding_and_exits_one()
{
    // The tree of this crate holds no home path, so the test joins each one.
    let home = concat!("/", "home/bob/work");
    let notes = format!("cd {home}\nsee /{}/.config\n", "home/user");
    let binary = format!("\0cd {home}\n");
    let cases = format!("[{{\"line\": \"cd {home}\"}}]\n");
    let root = tree("found", &[
        ("README.md", b"# A project\n".as_slice()),
        ("src/a.rs", b"fn a() {}\n<<<<<<< HEAD\n".as_slice()),
        ("notes.txt", notes.as_bytes()),
        ("docs/guide.md", b"# A guide\n".as_slice()),
        ("src/b.rs.orig", b"fn b() {}\n".as_slice()),
        ("data.bin", binary.as_bytes()),
        (".config/local-paths/cases.json", cases.as_bytes()),
    ]);
    let output = run(&root, &[]);
    assert_eq!(output.status.code(), Some(1_i32), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!(
            "docs/guide.md: markdown: a Markdown file outside the list of READMEs; move its \
             prose into rustdoc\nnotes.txt:1: paths: cd {home}\nsrc/a.rs:2: residue: <<<<<<< \
             HEAD\nsrc/b.rs.orig: residue: a file named as merge residue\ntree rules FAILED: 4 \
             findings of the rules residue, paths, markdown\n"
        )
    );
    let output = run(&root, &["--rule", "markdown"]);
    assert_eq!(output.status.code(), Some(1_i32), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .ends_with("tree rules FAILED: 1 findings of the rules markdown\n"),
        "{output:?}"
    );
}

#[test]
fn a_pattern_that_does_not_compile_is_a_fault()
{
    let root = tree("fault", &[("README.md", b"# A project\n".as_slice())]);
    std::fs::write(root.join(".config/merge-residue/patterns"), "(\n").unwrap();
    let output = run(&root, &[]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2_i32), "{output:?}");
    assert!(
        stderr.starts_with("tree-rules: `.config/merge-residue/patterns`: `(`: "),
        "{stderr}"
    );
}
