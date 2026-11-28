//! The `references window` binary over a small tree.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// A tree of this test's own under the system's temporary directory, with
/// `files` written in it.
///
/// # Specification
/// trivial.
fn tree(files: &[(&str, &str)]) -> PathBuf
{
    let root = std::env::temp_dir().join(format!("references-cli-{}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&root);
    for &(path, text) in files {
        let path = root.join(path);
        std::fs::create_dir_all(path.parent().expect("a file has a directory"))
            .expect("the directory");
        std::fs::write(path, text).expect("the file");
    }
    root
}

/// Runs `references window` over `root`, with `--cost`.
///
/// # Specification
/// trivial.
fn run(root: &Path) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_references"))
        .arg("window")
        .arg("--root")
        .arg(root)
        .arg("--cost")
        .output()
        .expect("the binary runs")
}

/// The window reads the README and the library modules of a crate, a
/// corpus source and the binary target of a binary crate, and leaves out the
/// binary targets beside a library. Its kept citations exit zero; a new
/// older citation in a module exits one and names its site.
#[test]
fn the_window_reads_the_sources_of_a_tree()
{
    let policy = "cutoff = 2019\n\n[[site]]\nsite = \"demo\"\nwork = \"doi:10.1000/old\"\nexemplar = \"frozen\"\n\n[[site]]\nsite = \"corpus/model/a.gandr\"\nwork = \"arXiv:1501.00001\"\nexemplar = \"frozen\"\n\n[[site]]\nsite = \"tool\"\nwork = \"arXiv:1601.00001\"\nexemplar = \"frozen\"\n";
    let mut files = vec![
        (".config/references/window.toml", policy),
        (
            "ledger/references.sql",
            "INSERT INTO work VALUES('doi:10.1000/old',1999,NULL);\n",
        ),
        (
            "crates/demo/README.md",
            "# demo\n\nSee `doi:10.1000/old`.\n",
        ),
        ("crates/demo/src/lib.rs", "//! The crate.\n"),
        ("crates/demo/src/main.rs", "//! arXiv:1401.00001\n"),
        ("crates/demo/src/bin/extra.rs", "//! arXiv:1401.00002\n"),
        ("crates/tool/src/main.rs", "//! arXiv:1601.00001\n"),
        ("corpus/model/a.gandr", "// arXiv:1501.00001\n"),
    ];
    let root = tree(&files);
    let output = run(&root);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "the kept citations pass: {stderr}");
    assert_eq!(
        "references window OK: 4 sources, the window opens in 2019, 3 entries keep an older work\n",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        stderr.contains("references: sources: 4 files, "),
        "the cost names the sources: {stderr}"
    );
    files.push((
        "crates/demo/src/new.rs",
        "//! A new module, doi:10.1000/old.\n",
    ));
    let root = tree(&files);
    let output = run(&root);
    assert_eq!(
        Some(1_i32),
        output.status.code(),
        "a new older citation exits one"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.starts_with("crates/demo/src/new.rs:1: `doi:10.1000/old` appeared in 1999, before the citation window opens in 2019; cite the newest work that states what demo::new builds"),
        "the finding names the site: {stderr}"
    );
    std::fs::remove_dir_all(&root).expect("the tree is removed");
}
