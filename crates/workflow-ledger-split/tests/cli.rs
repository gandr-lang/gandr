use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;

/// A directory of this test's own under the system's temporary directory,
/// emptied, with the directory `a` and the dump `text` as `dump.sql`.
///
/// # Specification
/// trivial.
fn scratch(
    name: &str,
    text: &str,
) -> PathBuf
{
    let directory =
        std::env::temp_dir().join(format!("ledger-split-cli-{}-{name}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(directory.join("a")).expect("the scratch directory");
    std::fs::write(directory.join("dump.sql"), text).expect("the dump");
    directory
}

/// Run the binary on the dump of `directory`, with `--cost`.
///
/// # Specification
/// trivial.
fn run(directory: &Path) -> Output
{
    Command::new(env!("CARGO_BIN_EXE_ledger-split"))
        .arg("--schema")
        .arg(directory.join("schema.sql"))
        .arg("--rows")
        .arg(format!("{}/{{}}/rows.sql", directory.display()))
        .arg("--cost")
        .arg(directory.join("dump.sql"))
        .output()
        .expect("the binary runs")
}

#[test]
fn a_dump_splits_and_prints_each_file()
{
    let directory = scratch(
        "split",
        "BEGIN TRANSACTION;\nCREATE TABLE t(a TEXT);\nINSERT INTO t VALUES('a');\nCOMMIT;\n",
    );
    let output = run(&directory);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "the dump splits: {stderr}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        format!(
            "{}\n{}\n",
            directory.join("schema.sql").display(),
            directory.join("a/rows.sql").display()
        ),
        "the run prints each file, the schema first"
    );
    assert!(
        stderr.contains("ledger-split: split and write: 4 lines, 2 files, "),
        "the cost names each part: {stderr}"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

#[test]
fn a_row_of_no_plain_name_exits_two_and_names_its_line()
{
    let directory = scratch(
        "refused",
        "CREATE TABLE t(a TEXT);\nINSERT INTO t VALUES(NULL);\n",
    );
    let output = run(&directory);
    assert_eq!(output.status.code(), Some(2_i32), "a refused row exits two");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "ledger-split: line 2 of the dump: the first value of the row is no quoted file name\n"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}
