use std::path::Path;
use std::path::PathBuf;

use gandr_workflow_ledger_split::RowPath;
use gandr_workflow_ledger_split::SplitFault;
use gandr_workflow_ledger_split::split;

/// A dump of two tables, with its frame, as `sqlite3` writes it.
const DUMP: &str = "PRAGMA foreign_keys=OFF;\nBEGIN TRANSACTION;\nCREATE TABLE purpose(crate TEXT, path TEXT);\nINSERT INTO purpose VALUES('a','x');\nINSERT INTO purpose VALUES('b','y');\nINSERT INTO purpose VALUES('a','z');\nCREATE TABLE held_by(crate TEXT, system TEXT);\nINSERT INTO held_by VALUES('a','linux');\nINSERT INTO held_by VALUES('it''s','macos');\nCOMMIT;\n";

/// A directory of this test's own under the system's temporary directory,
/// emptied, with the directories `a`, `b` and `it's`.
///
/// # Specification
/// trivial.
fn scratch(name: &str) -> PathBuf
{
    let directory =
        std::env::temp_dir().join(format!("ledger-split-{}-{name}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&directory);
    for crate_name in ["a", "b", "it's"] {
        std::fs::create_dir_all(directory.join(crate_name)).expect("the scratch directory");
    }
    directory
}

/// The row path of the scratch rows under `directory`.
///
/// # Specification
/// trivial.
fn rows(directory: &Path) -> RowPath
{
    RowPath::new(&format!("{}/{{}}/rows.sql", directory.display())).expect("one `{}`")
}

/// The text of the file at `path`.
///
/// # Specification
/// trivial.
fn read(path: &Path) -> String
{
    std::fs::read_to_string(path).expect("a written file")
}

#[test]
fn a_dump_splits_into_its_schema_and_a_file_for_each_name()
{
    let directory = scratch("whole");
    let schema = directory.join("schema.sql");
    let done = split(DUMP, &schema, &rows(&directory)).expect("the dump splits");
    assert_eq!(done.paths, [
        schema.clone(),
        directory.join("a/rows.sql"),
        directory.join("b/rows.sql"),
        directory.join("it's/rows.sql")
    ]);
    assert_eq!(done.lines, 10, "the split reads each line of the dump");
    assert_eq!(
        read(&schema),
        "CREATE TABLE purpose(crate TEXT, path TEXT);\nCREATE TABLE held_by(crate TEXT, system TEXT);\n",
        "the schema has no line of the frame and no row"
    );
    assert_eq!(
        read(&directory.join("a/rows.sql")),
        "INSERT INTO purpose VALUES('a','x');\nINSERT INTO purpose VALUES('a','z');\nINSERT INTO held_by VALUES('a','linux');\n",
        "the rows of one name stand in one file, in the order of the dump"
    );
    assert_eq!(
        read(&directory.join("b/rows.sql")),
        "INSERT INTO purpose VALUES('b','y');\n"
    );
    assert_eq!(
        read(&directory.join("it's/rows.sql")),
        "INSERT INTO held_by VALUES('it''s','macos');\n",
        "a doubled quote is one quote of the name"
    );
    let first = read(&directory.join("a/rows.sql"));
    split(DUMP, &schema, &rows(&directory)).expect("a second split");
    assert_eq!(
        read(&directory.join("a/rows.sql")),
        first,
        "a second split gives the same bytes"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

#[test]
fn a_row_with_no_place_is_refused_by_name()
{
    let directory = scratch("refused");
    let schema = directory.join("schema.sql");
    let missing = split(
        "CREATE TABLE purpose(crate TEXT);\nINSERT INTO purpose VALUES('c');\n",
        &schema,
        &rows(&directory),
    );
    assert!(
        matches!(missing, Err(SplitFault::Unwritable { ref path, .. }) if *path == directory.join("c/rows.sql")),
        "a name with no directory is refused naming its file: {missing:?}"
    );
    let outside = split(
        "CREATE TABLE purpose(crate TEXT);\nINSERT INTO purpose VALUES('../a');\n",
        &schema,
        &rows(&directory),
    );
    assert!(
        matches!(outside, Err(SplitFault::Row { line: 2 })),
        "a name that leaves its directory is refused naming its line: {outside:?}"
    );
    let template = RowPath::new("rows.sql");
    assert!(
        matches!(template, Err(SplitFault::Template { ref path }) if path == "rows.sql"),
        "a path with no place of the name is refused: {template:?}"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}
