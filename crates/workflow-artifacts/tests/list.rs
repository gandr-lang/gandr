//! The rows of the list, and the findings of a tree against them.

use alloc::borrow::ToOwned as _;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use gandr_workflow_artifacts::Each;
use gandr_workflow_artifacts::Entry;
use gandr_workflow_artifacts::Finding;
use gandr_workflow_artifacts::Kind;
use gandr_workflow_artifacts::Row;
use gandr_workflow_artifacts::entries;
use gandr_workflow_artifacts::holds;
use gandr_workflow_artifacts::read;
use gandr_workflow_artifacts::tracked;
use gandr_workflow_artifacts::unclean;

/// A list with an output, a ratchet of each crate that waits for a unit, a
/// ratchet that waits with no file, and a record.
const LIST: &str = r#"[
  {"name": "the census", "kind": "output", "paths": ["ledger/census.md"], "record": "mise run census"},
  {"each": "crate", "name": "the goldens of {crate}", "kind": "ratchet", "paths": ["crates/{crate}/tests/golden/"], "pending": "goldens-leave"},
  {"name": "the old ledger", "kind": "ratchet", "paths": ["corpus/old.ledger"], "pending": "old-leaves"},
  {"name": "the crate table", "kind": "record", "paths": ["crates/README.md"], "reason": "a person writes it"}
]"#;

/// The strings of `paths`.
///
/// # Specification
/// trivial.
fn owned(paths: &[&str]) -> Vec<String>
{
    paths.iter().map(|&path| path.to_owned()).collect()
}

/// The rows read their names, kinds, paths, `each` and `pending`, and
/// leave the fields of the replay; a kind that the list does not have
/// refuses.
#[test]
fn the_rows_read_their_kinds()
{
    let rows = read(LIST).expect("the list reads");
    assert_eq!(
        vec![
            Row {
                name: "the census".to_owned(),
                kind: Kind::Output,
                paths: owned(&["ledger/census.md"]),
                each: None,
                pending: None,
            },
            Row {
                name: "the goldens of {crate}".to_owned(),
                kind: Kind::Ratchet,
                paths: owned(&["crates/{crate}/tests/golden/"]),
                each: Some(Each::Crate),
                pending: Some("goldens-leave".to_owned()),
            },
            Row {
                name: "the old ledger".to_owned(),
                kind: Kind::Ratchet,
                paths: owned(&["corpus/old.ledger"]),
                each: None,
                pending: Some("old-leaves".to_owned()),
            },
            Row {
                name: "the crate table".to_owned(),
                kind: Kind::Record,
                paths: owned(&["crates/README.md"]),
                each: None,
                pending: None,
            },
        ],
        rows
    );
    assert!(
        read(r#"[{"name": "x", "kind": "habit", "paths": []}]"#).is_err(),
        "a kind that the list does not have refuses"
    );
    assert!(
        !Kind::Record.leaves() && Kind::Output.leaves(),
        "a record stays and an output leaves"
    );
}

/// A directory of the list holds each file below it, and not a file whose
/// name only starts with its name; a file holds itself alone.
#[test]
fn a_directory_holds_the_files_below_it()
{
    assert!(holds(
        "crates/a/tests/golden/",
        "crates/a/tests/golden/x.txt"
    ));
    assert!(!holds("crates/a/tests/golden/", "crates/a/tests/golden.rs"));
    assert!(holds("ledger/census.md", "ledger/census.md"));
    assert!(!holds("ledger/census.md", "ledger/census.md.bak"));
}

/// A tracked output refuses and names its row; a tracked record stays; a
/// `pending` row with tracked files stays, and a `pending` row with none
/// refuses after the files.
#[test]
fn a_tracked_output_is_refused_and_a_record_stays()
{
    let rows = read(LIST).expect("the list reads");
    let crates = owned(&["a", "b"]);
    let files = owned(&[
        "crates/README.md",
        "crates/a/src/lib.rs",
        "crates/a/tests/golden.rs",
        "crates/a/tests/golden/x.txt",
        "ledger/census.md",
        "ledger/census.md.bak",
    ]);
    let found = tracked(&rows, &crates, &files);
    assert_eq!(
        vec![
            Finding::Tracked {
                path: "ledger/census.md".to_owned(),
                row: "the census".to_owned(),
                kind: Kind::Output,
            },
            Finding::Waits {
                row: "the old ledger".to_owned(),
                unit: "old-leaves".to_owned(),
            },
        ],
        found
    );
    assert_eq!(
        "ledger/census.md: the tree tracks it, and the row `the census` of .config/replay/artifacts.json gives it as an output; remove it from the tree, or give its row a kind that stays and a reason",
        found.first().expect("a finding").to_string()
    );
    assert_eq!(
        ".config/replay/artifacts.json: the row `the old ledger` waits for `old-leaves`, and the tree tracks no file of it; remove its `pending`",
        found.get(1).expect("a second finding").to_string()
    );
}

/// A row of each crate with no `pending` refuses a tracked file below the
/// directory of one crate and names that crate; the other crate has none.
#[test]
fn a_row_of_each_crate_names_its_crate()
{
    let rows = read(
        r#"[{"each": "crate", "name": "the goldens of {crate}", "kind": "output", "paths": ["crates/{crate}/tests/golden/"]}]"#,
    )
    .expect("the list reads");
    let found = tracked(
        &rows,
        &owned(&["a", "b"]),
        &owned(&["crates/a/src/lib.rs", "crates/b/tests/golden/y.txt"]),
    );
    assert_eq!(
        vec![Finding::Tracked {
            path: "crates/b/tests/golden/y.txt".to_owned(),
            row: "the goldens of b".to_owned(),
            kind: Kind::Output,
        }],
        found
    );
}

/// The status reads a changed file, an unknown file and a rename as their
/// paths in the work tree, and skips the source of the rename.
#[test]
fn the_status_reads_each_entry()
{
    let status = b" M ledger/census.md\0?? target2/x\0R  new.rs\0old.rs\0";
    assert_eq!(
        vec![
            Entry {
                path: "ledger/census.md".to_owned(),
                unknown: false,
            },
            Entry {
                path: "target2/x".to_owned(),
                unknown: true,
            },
            Entry {
                path: "new.rs".to_owned(),
                unknown: false,
            },
        ],
        entries(status)
    );
    assert_eq!(Vec::<Entry>::new(), entries(b""));
}

/// A file that a writer of the list changed names its row, and an unknown
/// file of a writer that the list does not have names none.
#[test]
fn an_unclean_checkout_names_the_rows_of_its_files()
{
    let rows = read(LIST).expect("the list reads");
    let found = unclean(
        &rows,
        &owned(&["a"]),
        &entries(b" M crates/a/tests/golden/x.txt\0?? stray.log\0"),
    );
    assert_eq!(
        vec![
            Finding::Unclean {
                path: "crates/a/tests/golden/x.txt".to_owned(),
                unknown: false,
                row: Some("the goldens of a".to_owned()),
            },
            Finding::Unclean {
                path: "stray.log".to_owned(),
                unknown: true,
                row: None,
            },
        ],
        found
    );
    assert_eq!(
        "crates/a/tests/golden/x.txt: it changed after the gates; the row `the goldens of a` of .config/replay/artifacts.json holds it",
        found.first().expect("a finding").to_string()
    );
    assert_eq!(
        "stray.log: git does not know it and does not ignore it after the gates, and no row of .config/replay/artifacts.json holds it; add the row of its writer",
        found.get(1).expect("a second finding").to_string()
    );
}
