//! The rendered refusals of the corpus's refusing sources, each pinned as
//! the text a face prints. The writer of the outputs crate gives each text,
//! so the goldens and the store of outputs hold one text for a source.
//!
//! The cases, in a `cfg(test)` module so the crate's lint wall reads them as
//! test code rather than as shipping code.

use alloc::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;

use expect_test::expect_file;
use gandr_workflow_outputs::refusals::REFUSING;
use gandr_workflow_outputs::refusals::rendered;

/// The checkout's root, as the walk reaches it.
///
/// # Specification
/// trivial.
fn repository() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the checkout's root resolves")
}

/// Every `.txt` file under `dir`, in path order.
///
/// # Specification
/// trivial.
fn goldens_under(dir: &Path) -> Vec<PathBuf>
{
    let mut files = Vec::new();
    let mut pending = vec![dir.to_owned()];
    while let Some(next) = pending.pop() {
        let Ok(entries) = std::fs::read_dir(&next)
        else {
            continue;
        };
        for entry in entries {
            let path = entry.expect("a directory entry reads").path();
            if path.is_dir() {
                pending.push(path);
            }
            else if path.extension().is_some_and(|held| held == "txt") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Every refusing source's rendered refusals match its golden under
/// `tests/golden/corpus/`, at its path in the corpus, so the text a reader
/// is shown for each refusal name is a reviewed public surface. A golden
/// whose source is gone, or prints nothing, fails the suite;
/// `UPDATE_EXPECT=1` rewrites the goldens and deletes those.
#[test]
fn every_refusing_source_renders_as_its_golden()
{
    let repository = repository();
    let goldens = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden/corpus");
    let update = std::env::var_os("UPDATE_EXPECT").is_some();
    let mut expected: BTreeSet<PathBuf> = BTreeSet::new();
    let roots = REFUSING
        .iter()
        .map(|directory| repository.join("corpus").join(directory))
        .collect();
    let refusals = rendered(&repository, roots).expect("every refusing source reads");
    for (relative, text) in refusals {
        let golden = goldens.join(relative).with_extension("txt");
        if update && let Some(parent) = golden.parent() {
            std::fs::create_dir_all(parent).expect("the golden's directory is created");
        }
        expect_file![golden.clone()].assert_eq(&text);
        let _new = expected.insert(golden);
    }
    assert!(
        !expected.is_empty(),
        "the refusing sources print their refusals"
    );
    let orphans: Vec<PathBuf> = goldens_under(&goldens)
        .into_iter()
        .filter(|golden| !expected.contains(golden))
        .collect();
    if update {
        for orphan in &orphans {
            std::fs::remove_file(orphan).expect("an orphaned golden is removed");
        }
        return;
    }
    assert!(
        orphans.is_empty(),
        "goldens with no refusing source, to delete or rewrite with `UPDATE_EXPECT=1`: \
         {orphans:?}"
    );
}

/// The cyclic circuit's refusal names its port. The walk reads that source
/// alone, as a refusal of one source reads nothing beside it.
#[test]
fn cyclic_circuit_wiring_names_its_port_5805()
{
    let source = "pathological/circuit/circuit-cyclic-wiring.gandr";
    let repository = repository();
    let refusals = rendered(&repository, vec![repository.join("corpus").join(source)])
        .expect("the cyclic circuit fixture reads");
    let rendered = refusals
        .get(Path::new(source))
        .expect("the cyclic circuit fixture is refused");
    assert!(
        rendered.contains("port `z`"),
        "the cyclic circuit refusal names its port: {rendered}"
    );
}
