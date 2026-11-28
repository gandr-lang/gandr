//! The fixture comment gate. Every source opens with a comment. Every item
//! and every member of a block carries one immediately before it. An item
//! carries the comment before its attribute block. `check:prose` reads the
//! shape of a doc comment. The gate gives the uncommented items of each
//! source as values of the kind `uncommented` of the outputs. The difference
//! of that kind refuses a head that adds an uncommented item.

mod error;
mod judge;
mod scan;
mod shape;

use alloc::collections::BTreeMap;
use std::path::PathBuf;

use gandr_surface_grammar::Pbg;
use gandr_workflow_output_store::Kind;
use gandr_workflow_output_store::given;

use crate::comments::error::CommentError;
use crate::comments::judge::Finding;
use crate::comments::judge::grammar;
use crate::comments::scan::collect;

/// The fixture root beside this package.
///
/// # Specification
/// trivial.
fn fixture() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../corpus")
}

/// Every uncommented item under the fixture root, keys relative to it, the
/// exemplar subtree `ledger/` excluded: the exemplars are a separate root
/// with their own comment discipline.
///
/// # Specification
/// trivial.
fn collect_fixture(pbg: &Pbg) -> Result<Vec<Finding>, CommentError>
{
    let found = collect(pbg, &fixture())?;
    Ok(found
        .into_iter()
        .filter(|finding| !finding.line().0.starts_with("ledger/"))
        .collect())
}

/// Gives the findings `found` to the store of outputs as values of the kind
/// `uncommented`, when the environment names a run: one value for each
/// source, named by its path below the fixture root, with one line for each
/// finding. A line is the finding with no path, so an item that moves to
/// another source keeps its line.
///
/// # Specification
/// trivial.
fn given_findings(found: &[Finding])
{
    let mut values: BTreeMap<&str, String> = BTreeMap::new();
    for finding in found {
        let line = finding.line().0;
        let (path, member) = line.split_once(':').unwrap_or((line, ""));
        let value = values.entry(path).or_default();
        value.push_str(member);
        value.push('\n');
    }
    for (path, value) in values {
        let _given = given::give(Kind("uncommented"), path, value.as_bytes())
            .unwrap_or_else(|error| panic!("the findings of `{path}` go to the store: {error}"));
    }
}

#[cfg(test)]
mod gate
{
    use super::collect_fixture;
    use super::given_findings;
    use super::grammar;

    #[test]
    fn the_fixture_gives_its_uncommented_items()
    {
        let pbg = grammar().expect("the built-in grammar builds");
        let found = collect_fixture(&pbg).expect("the fixture walks");
        given_findings(&found);
        eprintln!("corpus comments: {} uncommented items", found.len());
    }
}
