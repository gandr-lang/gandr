//! The fixture comment gate: every source opens with a comment, and every
//! top-level item carries one immediately before its attribute block. The
//! committed ledger is the existing debt. A finding the ledger does not hold
//! is new debt; a ledger line the corpus no longer owes is stale.
//!
//! Set `CORPUS_COMMENTS_WRITE_LEDGER=1` to replace the ledger with the
//! current findings. That is how the ledger is rewritten; the check does not
//! write.

mod error;
mod judge;
mod ledger;
mod scan;
mod shape;

use std::path::PathBuf;

use gandr_surface_grammar::Pbg;

use crate::comments::error::CommentError;
use crate::comments::judge::Finding;
use crate::comments::judge::grammar;
use crate::comments::ledger::discrepancies;
use crate::comments::ledger::ledger_text;
use crate::comments::scan::collect;
use crate::comments::scan::replace;

/// The fixture root beside this package.
///
/// # Specification
/// trivial.
fn fixture() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../corpus")
}

/// The committed ledger.
///
/// # Specification
/// trivial.
fn ledger() -> PathBuf
{
    fixture().join("uncommented.ledger")
}

/// Every uncommented item under the fixture root, ledger keys relative to it,
/// the ledger's exemplar subtree excluded: the exemplars are a separate root
/// with their own comment discipline, not in the fixture's uncommented ledger.
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

#[cfg(test)]
mod gate
{
    use super::collect_fixture;
    use super::discrepancies;
    use super::grammar;
    use super::ledger;
    use super::ledger_text;
    use super::replace;

    #[test]
    fn the_fixture_matches_the_ledger()
    {
        let pbg = grammar().expect("the built-in grammar builds");
        let found = collect_fixture(&pbg).expect("the fixture walks");
        let path = ledger();
        if std::env::var_os("CORPUS_COMMENTS_WRITE_LEDGER").is_some() {
            let text = ledger_text(&found);
            let lines = text.lines().count();
            replace(&path, crate::comments::shape::Text(&text)).expect("the ledger writes");
            eprintln!("corpus comments wrote {} ({lines} lines)", path.display());
            return;
        }
        let held = std::fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!("{}: the ledger did not read: {error}", path.display());
        });
        let rows = discrepancies(&found, crate::comments::shape::Text(&held));
        let rendered = rows
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            rows.is_empty(),
            "corpus comments FAILED ({count} disagreements):\n{rendered}",
            count = rows.len()
        );
        eprintln!(
            "corpus comments OK: {} ledger lines",
            held.lines()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .count()
        );
    }
}
