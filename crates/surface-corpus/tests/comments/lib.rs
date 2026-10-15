//! The fixture comment gate: every source opens with a comment, and every
//! top-level item carries one immediately before its attribute block. The
//! committed ledger is the existing debt. A finding the ledger does not hold
//! is new debt; a ledger line the corpus no longer owes is stale.
//!
//! Set `CORPUS_COMMENTS_WRITE_LEDGER=1` to replace the ledger with the
//! current findings. That is how the ledger is rewritten; the check does not
//! write.

extern crate alloc;

mod error;
mod judge;
mod ledger;
mod scan;
mod shape;

use std::path::PathBuf;

use crate::judge::grammar;
use crate::ledger::discrepancies;
use crate::ledger::ledger_text;
use crate::scan::collect;
use crate::scan::replace;

/// The fixture root beside this package.
///
/// # Specification
/// trivial.
fn fixture() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixture")
}

/// The committed ledger.
///
/// # Specification
/// trivial.
fn ledger() -> PathBuf
{
    fixture().join("uncommented.ledger")
}

#[cfg(test)]
mod gate
{
    use super::collect;
    use super::discrepancies;
    use super::fixture;
    use super::grammar;
    use super::ledger;
    use super::ledger_text;
    use super::replace;

    #[test]
    fn the_fixture_matches_the_ledger()
    {
        let pbg = grammar().expect("the built-in grammar builds");
        let found = collect(&pbg, &fixture()).expect("the fixture walks");
        let path = ledger();
        if std::env::var_os("CORPUS_COMMENTS_WRITE_LEDGER").is_some() {
            let text = ledger_text(&found);
            let lines = text.lines().count();
            replace(&path, crate::shape::Text(&text)).expect("the ledger writes");
            eprintln!("corpus comments wrote {} ({lines} lines)", path.display());
            return;
        }
        let held = std::fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!("{}: the ledger did not read: {error}", path.display());
        });
        let rows = discrepancies(&found, crate::shape::Text(&held));
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
            held.lines().filter(|line| !line.trim().is_empty()).count()
        );
    }
}
