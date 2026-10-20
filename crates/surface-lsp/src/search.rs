//! Workspace symbols: the names a document's import closure declares, kept
//! once per text and searched by a query whose characters a name holds in
//! order.
//!
//! A document copy's [`Found`] is read at the first workspace-symbol request
//! after its text changed, off the outline of each source of the closure its
//! hovers' type table laid out: one entry per declaration the outline reads —
//! a module's members, a theory's members and a family's constructors
//! included — with the outline's kind, the name of the declaration holding
//! it, and the range of its name in the text of the source that writes it. A
//! request reads every held document's index; a name is found when the
//! query's characters, compared without case, occur in it in order.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_syntax::SourceText;

use crate::position::Range;
use crate::protocol::SymbolKind;
use crate::reading::Reading;

/// The most symbols one workspace-symbol request answers.
pub const FOUND_HELD: usize = 128;

/// One declared name of a closure: its name, the name folded to lower case,
/// what it declares, the declaration holding it, the source writing it and
/// the range of its name there.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Entry
{
    /// The name folded to lower case, which a query is compared with.
    pub folded: String,
    /// The name as written.
    pub name: String,
    /// What it declares, as the outline names it.
    pub kind: SymbolKind,
    /// The name of the declaration holding it; none at the top of its
    /// source.
    pub container: Option<String>,
    /// The closure's source writing it.
    pub source: SourceIndex,
    /// The range of its name in that source's text.
    pub range: Range,
}

/// The names a document's import closure declares, ascending by folded name,
/// then by name, source and range.
///
/// # Specification
/// - requires: built by [`Found::of`].
/// - ensures: ascending; no entry twice.
/// - panics: none.
/// - executable: none — a carrier; [`Found::of`] and [`Found::matching`] carry
///   the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Found::matching`].
/// - witness: `search::tests::a_query_finds_the_names_holding_its_characters_in_order`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Found(Vec<Entry>);

impl Found
{
    /// The declarations of the closure `table` laid out, each with the range
    /// of its name in its source's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for each source of the table's unit, one entry per symbol
    ///   [`Reading::symbols`] reads off its text, named, kinded and ranged as
    ///   the symbol is, its container the name of the symbol holding it; a
    ///   symbol with the holder, name and kind of one before it in its source —
    ///   a definition after its signature — is left out. Ascending, once.
    /// - provides: the index a workspace-symbol request reads, built once per
    ///   text.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one reading per source and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling's names are found with the sibling's
    ///   ranges, a family's constructors and a theory's members with their
    ///   holder, and a declaration written as a signature and a definition
    ///   once.
    /// - witness: `server::tests::workspace_symbols_find_the_names_the_open_closures_declare`
    #[spec(ensures: |ret| ret.0.windows(2).all(|pair| matches!(pair, [first, second] if first < second)))]
    #[must_use]
    pub fn of(table: &TypeTable) -> Self
    {
        let mut entries = Vec::new();
        let mut at = 0_usize;
        while let Some(text) = table.source_text(SourceIndex::from(at)) {
            let source = SourceIndex::from(at);
            at = at.saturating_add(1_usize);
            let symbols = Reading::of(text).symbols().0;
            let mut written: BTreeSet<(Option<&str>, &str, SymbolKind)> = BTreeSet::new();
            for symbol in &symbols {
                let container = symbol
                    .holder
                    .and_then(|holder| symbols.get(holder))
                    .map(|holder| holder.name.as_str());
                if !written.insert((container, symbol.name.as_str(), symbol.kind)) {
                    continue;
                }
                entries.push(Entry {
                    folded: symbol.name.to_lowercase(),
                    name: symbol.name.clone(),
                    kind: symbol.kind,
                    container: container.map(String::from),
                    source,
                    range: symbol.selection_range,
                });
            }
        }
        entries.sort_unstable();
        entries.dedup();
        Self(entries)
    }

    /// The entries whose folded name holds the folded `query`'s characters in
    /// order, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the entries whose folded name holds every character
    ///   of `query` folded to lower case, in order, not necessarily adjacent;
    ///   every entry for the empty query.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy filter; the witness reads it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `nt` finds `Nat` and `count` and not `tan`; a
    ///   prefix-only or case-sensitive match changes it.
    /// - witness: `search::tests::a_query_finds_the_names_holding_its_characters_in_order`
    pub fn matching<'found>(
        &'found self,
        query: SourceText<'_>,
    ) -> impl Iterator<Item = &'found Entry> + use<'found>
    {
        let folded = <&str>::from(query).to_lowercase();
        self.0.iter().filter(move |entry| {
            let mut rest = entry.folded.chars();
            folded.chars().all(|wanted| rest.any(|held| held == wanted))
        })
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_syntax::SourceText;

    use super::Entry;
    use super::Found;
    use crate::position::Range;
    use crate::protocol::SymbolKind;

    #[test]
    fn a_query_finds_the_names_holding_its_characters_in_order()
    {
        let entry = |name: &str| Entry {
            folded: name.to_lowercase(),
            name: String::from(name),
            kind: SymbolKind::FUNCTION,
            container: None,
            source: SourceIndex::from(0_usize),
            range: Range::default(),
        };
        let mut entries: Vec<Entry> = ["Nat", "count", "tan", "zero"]
            .into_iter()
            .map(entry)
            .collect();
        entries.sort_unstable();
        let found = Found(entries);
        let names = |query: &str| -> Vec<&str> {
            found
                .matching(SourceText::from(query))
                .map(|entry| entry.name.as_str())
                .collect()
        };
        assert_eq!(
            names("nt"),
            ["count", "Nat"],
            "the characters in order, apart, without case"
        );
        assert_eq!(
            names("NA"),
            ["Nat"],
            "an upper-case query finds a lower-case name"
        );
        assert_eq!(names("tn"), ["tan"], "out of order is not found");
        assert_eq!(
            names(""),
            ["count", "Nat", "tan", "zero"],
            "the empty query finds every name"
        );
        assert!(
            names("q").is_empty(),
            "a character no name holds finds nothing"
        );
    }
}
