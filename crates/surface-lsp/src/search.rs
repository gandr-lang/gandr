//! Workspace symbols: the names a text declares, kept once per text and
//! searched by a query whose characters a name holds in order.
//!
//! [`declared`] reads a text's names off its outline, one parse and no
//! lowering: one per declaration the outline reads — a module's members, a
//! theory's members and a family's constructors included — with the outline's
//! kind, the name of the declaration holding it, and the range of its name. A
//! document copy's [`Found`] holds the names of each source of the closure its
//! hovers' type table laid out, read at the first workspace-symbol request
//! after its text changed; the file table holds the names of each source
//! under the opened folders (`crate::files`). A name is found when the
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

/// One name a text declares: its name, the name folded to lower case, what it
/// declares, the declaration holding it and the range of its name in the
/// text.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Declared
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
    /// The range of its name in the text.
    pub range: Range,
}

/// A workspace-symbol query, folded to lower case once.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Query(String);

/// Whether a name holds a query's characters in order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Matched(bool);

impl Query
{
    /// The query `text` asks, folded to lower case.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn of(text: SourceText<'_>) -> Self
    {
        Self(<&str>::from(text).to_lowercase())
    }

    /// Whether `declared`'s name holds the query's characters in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: whether every character of the folded query occurs in the
    ///   folded name, in order, not necessarily adjacent; true for the empty
    ///   query.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause is the comparison itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `nt` finds `Nat` and `count` and not `tan`; a
    ///   prefix-only or case-sensitive match changes it.
    /// - witness: `search::tests::a_query_finds_the_names_holding_its_characters_in_order`
    fn matched(
        &self,
        declared: &Declared,
    ) -> Matched
    {
        let mut rest = declared.folded.chars();
        Matched(self.0.chars().all(|wanted| rest.any(|held| held == wanted)))
    }

    /// The names of `names` the query matches, in their order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the names whose folded name holds every character of
    ///   the folded query in order; every name for the empty query.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy filter; the witness reads it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Found::matching`], which matches through the
    ///   same comparison.
    /// - witness: `server::tests::workspace_symbols_find_the_names_no_open_closure_reaches`
    pub fn matching<'names>(
        &'names self,
        names: &'names [Declared],
    ) -> impl Iterator<Item = &'names Declared> + use<'names>
    {
        names
            .iter()
            .filter(move |declared| self.matched(declared).0)
    }
}

/// The names `text` declares, in the order its outline reads them: one per
/// symbol [`Reading::symbols`] reads off it, named, kinded and ranged as the
/// symbol is, its container the name of the symbol holding it; a symbol with
/// the holder, name and kind of one before it — a definition after its
/// signature — left out.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as stated; nothing for a text that does not parse.
/// - provides: what an index of a text's names keeps, read from one parse and
///   no lowering.
/// - fails: never.
/// - panics: none.
/// - intension: one parse and one pass over its outline.
/// - executable: none — the clause would parse the text again.
///
/// # Adequacy
/// - hypothesis: L3 — a family's constructors and a theory's members with their
///   holder, and a declaration written as a signature and a definition once.
/// - witness: `server::tests::workspace_symbols_find_the_names_the_open_closures_declare`
#[must_use]
pub fn declared(text: SourceText<'_>) -> Vec<Declared>
{
    let symbols = Reading::of(text).symbols().0;
    let mut written: BTreeSet<(Option<&str>, &str, SymbolKind)> = BTreeSet::new();
    let mut names = Vec::with_capacity(symbols.len());
    for symbol in &symbols {
        let container = symbol
            .holder
            .and_then(|holder| symbols.get(holder))
            .map(|holder| holder.name.as_str());
        if !written.insert((container, symbol.name.as_str(), symbol.kind)) {
            continue;
        }
        names.push(Declared {
            folded: symbol.name.to_lowercase(),
            name: symbol.name.clone(),
            kind: symbol.kind,
            container: container.map(String::from),
            range: symbol.selection_range,
        });
    }
    names
}

/// One declared name of a closure and the closure's source writing it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Entry
{
    /// The name, as its source declares it.
    pub declared: Declared,
    /// The closure's source writing it.
    pub source: SourceIndex,
}

/// The names a document's import closure declares, ascending by folded name,
/// then by name, kind, container, range and source.
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
    /// - ensures: for each source of the table's unit, the names [`declared`]
    ///   reads off its text, each with that source. Ascending, once.
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
            entries.extend(
                declared(text)
                    .into_iter()
                    .map(|declared| Entry { declared, source }),
            );
        }
        entries.sort_unstable();
        entries.dedup();
        Self(entries)
    }

    /// The entries whose name `query` matches, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the entries whose name `query` matches, as
    ///   [`Query::matching`] matches; every entry for the empty query.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the answer is a lazy filter; the witness reads it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `nt` finds `Nat` and `count` and not `tan`; a
    ///   prefix-only or case-sensitive match changes it.
    /// - witness: `search::tests::a_query_finds_the_names_holding_its_characters_in_order`
    pub fn matching<'found, 'query>(
        &'found self,
        query: &'query Query,
    ) -> impl Iterator<Item = &'found Entry> + use<'found, 'query>
    {
        self.0
            .iter()
            .filter(move |entry| query.matched(&entry.declared).0)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_syntax::SourceText;

    use super::Declared;
    use super::Entry;
    use super::Found;
    use super::Query;
    use crate::position::Range;
    use crate::protocol::SymbolKind;

    #[test]
    fn a_query_finds_the_names_holding_its_characters_in_order()
    {
        let entry = |name: &str| Entry {
            declared: Declared {
                folded: name.to_lowercase(),
                name: String::from(name),
                kind: SymbolKind::FUNCTION,
                container: None,
                range: Range::default(),
            },
            source: SourceIndex::from(0_usize),
        };
        let mut entries: Vec<Entry> = ["Nat", "count", "tan", "zero"]
            .into_iter()
            .map(entry)
            .collect();
        entries.sort_unstable();
        let found = Found(entries);
        let names = |query: &str| -> Vec<&str> {
            let query = Query::of(SourceText::from(query));
            found
                .matching(&query)
                .map(|entry| entry.declared.name.as_str())
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
