//! Workspace symbols: the names a document's import closure declares, kept
//! once per text and searched by a query whose characters a name holds in
//! order.
//!
//! A document copy's [`Found`] is read off the type table its hovers keep, at
//! the first workspace-symbol request after its text changed: one entry per
//! declared name, a family's constructors included, with the range of its name
//! in the text of the source that writes it. A request reads every held
//! document's index; a name is found when the query's characters, compared
//! without case, occur in it in order.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::NameKind;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::SourceText;

use crate::position::Range;
use crate::protocol::SymbolKind;

/// The most symbols one workspace-symbol request answers.
pub const FOUND_HELD: usize = 128;

/// One declared name of a closure: its name, the name folded to lower case,
/// what it declares, the source writing it and the range of its name there.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Entry
{
    /// The name folded to lower case, which a query is compared with.
    pub folded: String,
    /// The name as written.
    pub name: String,
    /// What it declares.
    pub kind: NameKind,
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
    /// The names `table`'s unit declares, each with the range of its name in
    /// its source's text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per [`TypeTable::declared_names`] entry whose
    ///   source's text holds its name, ascending, once; a name its source's
    ///   text does not hold, or whose range does not count, is dropped.
    /// - provides: the index a workspace-symbol request reads, built once per
    ///   text.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the declared names, one line index per
    ///   source, and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling's names are found with the sibling's ranges
    ///   and a family's constructors with their family.
    /// - witness: `server::tests::workspace_symbols_find_the_names_the_open_closures_declare`
    #[spec(ensures: |ret| ret.0.windows(2).all(|pair| matches!(pair, [first, second] if first < second)))]
    #[must_use]
    pub fn of(table: &TypeTable) -> Self
    {
        let mut indexes: Vec<Option<LineIndex<'_>>> = Vec::new();
        let mut entries = Vec::with_capacity(table.declared_names().len());
        for &(referent, kind) in table.declared_names() {
            let source = referent.source();
            let Some(text) = table.source_text(source).map(<&str>::from)
            else {
                continue;
            };
            let at = usize::from(source);
            if indexes.len() <= at {
                indexes.resize_with(at.saturating_add(1_usize), || None);
            }
            let Some(index) = indexes
                .get_mut(at)
                .map(|slot| slot.get_or_insert_with(|| LineIndex::new(text.into())))
            else {
                continue;
            };
            let named = referent.named();
            let (Some(name), Ok(range)) = (
                text.get(usize::from(named.start()) .. usize::from(named.end())),
                Range::of_bytes(
                    index,
                    RenderOffset::from(usize::from(named.start())),
                    RenderOffset::from(usize::from(named.end())),
                ),
            )
            else {
                continue;
            };
            entries.push(Entry {
                folded: name.to_lowercase(),
                name: String::from(name),
                kind,
                source,
                range,
            });
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

/// The protocol's kind for a declared name of `kind`: a family is an enum, as
/// the outline names a data declaration; a constructor is a constructor; any
/// other declaration is a function.
///
/// # Specification
/// trivial.
#[must_use]
pub const fn kind_of(kind: NameKind) -> SymbolKind
{
    match kind {
        NameKind::Family => SymbolKind::ENUM,
        NameKind::Constructor => SymbolKind::CONSTRUCTOR,
        NameKind::Value => SymbolKind::FUNCTION,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_dispatcher::NameKind;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_syntax::SourceText;

    use super::Entry;
    use super::Found;
    use crate::position::Range;

    #[test]
    fn a_query_finds_the_names_holding_its_characters_in_order()
    {
        let entry = |name: &str| Entry {
            folded: name.to_lowercase(),
            name: String::from(name),
            kind: NameKind::Value,
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
