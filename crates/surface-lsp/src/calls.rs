//! Calls: the call hierarchy of a declared value, read off the referent index
//! its document's type table keeps.
//!
//! An item is a declaration the table offers as a value ([`NameKind::Value`]),
//! at its definition: the definition's name and its whole form, so a name
//! declared in two halves is one item whichever half the request names. A
//! preparation answers the item for the name at the position, as a highlight
//! finds it. The calls an item makes are the uses lying in its definition's
//! form whose referent is a declared value, grouped by that value. The calls
//! made of it are its uses in each document a reference request reads, each
//! grouped by the declared value whose definition holds it, the innermost
//! when definitions nest; a use no definition holds is no call. Every span
//! and extent is the table's own, so nothing is parsed or resolved again.
//!
//! [`NameKind::Value`]: gandr_surface_dispatcher::NameKind::Value

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use std::path::Path;

use anodized::spec;
use gandr_surface_dispatcher::DeclaredHalf;
use gandr_surface_dispatcher::NameKind;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::goto::ranged;
use crate::hover::Hovering;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::CallHierarchyItem;
use crate::protocol::DocumentUri;
use crate::protocol::IncomingCall;
use crate::protocol::OutgoingCall;
use crate::protocol::SymbolKind;
use crate::uses::named;
use crate::uses::spelling;

/// A document a call request reads: its URI, its canonical path, its text and
/// what its hovers read, its type table among it.
#[derive(Clone, Copy)]
pub struct Read<'read>
{
    /// Its URI.
    pub uri: &'read DocumentUri,
    /// Its canonical path.
    pub path: &'read Path,
    /// Its text.
    pub text: SourceText<'read>,
    /// What its hovers read.
    pub hovering: &'read Hovering,
}

/// The declared value `referent` names, at its definition's site; none when
/// the table declares no value there.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the definition half of the name the table offers as
///   [`NameKind::Value`] where `referent`, or either of its halves, is named,
///   whatever extent `referent` gives it, as a recursive call's binder does;
///   none for any other binder, a family and a constructor.
/// - provides: what a call hierarchy names an item by.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function used and at its own name, and a value declared
///   in two halves at either, are callable; a constructor and a parameter are
///   not.
/// - witness: `server::tests::the_call_hierarchy_follows_a_corpus_closure`
#[spec(ensures: |ret| ret.is_none_or(|site| site.source() == referent.source()))]
#[must_use]
pub fn callable(
    table: &TypeTable,
    referent: Referent,
) -> Option<Referent>
{
    let declared = table.declared_names();
    let value = |site: Referent| {
        declared
            .binary_search_by(|&(offered, _)| {
                (offered.source(), offered.named()).cmp(&(site.source(), site.named()))
            })
            .ok()
            .and_then(|at| declared.get(at))
            .filter(|&&(_, kind)| kind == NameKind::Value)
            .map(|&(offered, _)| table.half(offered, DeclaredHalf::Definition))
    };
    [
        referent,
        table.half(referent, DeclaredHalf::Signature),
        table.half(referent, DeclaredHalf::Definition),
    ]
    .into_iter()
    .find_map(value)
}

/// The item standing for `site`, a declared value of `read`'s closure, in the
/// document it is written in.
///
/// # Specification
/// - requires: `own` indexes `read`'s text.
/// - ensures: the name `site` spells, kind function, at `read`'s URI when
///   `read` writes it and otherwise at the URI `locate` gives the path of its
///   source, with its extent's range and its name's; none when its source names
///   no path, `locate` gives none, or a span has no range in its text.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an item of the document and one of a sibling are each
///   placed in their own text.
/// - witness: `server::tests::the_call_hierarchy_follows_a_corpus_closure`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|placed| placed.kind == SymbolKind::FUNCTION
    && (site.source() != read.hovering.table().own_source() || placed.uri == *read.uri)))]
fn item(
    read: Read<'_>,
    own: &LineIndex<'_>,
    site: Referent,
    locate: &dyn Fn(&Path) -> Option<DocumentUri>,
) -> Option<CallHierarchyItem>
{
    let table = read.hovering.table();
    let placed = |text: SourceText<'_>, index: &LineIndex<'_>, uri: DocumentUri| {
        Some(CallHierarchyItem {
            name: String::from(<&str>::from(spelling(text, site.named())?)),
            kind: SymbolKind::FUNCTION,
            uri,
            range: ranged(index, site.extent())?,
            selection_range: ranged(index, site.named())?,
        })
    };
    if site.source() == table.own_source() {
        placed(read.text, own, read.uri.clone())
    }
    else {
        let text = table.source_text(site.source())?;
        let uri = locate(read.hovering.source_path(site.source())?)?;
        placed(text, &LineIndex::new(<&str>::from(text).into()), uri)
    }
}

/// What a call-hierarchy preparation at `position` of `read` answers: the
/// declared value the name there names.
///
/// # Specification
/// - requires: `read`'s hovering was read off its text.
/// - ensures: one item, as [`callable`] and the item's placing answer for the
///   name [`named`] finds at the position's byte; empty when it finds none or
///   that name is no declared value.
/// - provides: the answer to `textDocument/prepareCallHierarchy`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a call of a sibling's function and a function's own name
///   each prepare it; a constructor prepares nothing.
/// - witness: `server::tests::the_call_hierarchy_follows_a_corpus_closure`
#[spec(ensures: |ret| ret.len() <= 1_usize)]
#[must_use]
pub fn items(
    read: Read<'_>,
    position: Position,
    locate: &dyn Fn(&Path) -> Option<DocumentUri>,
) -> Vec<CallHierarchyItem>
{
    let table = read.hovering.table();
    let index = LineIndex::new(<&str>::from(read.text).into());
    named(table, offset(&index, position))
        .and_then(|referent| callable(table, referent))
        .and_then(|site| item(read, &index, site, locate))
        .into_iter()
        .collect()
}

/// The calls `read` makes of the name written at `named` of the source at
/// `path`, each grouped by the declared value whose definition holds it.
///
/// # Specification
/// - requires: `read`'s hovering was read off its text.
/// - ensures: when `path` is `read`'s own, its own source, else the source its
///   closure reads at `path`, and empty when it reads none; then, for each use
///   of the name there in `read`'s text other than the range `skipped`, the
///   innermost declared value of `read`'s own source whose definition's form
///   holds it, once per value in the order the table orders them, with the
///   ranges of its uses in document order. A use no definition holds is left
///   out.
/// - provides: one document's part of an incoming-calls answer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an importer's calls of a sibling's function are grouped
///   by the definition making them, a recursive call by its own definition.
/// - witness: `server::tests::the_call_hierarchy_follows_a_corpus_closure`
#[spec(ensures: |ret| ret.iter().all(|call| !call.from_ranges.is_empty()))]
#[must_use]
pub fn callers(
    read: Read<'_>,
    path: &Path,
    named: ByteSpan,
    skipped: Option<Range>,
    locate: &dyn Fn(&Path) -> Option<DocumentUri>,
) -> Vec<IncomingCall>
{
    let table = read.hovering.table();
    let own = table.own_source();
    let source = if path == read.path {
        Some(own)
    }
    else {
        read.hovering.source_at(path)
    };
    let Some(source) = source
    else {
        return Vec::new();
    };
    let index = LineIndex::new(<&str>::from(read.text).into());
    let holders: Vec<Referent> = table
        .declared_names()
        .iter()
        .filter(|&&(declared, kind)| kind == NameKind::Value && declared.source() == own)
        .map(|&(declared, _)| table.half(declared, DeclaredHalf::Definition))
        .collect();
    let mut grouped: BTreeMap<Referent, Vec<Range>> = BTreeMap::new();
    table
        .uses_of(source, named)
        .filter_map(|span| {
            let range = ranged(&index, span)?;
            let holder = holders
                .iter()
                .filter(|holder| {
                    holder.extent().start() <= span.start() && span.end() <= holder.extent().end()
                })
                .max_by_key(|holder| holder.extent().start())?;
            (Some(range) != skipped).then_some((*holder, range))
        })
        .for_each(|(holder, range)| grouped.entry(holder).or_default().push(range));
    grouped
        .into_iter()
        .filter_map(|(holder, from_ranges)| {
            Some(IncomingCall {
                from: item(read, &index, holder, locate)?,
                from_ranges,
            })
        })
        .collect()
}

/// What an outgoing-calls request about the item whose name stands at
/// `position` of `read` answers: each declared value its definition uses.
///
/// # Specification
/// - requires: `read`'s hovering was read off its text.
/// - ensures: for the declared value [`callable`] finds for the name at the
///   position's byte, when `read` writes it, each declared value a use lying in
///   its definition's form refers to, the names of its own halves aside, once
///   per value in the order the table orders them, with the range of the
///   narrowest use starting at each offset, as a recursive call's name is
///   narrower than the call it heads, in document order; empty when no such
///   value is found.
/// - provides: the answer to `callHierarchy/outgoingCalls`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a definition calling a sibling's function and itself
///   answers both, each with its uses; a constructor it applies is no call.
/// - witness: `server::tests::the_call_hierarchy_follows_a_corpus_closure`
#[spec(ensures: |ret| ret.iter().all(|call| !call.from_ranges.is_empty()))]
#[must_use]
pub fn callees(
    read: Read<'_>,
    position: Position,
    locate: &dyn Fn(&Path) -> Option<DocumentUri>,
) -> Vec<OutgoingCall>
{
    let table = read.hovering.table();
    let index = LineIndex::new(<&str>::from(read.text).into());
    let Some(caller) = named(table, offset(&index, position))
        .and_then(|referent| callable(table, referent))
        .filter(|caller| caller.source() == table.own_source())
    else {
        return Vec::new();
    };
    let own = [DeclaredHalf::Signature, DeclaredHalf::Definition]
        .map(|half| table.half(caller, half).named());
    let mut grouped: BTreeMap<Referent, Vec<Range>> = BTreeMap::new();
    table
        .uses_within(caller.extent())
        .filter(|&(span, _)| !own.contains(&span))
        .filter_map(|(span, referent)| Some((callable(table, referent)?, ranged(&index, span)?)))
        .for_each(|(callee, range)| {
            let ranges = grouped.entry(callee).or_default();
            match ranges.last_mut() {
                Some(last) if last.start == range.start => *last = (*last).min(range),
                Some(_) | None => ranges.push(range),
            }
        });
    grouped
        .into_iter()
        .filter_map(|(callee, from_ranges)| {
            Some(OutgoingCall {
                to: item(read, &index, callee, locate)?,
                from_ranges,
            })
        })
        .collect()
}

/// The byte `position` stands at in the text `index` indexes.
///
/// # Specification
/// trivial.
fn offset(
    index: &LineIndex<'_>,
    position: Position,
) -> ByteOffset
{
    ByteOffset::from(usize::from(position.byte(index)))
}
