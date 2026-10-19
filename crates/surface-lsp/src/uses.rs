//! Uses: where the name at a position is declared and where the open
//! documents use it.
//!
//! A highlight or reference request finds the name at the position: the use
//! holding it, read off the referent index the document's type table keeps
//! ([`TypeTable::referent`]), or else the declaring name holding it
//! ([`TypeTable::named_at`]). It answers that name's uses from the reverse
//! index built beside the referent index, once per text
//! ([`TypeTable::uses_of`]), and the declaring name when the document writes
//! it. A use and a declaring name are one name when they name the same written
//! name, so a recursive declaration's call, which the lowering binds as a
//! binder, is a use of the declaration. No name is resolved again and the text
//! is never searched for one. A position just past a name answers the name.
//!
//! A highlight reads the requesting document alone. A reference request reads
//! every open document's own uses: a name is the same across documents when
//! its source's canonical path and its span agree, so an importer finds a
//! sibling's name at the index its own closure gave that sibling. A source no
//! document has open is not read, so its uses are not answered.
//!
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent
//! [`TypeTable::named_at`]: gandr_surface_dispatcher::TypeTable::named_at
//! [`TypeTable::uses_of`]: gandr_surface_dispatcher::TypeTable::uses_of

use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::goto::ranged;
use crate::hover::Hovering;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::Answer;
use crate::protocol::DocumentHighlight;
use crate::protocol::DocumentUri;
use crate::protocol::HighlightKind;
use crate::protocol::Location;

/// The name a request at `at` of the table's own source means: the referent
/// of the use holding `at`, else the name declared there, else either of
/// those at the byte before.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first of the use's referent at `at`, the declaring name at
///   `at`, the use's referent at the byte before and the declaring name there
///   that the table answers; none when it answers none of them.
/// - provides: what a highlight, a reference search and a rename at a position
///   are about.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use, a declaring name and a caret just past either
///   answer the name; a keyword answers nothing.
/// - witness: `server::tests::a_highlight_marks_a_name_s_declaration_and_its_uses`
#[spec(ensures: |ret| ret.is_none_or(|found| found.source() == table.own_source()
    || table.uses_of(found.source(), found.named()).next().is_some()))]
pub fn named(
    table: &TypeTable,
    at: ByteOffset,
) -> Option<Referent>
{
    let probe = |offset: ByteOffset| match table.referent(offset) {
        Maybe::Present((_, referent)) => Some(referent),
        Maybe::Absent(_) => match table.named_at(offset) {
            Maybe::Present(referent) => Some(referent),
            Maybe::Absent(_) => None,
        },
    };
    probe(at).or_else(|| {
        usize::from(at)
            .checked_sub(1_usize)
            .map(ByteOffset::from)
            .and_then(probe)
    })
}

/// What a highlight request at `position` of `text`, whose copy keeps
/// `hovering`, answers.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: for the name [`named`] finds at the position's byte, its
///   declaring name as a text highlight when the document writes it, then each
///   of its uses in the document as a read highlight, ascending; empty when no
///   name is found. A span with no range in `text` is dropped.
/// - provides: the answer to `textDocument/documentHighlight` for a held
///   document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter at its binder and at a use, a recursive
///   declaration at its name and at its call, and a constructor in terms and in
///   a pattern each mark the same ranges; a keyword marks nothing.
/// - witness: `server::tests::a_highlight_marks_a_name_s_declaration_and_its_uses`
#[spec(ensures: |ret| matches!(ret, Answer::Highlights(_)))]
#[must_use]
pub fn highlights(
    text: SourceText<'_>,
    hovering: &Hovering,
    position: Position,
) -> Answer
{
    let table = hovering.table();
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let Some(referent) = named(table, at)
    else {
        return Answer::Highlights(Vec::new());
    };
    let declared = (referent.source() == table.own_source())
        .then(|| ranged(&index, referent.named()))
        .flatten()
        .map(|range| DocumentHighlight {
            range,
            kind: HighlightKind::TEXT,
        });
    Answer::Highlights(
        declared
            .into_iter()
            .chain(
                table
                    .uses_of(referent.source(), referent.named())
                    .filter_map(|span| ranged(&index, span))
                    .map(|range| DocumentHighlight {
                        range,
                        kind: HighlightKind::READ,
                    }),
            )
            .collect(),
    )
}

/// Where a name is written: its source's canonical path, its span in that
/// source's text, and its range there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Written
{
    /// The canonical path of the source writing it.
    pub path: PathBuf,
    /// Its span in that source's text.
    pub named: ByteSpan,
    /// Its range in that source's text, none when the span has none.
    pub range: Option<Range>,
}

/// Where the name a request at `position` of `text`, the document whose
/// canonical path is `own` and whose copy keeps `hovering`, is about is
/// written.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: for the name [`named`] finds at the position's byte, `own` when
///   the document writes it and its source's path otherwise, with its span and
///   its range in that source's text; none when no name is found or its source
///   names no path.
/// - provides: what a reference request looks for in every open document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a name the document declares and a sibling's name used in
///   it are each placed in their own source.
/// - witness: `server::tests::references_find_a_name_s_uses_in_every_open_document`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|written| written.range.is_none_or(|range| range.start <= range.end)))]
#[must_use]
pub fn placed(
    text: SourceText<'_>,
    own: &Path,
    hovering: &Hovering,
    position: Position,
) -> Option<Written>
{
    let table = hovering.table();
    let index = LineIndex::new(<&str>::from(text).into());
    let referent = named(table, ByteOffset::from(usize::from(position.byte(&index))))?;
    if referent.source() == table.own_source() {
        return Some(Written {
            path: own.to_path_buf(),
            named: referent.named(),
            range: ranged(&index, referent.named()),
        });
    }
    let path = hovering.source_path(referent.source())?.to_path_buf();
    let sibling = table.source_text(referent.source())?;
    let sibling = LineIndex::new(<&str>::from(sibling).into());
    Some(Written {
        path,
        named: referent.named(),
        range: ranged(&sibling, referent.named()),
    })
}

/// The locations of the uses that the document at `uri`, whose canonical path
/// is `own` and whose copy of `text` keeps `hovering`, makes of the name
/// written at `named` of the source at `path`.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: when `path` is `own`, the document's own source, else the source
///   its closure reads at `path`, and none when it reads none; then each use of
///   the name written at `named` there, in the document's own text, ascending,
///   at `uri`. A span with no range in `text` is dropped.
/// - provides: one open document's part of a reference request's answer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the declaring document's own uses and an importer's uses
///   of a sibling's name are each found, and a document that reads no such
///   source answers none.
/// - witness: `server::tests::references_find_a_name_s_uses_in_every_open_document`
#[spec(ensures: |ret| ret.iter().all(|location| location.uri == *uri))]
#[must_use]
pub fn located(
    text: SourceText<'_>,
    uri: &DocumentUri,
    own: &Path,
    hovering: &Hovering,
    path: &Path,
    named: ByteSpan,
) -> Vec<Location>
{
    let table = hovering.table();
    let source = if path == own {
        Some(table.own_source())
    }
    else {
        hovering.source_at(path)
    };
    let Some(source) = source
    else {
        return Vec::new();
    };
    let index = LineIndex::new(<&str>::from(text).into());
    table
        .uses_of(source, named)
        .filter_map(|span| ranged(&index, span))
        .map(|range| Location {
            uri: uri.clone(),
            range,
        })
        .collect()
}
