//! Uses: where the name at a position is declared and where the documents of
//! the workspace use it.
//!
//! A highlight, linked-editing, reference or rename request finds the name at
//! the position: the use holding it, read off the referent index the document's
//! type table keeps ([`TypeTable::referent`]), or else the declaring name
//! holding it ([`TypeTable::named_at`]). It answers that name's uses from the
//! reverse index built beside the referent index, once per text
//! ([`TypeTable::uses_of`]), and the declaring name when the document writes
//! it. A use and a declaring name are one name when they name the same written
//! name, so a recursive declaration's call, which the lowering binds as a
//! binder, is a use of the declaration. No name is resolved again and the text
//! is never searched for one. A position just past a name answers the name.
//!
//! A highlight reads the requesting document alone, and so does linked
//! editing, which answers only a binder local to one of its declarations: a
//! name the unit declares may be written by importers, which an edit mirrored
//! in one document would leave behind. A reference or rename request reads
//! every open document's own uses, and those of every source
//! under the workspace's roots that imports the name's source and no editor
//! holds, read from disk: a name is the same across documents when its
//! source's canonical path and its span agree, so an importer finds a
//! sibling's name at the index its own closure gave that sibling.
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
use crate::protocol::LinkedEditingRanges;
use crate::protocol::Location;

/// What is written at `at` of the table's own source, and the name it means:
/// the use holding `at` and its referent, else the declaring name there and
/// itself, else either of those at the byte before.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first of the use at `at`, the declaring name at `at`, the use
///   at the byte before and the declaring name there that the table answers,
///   each with the span written in the table's own text; none when it answers
///   none of them.
/// - provides: what a highlight, a reference search and a rename at a position
///   are about, and where a rename at a position starts.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use, a declaring name and a caret just past either
///   answer the name; a keyword answers nothing.
/// - witness: `server::tests::a_highlight_marks_a_name_s_declaration_and_its_uses`
/// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
#[spec(ensures: |ret| ret.is_none_or(|(span, found)| span.start() <= at
    && usize::from(at) <= usize::from(span.end())
    && (found.source() == table.own_source()
        || table.uses_of(found.source(), found.named()).next().is_some())))]
pub fn found(
    table: &TypeTable,
    at: ByteOffset,
) -> Option<(ByteSpan, Referent)>
{
    let probe = |offset: ByteOffset| match table.referent(offset) {
        Maybe::Present(found) => Some(found),
        Maybe::Absent(_) => match table.named_at(offset) {
            Maybe::Present(referent) => Some((referent.named(), referent)),
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

/// The name a request at `at` of the table's own source means, as [`found`]
/// finds it.
///
/// # Specification
/// trivial.
pub fn named(
    table: &TypeTable,
    at: ByteOffset,
) -> Option<Referent>
{
    found(table, at).map(|(_, referent)| referent)
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

/// What a linked-editing request at `position` of `text`, whose copy keeps
/// `hovering`, answers: the name of a binder local to a declaration of the
/// document and each of its uses, an edit of one applying to all; nothing for
/// a name the unit declares, which other documents may write.
///
/// # Specification
/// - requires: `hovering` holds the type table of `text`.
/// - ensures: [`Answer::Nothing`] when no name is at the position, when the
///   name is one the document's unit declares or is written in another source,
///   or when a use of it is spelled otherwise than its binder; otherwise
///   [`Answer::Mirrored`] holding the binder's range, then each use's,
///   ascending, every range spelling the binder's text.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter at its binder and at a use, and a pattern's
///   binder, answer the binder and its uses; a declaration's name and a
///   constructor answer nothing.
/// - witness: `server::tests::linked_editing_mirrors_a_binder_within_its_declaration`
#[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Mirrored(_)))]
#[must_use]
pub fn mirrored(
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
        return Answer::Nothing;
    };
    let declared = table
        .declared_names()
        .binary_search_by(|&(held, _)| held.cmp(&referent))
        .is_ok();
    if declared || referent.source() != table.own_source() {
        return Answer::Nothing;
    }
    let Some(spelled) = spelling(text, referent.named()).map(<&str>::from)
    else {
        return Answer::Nothing;
    };
    let mut ranges = Vec::new();
    for span in
        core::iter::once(referent.named()).chain(table.uses_of(referent.source(), referent.named()))
    {
        let alike = spelling(text, span).map(<&str>::from) == Some(spelled);
        let Some(range) = alike.then(|| ranged(&index, span)).flatten()
        else {
            return Answer::Nothing;
        };
        ranges.push(range);
    }
    Answer::Mirrored(LinkedEditingRanges { ranges })
}

/// Where a name is written: its source's canonical path, its span in that
/// source's text, its range there and how it is spelled.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Written
{
    /// The canonical path of the source writing it.
    pub path: PathBuf,
    /// Its span in that source's text.
    pub named: ByteSpan,
    /// Its range in that source's text, none when the span has none.
    pub range: Option<Range>,
    /// The text of its span.
    pub spelled: String,
}

/// Where the name a request at `position` of `text`, the document whose
/// canonical path is `own` and whose copy keeps `hovering`, is about is
/// written.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: for the name [`named`] finds at the position's byte, `own` when
///   the document writes it and its source's path otherwise, with its span, its
///   range and its text in that source's text; none when no name is found, its
///   source names no path, or its span lies outside its source's text.
/// - provides: what a reference or rename request looks for in every document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a name the document declares and a sibling's name used in
///   it are each placed in their own source.
/// - witness: `server::tests::references_find_a_name_s_uses_in_every_open_document`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|written| written.range.is_none_or(|range| range.start <= range.end)
    && written.spelled.len() == usize::from(written.named.end()).saturating_sub(usize::from(written.named.start()))))]
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
    let (path, source) = if referent.source() == table.own_source() {
        (own.to_path_buf(), text)
    }
    else {
        (
            hovering.source_path(referent.source())?.to_path_buf(),
            table.source_text(referent.source())?,
        )
    };
    let named = referent.named();
    let spelled = spelling(source, named)?;
    let source = LineIndex::new(<&str>::from(source).into());
    Some(Written {
        path,
        named,
        range: ranged(&source, named),
        spelled: String::from(<&str>::from(spelled)),
    })
}

/// The text of `span` in `text`; none when the span lies outside it or splits
/// a character.
///
/// # Specification
/// trivial.
pub fn spelling(
    text: SourceText<'_>,
    span: ByteSpan,
) -> Option<SourceText<'_>>
{
    <&str>::from(text)
        .get(usize::from(span.start()) .. usize::from(span.end()))
        .map(SourceText::from)
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
