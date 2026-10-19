//! Uses: where the name at a position is declared and where a document uses
//! it.
//!
//! A highlight request finds the name at the position: the use holding it,
//! read off the referent index the document's type table keeps
//! ([`TypeTable::referent`]), or else the declaring name holding it
//! ([`TypeTable::named_at`]). It answers that name's uses from the reverse
//! index built beside the referent index, once per text
//! ([`TypeTable::uses_of`]), and the declaring name when the document writes
//! it. A use and a declaring name are one name when they name the same written
//! name, so a recursive declaration's call, which the lowering binds as a
//! binder, is a use of the declaration. No name is resolved again and the text
//! is never searched for one. A position just past a name answers the name.
//!
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent
//! [`TypeTable::named_at`]: gandr_surface_dispatcher::TypeTable::named_at
//! [`TypeTable::uses_of`]: gandr_surface_dispatcher::TypeTable::uses_of

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::goto::ranged;
use crate::hover::Hovering;
use crate::position::Position;
use crate::protocol::Answer;
use crate::protocol::DocumentHighlight;
use crate::protocol::HighlightKind;

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
#[spec(ensures: |ret| ret.is_none_or(|found| found.source() == table.own_source() || table.uses_of(found).next().is_some()))]
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
                    .uses_of(referent)
                    .filter_map(|span| ranged(&index, span))
                    .map(|range| DocumentHighlight {
                        range,
                        kind: HighlightKind::READ,
                    }),
            )
            .collect(),
    )
}
