//! Formatting: the document laid out by `gandr-surface-format`, answered as
//! the edits that turn the client's text into it.
//!
//! # Every edit is trimmed
//!
//! An edit is the formatted text minus the prefix and suffix it shares with
//! the client's, so an editor keeps its cursor and marks on every line the
//! layout did not touch. A whole-document request answers at most one.
//!
//! # A range is the top-level forms it touches
//!
//! The formatter lays a document out a top-level form at a time, each with the
//! comments standing before it, and reports where each sits before and after.
//! A range request answers an edit for each form the range overlaps, or holds
//! the cursor of, whose layout changed, and leaves the blank lines between
//! forms as the client wrote them.
//!
//! # Formatting answers the formatter's layout as edits
//!
//! A formatting request parses the held text under the process's grammar and
//! lays it out through `gandr-surface-format` at its default page of 100
//! columns, which keeps every token and comment, copies strings, shell blocks,
//! holes and repaired forms as written, and refuses a layout whose parse
//! differs from the text's. The answer is the edits that turn the held text
//! into that layout; the server's copy changes only when the client applies
//! them and synchronises back.
//!
//! - **The whole document** answers no edit when the layout is the text's own,
//!   and otherwise one edit.
//! - **A range** answers one edit per top-level form whose span overlaps it, or
//!   holds it when the range is empty, and whose layout changed. A form carries
//!   the comments standing directly before it, as the formatter places them;
//!   the blank lines between forms are never edited. The formatter lays each
//!   top-level form out on its own, so a form's layout does not depend on its
//!   neighbours.
//! - **Every edit is trimmed** to the span between the longest prefix and the
//!   longest suffix the source and the layout share, both on character
//!   boundaries, so a client keeps its cursor, marks and undo granularity on
//!   every line the layout left alone.
//! - **A refusal** — a grammar that did not build, a parse that did not commit,
//!   or a layout the formatter refuses — answers `-32803` request failed with
//!   the reason, so the client says why the document was not formatted rather
//!   than silently leaving it.
//!
//! The client's `options` — tab size, spaces or tabs — are read and set aside:
//! the formatter's layout is the one `gandr fmt` writes, and a second layout
//! per editor setting would make the two disagree. The alternatives were one
//! edit replacing the whole document, which every client applies but which
//! moves a cursor anywhere in it, and a minimal diff per line, which costs a
//! diff for edits a client merges anyway. The choice reverses when a client is
//! measured paying for the trimmed edit's size, or when the formatter gains
//! settings a project chooses, which the server then reads from the workspace
//! configuration rather than from `options`.

use core::fmt;

use anodized::spec;
use gandr_surface_format::FormatError;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::format;
use gandr_surface_grammar::PbgError;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::PosOfByteError;
use gandr_surface_syntax::SourceText;

use crate::position::Position;
use crate::position::Range;
use crate::protocol::TextEdit;
use crate::recheck::grammar;

/// Why a document was not formatted.
#[derive(Debug)]
pub enum Unformatted
{
    /// The built-in grammar did not build.
    Grammar(&'static PbgError),
    /// The parse could not commit a tree.
    Parse(MeldError),
    /// The formatter refused the document.
    Refused(FormatError),
    /// An edit's offset is not a position of the document.
    Position(PosOfByteError),
}

impl fmt::Display for Unformatted
{
    /// Writes why, in one line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Grammar(error) => {
                write!(
                    f,
                    "not formatted: the built-in grammar did not build: {error}"
                )
            },
            Self::Parse(ref error) => {
                write!(f, "not formatted: the parse did not commit: {error}")
            },
            Self::Refused(ref error) => write!(f, "not formatted: {error}"),
            Self::Position(ref error) => write!(f, "not formatted: {error}"),
        }
    }
}

/// What a formatting request lays out: the whole document, the top-level
/// forms some of the ranges touch, or the form a position closes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Scope<'ranges>
{
    /// The whole document.
    Whole,
    /// The forms these ranges touch.
    Within(&'ranges [Range]),
    /// The form whose source ends at this position: the form a character
    /// typed there closed.
    Closing(Position),
}

/// The edits that lay `text` out, over the whole document or the top-level
/// forms `scope` touches.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `text` is parsed and laid out by `gandr-surface-format` at its
///   default page, once whatever the scope. Over [`Scope::Whole`], no edit when
///   the layout is the text's own, and otherwise one edit. Over
///   [`Scope::Within`], one edit per top-level form, with the comments standing
///   before it, whose source span overlaps one of the ranges, or contains it
///   when that range is empty, and whose layout differs; a form several ranges
///   touch is edited once, and the blank lines between forms are never edited.
///   Over [`Scope::Closing`], the edit of the one form whose source ends at the
///   position, if any. Each edit replaces the span of its form, or of the
///   document, between the longest prefix and the longest suffix the source and
///   the layout share, both on character boundaries, with the layout between
///   them. Edits are in document order and never overlap.
/// - fails: a grammar that did not build, a parse that did not commit, a
///   formatter refusal, or an offset the line index cannot place.
/// - panics: none.
///
/// # Errors
/// The [`Unformatted`] reason.
///
/// # Adequacy
/// - hypothesis: L3 — a document with two forms out of layout, formatted whole,
///   over a range covering one form, at a cursor inside the other, and over two
///   ranges touching both forms or one form twice, observes the trimmed whole
///   edit and the per-form edits exactly; a document in layout answers no edit,
///   and a repaired form none; a position after a form's closing `;` edits that
///   form, and one inside a form or after a block's statement edits nothing.
/// - witness: `format::tests::the_whole_document_is_one_trimmed_edit`
/// - witness: `format::tests::a_range_formats_the_forms_it_touches`
/// - witness: `format::tests::several_ranges_format_each_form_they_touch_once`
/// - witness: `format::tests::a_closing_position_formats_the_form_it_ends`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |edits|
    edits.windows(2).all(|pair| match *pair {
        [ref earlier, ref later] => earlier.range.end <= later.range.start,
        _ => false,
    })
    && (matches!(scope, Scope::Within(_)) || edits.len() <= 1)))]
pub fn edits(
    text: SourceText<'_>,
    scope: Scope<'_>,
) -> Result<Vec<TextEdit>, Unformatted>
{
    let grammar = grammar().map_err(Unformatted::Grammar)?;
    let parsed = parse(grammar, text).map_err(Unformatted::Parse)?;
    let formatted =
        format(grammar, &parsed, FormatOptions::default()).map_err(Unformatted::Refused)?;
    let source = <&str>::from(text);
    let laid = <&str>::from(formatted.text());
    let index = LineIndex::new(source.into());
    let mut edits = Vec::new();
    // The edit turning `before`, at `from` in the source, into `after`,
    // trimmed to the span between the longest prefix and the longest suffix
    // the two share, each ending on a character boundary of both.
    let mut replace = |from: usize, before: &str, after: &str| {
        if before == after {
            return Ok(());
        }
        let mut prefix = before
            .bytes()
            .zip(after.bytes())
            .take_while(|&(one, other)| one == other)
            .count();
        while !(before.is_char_boundary(prefix) && after.is_char_boundary(prefix)) {
            prefix = prefix.saturating_sub(1);
        }
        let (rest, laid_rest) = (
            before.get(prefix ..).unwrap_or_default(),
            after.get(prefix ..).unwrap_or_default(),
        );
        let mut suffix = rest
            .bytes()
            .rev()
            .zip(laid_rest.bytes().rev())
            .take_while(|&(one, other)| one == other)
            .count();
        while !(rest.is_char_boundary(rest.len().saturating_sub(suffix))
            && laid_rest.is_char_boundary(laid_rest.len().saturating_sub(suffix)))
        {
            suffix = suffix.saturating_sub(1);
        }
        let start = from.saturating_add(prefix);
        let end = from.saturating_add(before.len().saturating_sub(suffix));
        let range = Range::of_bytes(&index, ByteOffset::from(start), ByteOffset::from(end))
            .map_err(Unformatted::Position)?;
        edits.push(TextEdit {
            range,
            new_text: after
                .get(prefix .. after.len().saturating_sub(suffix))
                .unwrap_or_default()
                .to_owned(),
        });
        Ok(())
    };
    match scope {
        Scope::Whole => replace(0, source, laid)?,
        Scope::Within(_) | Scope::Closing(_) => {
            let at = |position: Position| usize::from(position.byte(&index));
            let bounds: Vec<(usize, usize)> = match scope {
                Scope::Within(ranges) => ranges
                    .iter()
                    .map(|range| (at(range.start), at(range.end)))
                    .collect(),
                Scope::Whole | Scope::Closing(_) => Vec::new(),
            };
            let closing = match scope {
                Scope::Closing(position) => Some(at(position)),
                Scope::Whole | Scope::Within(_) => None,
            };
            for piece in formatted.pieces() {
                let (from, to) = (
                    usize::from(piece.source.start()),
                    usize::from(piece.source.end()),
                );
                let touched = closing == Some(to)
                    || bounds.iter().any(|&(start, end)| {
                        if start < end {
                            from < end && start < to
                        }
                        else {
                            from <= start && start <= to
                        }
                    });
                let (Some(before), Some(after)) = (
                    source.get(from .. to),
                    laid.get(
                        usize::from(piece.formatted.start()) .. usize::from(piece.formatted.end()),
                    ),
                )
                else {
                    continue;
                };
                if touched {
                    replace(from, before, after)?;
                }
            }
        },
    }
    Ok(edits)
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::SourceText;

    use super::Scope;
    use super::edits;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::TextEdit;

    /// The position at `line` and `character`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        line: impl Into<Line>,
        character: impl Into<Character>,
    ) -> Position
    {
        Position {
            line: line.into(),
            character: character.into(),
        }
    }

    /// The edit replacing `start` to `end` with `new_text`.
    ///
    /// # Specification
    /// trivial.
    fn replace(
        start: Position,
        end: Position,
        new_text: impl Into<String>,
    ) -> TextEdit
    {
        TextEdit {
            range: Range { start, end },
            new_text: new_text.into(),
        }
    }

    /// Two forms out of layout, a comment between them in layout.
    const LOOSE: &str = "def  a =  1;\n// kept\ndef b   = 2;\n";

    #[test]
    fn the_whole_document_is_one_trimmed_edit()
    {
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Whole).expect("the document formats"),
            vec![replace(
                at(0_u32, 4_u32),
                at(2_u32, 7_u32),
                "a = 1;\n// kept\ndef b"
            )],
            "one edit, from the first change to the last"
        );
        assert_eq!(
            edits(SourceText::from("def a = 1;\n"), Scope::Whole).expect("the document formats"),
            Vec::new(),
            "a document in layout answers no edit"
        );
    }

    #[test]
    fn a_range_formats_the_forms_it_touches()
    {
        let second = Range {
            start: at(2_u32, 0_u32),
            end: at(2_u32, 2_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[second])).expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "a range inside the second form edits it alone, trimmed"
        );
        let cursor = Range {
            start: at(0_u32, 6_u32),
            end: at(0_u32, 6_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[cursor])).expect("the document formats"),
            vec![replace(at(0_u32, 4_u32), at(0_u32, 9_u32), "a =")],
            "a cursor formats the form holding it"
        );
        let comment = Range {
            start: at(1_u32, 0_u32),
            end: at(1_u32, 7_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[comment]))
                .expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "a comment belongs to the form after it"
        );
        let blank = Range {
            start: at(1_u32, 0_u32),
            end: at(1_u32, 0_u32),
        };
        assert_eq!(
            edits(
                SourceText::from("def  a =  1;\n\ndef b   = 2;\n"),
                Scope::Within(&[blank])
            )
            .expect("the document formats"),
            Vec::new(),
            "a cursor on the blank line between forms edits nothing"
        );
        let repaired = Range {
            start: at(0_u32, 0_u32),
            end: at(1_u32, 0_u32),
        };
        assert_eq!(
            edits(
                SourceText::from("def  a = (1 ;\n"),
                Scope::Within(&[repaired])
            )
            .expect("the document formats"),
            Vec::new(),
            "a repaired form stays as written"
        );
        let across = Range {
            start: at(0_u32, 6_u32),
            end: at(2_u32, 2_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[across])).expect("the document formats"),
            vec![
                replace(at(0_u32, 4_u32), at(0_u32, 9_u32), "a ="),
                replace(at(2_u32, 6_u32), at(2_u32, 8_u32), ""),
            ],
            "a range across two forms formats both"
        );
        let to_the_next = Range {
            start: at(0_u32, 6_u32),
            end: at(1_u32, 0_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[to_the_next]))
                .expect("the document formats"),
            vec![replace(at(0_u32, 4_u32), at(0_u32, 9_u32), "a =")],
            "a range ending where the next form starts leaves that form"
        );
        let from_the_end = Range {
            start: at(0_u32, 12_u32),
            end: at(2_u32, 2_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[from_the_end]))
                .expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "a range starting where a form ends leaves that form"
        );
        let at_the_start = Range {
            start: at(1_u32, 0_u32),
            end: at(1_u32, 0_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[at_the_start]))
                .expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "a cursor where a form starts formats it"
        );
    }

    #[test]
    fn several_ranges_format_each_form_they_touch_once()
    {
        let first = Range {
            start: at(0_u32, 6_u32),
            end: at(0_u32, 6_u32),
        };
        let second = Range {
            start: at(2_u32, 0_u32),
            end: at(2_u32, 2_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[second, first]))
                .expect("the document formats"),
            vec![
                replace(at(0_u32, 4_u32), at(0_u32, 9_u32), "a ="),
                replace(at(2_u32, 6_u32), at(2_u32, 8_u32), ""),
            ],
            "two ranges in either order format both forms, in document order"
        );
        let again = Range {
            start: at(2_u32, 4_u32),
            end: at(2_u32, 9_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[second, again]))
                .expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "two ranges in one form edit it once"
        );
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Within(&[])).expect("the document formats"),
            Vec::new(),
            "no range edits nothing"
        );
    }

    #[test]
    fn a_closing_position_formats_the_form_it_ends()
    {
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Closing(at(0_u32, 12_u32)))
                .expect("the document formats"),
            vec![replace(at(0_u32, 4_u32), at(0_u32, 9_u32), "a =")],
            "after the first form's `;`: that form alone"
        );
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Closing(at(2_u32, 12_u32)))
                .expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "after the second form's `;`: that form alone"
        );
        assert_eq!(
            edits(SourceText::from(LOOSE), Scope::Closing(at(0_u32, 6_u32)))
                .expect("the document formats"),
            Vec::new(),
            "inside a form: nothing"
        );
        assert_eq!(
            edits(
                SourceText::from("def  a = thunk { run x <- pure 1 ; return x } ;\n"),
                Scope::Closing(at(0_u32, 34_u32))
            )
            .expect("the document formats"),
            Vec::new(),
            "after a block's statement: nothing"
        );
    }
}
