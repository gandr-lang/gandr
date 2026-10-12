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

use crate::position::Range;
use crate::protocol::TextEdit;
use crate::recheck::grammar;
use crate::server::Window;

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
            | Self::Grammar(error) => {
                write!(
                    f,
                    "not formatted: the built-in grammar did not build: {error}"
                )
            },
            | Self::Parse(ref error) => {
                write!(f, "not formatted: the parse did not commit: {error}")
            },
            | Self::Refused(ref error) => write!(f, "not formatted: {error}"),
            | Self::Position(ref error) => write!(f, "not formatted: {error}"),
        }
    }
}

/// The edits that lay `text` out, over the whole document or the top-level
/// forms `window` touches.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `text` is parsed and laid out by `gandr-surface-format` at its
///   default page. Over [`Window::Whole`], no edit when the layout is the
///   text's own, and otherwise one edit. Over [`Window::Within`], one edit per
///   top-level form, with the comments standing before it, whose source span
///   overlaps the range, or contains it when the range is empty, and whose
///   layout differs; the blank lines between forms are never edited. Each edit
///   replaces the span of its form, or of the document, between the longest
///   prefix and the longest suffix the source and the layout share, both on
///   character boundaries, with the layout between them. Edits are in document
///   order and never overlap.
/// - fails: a grammar that did not build, a parse that did not commit, a
///   formatter refusal, or an offset the line index cannot place.
/// - panics: none.
///
/// # Errors
/// The [`Unformatted`] reason.
///
/// # Adequacy
/// - hypothesis: L3 — a document with two forms out of layout, formatted whole,
///   over a range covering one form, and at a cursor inside the other, observes
///   the trimmed whole edit and the per-form edits exactly; a document in
///   layout answers no edit, and a repaired form none.
/// - witness: `format::tests::the_whole_document_is_one_trimmed_edit`
/// - witness: `format::tests::a_range_formats_the_forms_it_touches`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |edits|
    edits.windows(2).all(|pair| match *pair {
        [ref earlier, ref later] => earlier.range.end <= later.range.start,
        _ => false,
    })
    && (!matches!(window, Window::Whole) || edits.len() <= 1)))]
pub fn edits(
    text: SourceText<'_>,
    window: Window,
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
    match window {
        | Window::Whole => replace(0, source, laid)?,
        | Window::Within(range) => {
            let (start, end) = (
                usize::from(range.start.byte(&index)),
                usize::from(range.end.byte(&index)),
            );
            for piece in formatted.pieces() {
                let (from, to) = (
                    usize::from(piece.source.start()),
                    usize::from(piece.source.end()),
                );
                let touched = if start < end {
                    from < end && start < to
                }
                else {
                    from <= start && start <= to
                };
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

    use super::edits;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::TextEdit;
    use crate::server::Window;

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
    const LOOSE: &str = "def  a =  1 ;\n// kept\ndef b   = 2 ;\n";

    #[test]
    fn the_whole_document_is_one_trimmed_edit()
    {
        assert_eq!(
            edits(SourceText::from(LOOSE), Window::Whole).expect("the document formats"),
            vec![replace(
                at(0_u32, 4_u32),
                at(2_u32, 7_u32),
                "a = 1 ;\n// kept\ndef b"
            )],
            "one edit, from the first change to the last"
        );
        assert_eq!(
            edits(SourceText::from("def a = 1 ;\n"), Window::Whole).expect("the document formats"),
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
            edits(SourceText::from(LOOSE), Window::Within(second)).expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "a range inside the second form edits it alone, trimmed"
        );
        let cursor = Range {
            start: at(0_u32, 6_u32),
            end: at(0_u32, 6_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Window::Within(cursor)).expect("the document formats"),
            vec![replace(at(0_u32, 4_u32), at(0_u32, 9_u32), "a =")],
            "a cursor formats the form holding it"
        );
        let comment = Range {
            start: at(1_u32, 0_u32),
            end: at(1_u32, 7_u32),
        };
        assert_eq!(
            edits(SourceText::from(LOOSE), Window::Within(comment)).expect("the document formats"),
            vec![replace(at(2_u32, 6_u32), at(2_u32, 8_u32), "")],
            "a comment belongs to the form after it"
        );
        let blank = Range {
            start: at(1_u32, 0_u32),
            end: at(1_u32, 0_u32),
        };
        assert_eq!(
            edits(
                SourceText::from("def  a =  1 ;\n\ndef b   = 2 ;\n"),
                Window::Within(blank)
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
                Window::Within(repaired)
            )
            .expect("the document formats"),
            Vec::new(),
            "a repaired form stays as written"
        );
    }
}
