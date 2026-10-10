//! The rows of a transcript block: the one layout every face draws.

use anodized::spec;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::SourceText;
use gandr_surface_render_remote::TranscriptBlock;

/// The mark a transcript line of one kind opens with, and the blank columns
/// as wide as it that indent the line's later rows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Mark
{
    /// The mark itself, which may be empty.
    text: &'static str,
    /// Blank columns as wide as the mark.
    indent: &'static str,
}

/// What a transcript row opens with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Lead
{
    /// The first row of a line: the mark of the line's kind.
    Mark(Mark),
    /// A later row holding text: blank columns as wide as the line's mark.
    Indent(Mark),
    /// A later row holding no text: nothing, so the row ends where it starts.
    Bare,
}

impl From<Lead> for &'static str
{
    /// The text the row opens with: the mark, its blank columns, or nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(lead: Lead) -> Self
    {
        match lead {
            | Lead::Mark(Mark { text, .. }) => text,
            | Lead::Indent(Mark { indent, .. }) => indent,
            | Lead::Bare => "",
        }
    }
}

/// One row of a transcript block, as every face lays it out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Row<'block>
{
    /// The kind of the line the row belongs to; the echo's rows are
    /// [`OutKind::Source`].
    pub kind: OutKind,
    /// What the row opens with.
    pub lead: Lead,
    /// The row's text, without its terminator.
    pub text: &'block str,
    /// Where the row's text starts in its line's text: in the block's source
    /// for the echo's rows, so the source's highlight spans address it.
    pub start: ByteOffset,
}

/// The mark a line of `kind` opens with.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `▸ ` for the echo, `= ` for a value, `? ` for a goal, `· ` for a
///   note or a stuck evaluation, `! ` for blame; nothing for a type line, which
///   spells its own `name : T`, nor for a diagnostic, which opens with its own
///   severity. Each mark's indent is as many blank columns as the mark is wide.
/// - provides: the kind marks, so a transcript without colour still tells its
///   lines apart.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a piped session's transcript is asserted line by line,
///   and a block's rows are asserted mark by mark.
/// - witness: `loop::tests::piped_value_prints_a_transcript`
/// - witness: `loop::tests::a_block_lays_out_as_rows`
/// - witness: `loop::tests::row_kinds_and_unicode_boundaries_keep_their_meaning`
#[spec(ensures: |ret| match kind {
    OutKind::Source => matches!(ret.text.as_bytes(), &[0xe2, 0x96, 0xb8, b' '])
        && matches!(ret.indent.as_bytes(), &[b' ', b' ']),
    OutKind::Value => matches!(ret.text.as_bytes(), &[b'=', b' '])
        && matches!(ret.indent.as_bytes(), &[b' ', b' ']),
    OutKind::Goal => matches!(ret.text.as_bytes(), &[b'?', b' '])
        && matches!(ret.indent.as_bytes(), &[b' ', b' ']),
    OutKind::Stuck | OutKind::Info => matches!(ret.text.as_bytes(), &[0xc2, 0xb7, b' '])
        && matches!(ret.indent.as_bytes(), &[b' ', b' ']),
    OutKind::Blame => matches!(ret.text.as_bytes(), &[b'!', b' '])
        && matches!(ret.indent.as_bytes(), &[b' ', b' ']),
    OutKind::Type | OutKind::Diag => ret.text.is_empty() && ret.indent.is_empty(),
})]
const fn mark(kind: OutKind) -> Mark
{
    match kind {
        | OutKind::Source => Mark {
            text: "▸ ",
            indent: "  ",
        },
        | OutKind::Value => Mark {
            text: "= ",
            indent: "  ",
        },
        | OutKind::Goal => Mark {
            text: "? ",
            indent: "  ",
        },
        | OutKind::Stuck | OutKind::Info => Mark {
            text: "· ",
            indent: "  ",
        },
        | OutKind::Blame => Mark {
            text: "! ",
            indent: "  ",
        },
        | OutKind::Type | OutKind::Diag => Mark {
            text: "",
            indent: "",
        },
    }
}

/// The rows of `text`, a line of `kind`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one row per line of `text` as [`str::lines`] splits it, each
///   without its terminator and starting at its byte offset in `text`; the
///   first opens with the kind's mark, a later one with text with the mark's
///   indent, and a later empty one with nothing.
/// - provides: the layout of one line of a block.
/// - fails: never.
/// - panics: none.
/// - executable: none — the opaque one-shot iterator exposes no row observer or
///   clone; consuming it in a postcondition would change the caller's rows.
///
/// # Adequacy
/// - hypothesis: L3 — a two-row echo, a three-row diagnostic with an empty
///   middle row, every output kind, Unicode byte offsets, CRLF and lone
///   carriage returns are asserted row by row.
/// - witness: `loop::tests::a_block_lays_out_as_rows`
/// - witness: `loop::tests::row_kinds_and_unicode_boundaries_keep_their_meaning`
fn line_rows(
    kind: OutKind,
    text: SourceText<'_>,
) -> impl Iterator<Item = Row<'_>>
{
    let mark = mark(kind);
    <&str>::from(text)
        .split_inclusive('\n')
        .scan(0_usize, |start, piece| {
            let at = *start;
            *start = start.saturating_add(piece.len());
            Some((ByteOffset::from(at), piece))
        })
        .enumerate()
        .map(move |(index, (start, piece))| {
            let text = piece
                .strip_suffix('\n')
                .map_or(piece, |line| line.strip_suffix('\r').unwrap_or(line));
            let lead = match (index, text.is_empty()) {
                | (0, _) => Lead::Mark(mark),
                | (_, true) => Lead::Bare,
                | (_, false) => Lead::Indent(mark),
            };
            Row {
                kind,
                lead,
                text,
                start,
            }
        })
}

/// The rows of `block`, in the order every face draws them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the echo's rows, then each result line's rows in the block's
///   order; a line's rows are the lines of its text, each without its
///   terminator and carrying its byte offset in that text. A line's first row
///   opens with its kind's mark — `▸ ` the echo, `= ` a value, `? ` a goal, `·
///   ` a note or a stuck evaluation, `! ` blame, nothing for a type line or a
///   diagnostic — a later row with text with blank columns as wide as the mark,
///   and a later empty row with nothing. A line with empty text has no row.
/// - provides: the one spelling of a block's layout that the plain transcript
///   and the terminal face both read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the opaque one-shot iterator exposes no row observer or
///   clone; consuming it in a postcondition would change the caller's rows.
///
/// # Adequacy
/// - hypothesis: L3 — a block with a two-row echo and a multi-row diagnostic is
///   asserted row by row, kinds, leads, texts and starts; a piped session's
///   transcript, written from these rows, is asserted line by line.
/// - witness: `loop::tests::a_block_lays_out_as_rows`
/// - witness: `loop::tests::piped_value_prints_a_transcript`
/// - witness: `loop::tests::row_kinds_and_unicode_boundaries_keep_their_meaning`
#[inline]
pub fn rows(block: &TranscriptBlock) -> impl Iterator<Item = Row<'_>>
{
    core::iter::once((OutKind::Source, block.source.as_str()))
        .chain(
            block
                .lines
                .iter()
                .map(|&(kind, ref text)| (kind, text.as_str())),
        )
        .flat_map(|(kind, text)| line_rows(kind, SourceText::from(text)))
}
