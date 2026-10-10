//! The presentation seam: the plain data a pipeline hands a renderer, and the
//! projection from a byte offset to a row and column.
//!
//! Every type here is owned data — strings, validated byte ranges and closed
//! enums — so it crosses a thread channel as it is, and a socket once the
//! `serde` feature gives it a wire image. The render-bus frame
//! ([`RenderFrame`]) carries these types as its report; an in-process
//! renderer reads them directly.
//!
//! [`RenderFrame`]: crate::wire::RenderFrame

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::diagnostic::DiagnosticCode;

/// A zero-based byte offset into a source document.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteOffset(usize);

impl From<usize> for ByteOffset
{
    /// Read a `usize` as a byte offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: usize) -> Self
    {
        Self(offset)
    }
}

impl From<ByteOffset> for usize
{
    /// Read the offset back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: ByteOffset) -> Self
    {
        offset.0
    }
}

impl fmt::Display for ByteOffset
{
    /// Write the offset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried count through the `usize` rendering, so
    ///   the width, fill and sign options the caller set apply to it.
    /// - provides: the offset a refusal's message quotes.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes its options and write status,
    ///   but not the rendered output needed to check their effect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independent goldens distinguish width, sign, zero
    ///   padding and nondefault alignment/fill. Numeric refusal parameters also
    ///   cover a maximum offset. These are bounded successful writes, not every
    ///   option combination or rejecting sink.
    /// - witness: `present::tests::byte_offsets_preserve_formatter_options`
    /// - witness: `present::tests::range_and_position_errors_preserve_numeric_parameters`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// The half-open byte range `[start, end)` a span, a mark or a card covers.
///
/// # Specification
/// - ensures: the start is at or below the end of every range, whether built by
///   [`ByteRange::new`] or decoded; an empty range is a position.
/// - provides: the wire image `{"start": s, "end": e}` under the `serde`
///   feature, whose decode refuses an inverted pair with [`InvertedRange`].
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteRange
{
    /// The offset of the first byte covered.
    start: ByteOffset,
    /// The offset one byte past the last byte covered.
    end: ByteOffset,
}

impl ByteRange
{
    /// The range from `start` up to, and not including, `end`.
    ///
    /// # Specification
    /// - requires: nothing — an inverted pair is admissible input and is
    ///   refused rather than reordered, because swapping the endpoints would
    ///   turn a mis-measured span into a plausible one.
    /// - ensures: on success the range's start and end are exactly the offered
    ///   offsets.
    /// - provides: the only way to build a range, so every range a card or a
    ///   span carries is ordered.
    /// - fails: [`InvertedRange`], carrying both offered offsets, when `end` is
    ///   strictly below `start`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`InvertedRange`] when `end < start`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — strict order, equality and inversion are
    ///   distinguished at ordinary offsets and the maximum representable
    ///   offset. Exact endpoints and typed refusals detect reordering or
    ///   narrowing, without claiming enumeration of every pair.
    /// - witness: `present::tests::byte_range_ordering_includes_offset_extremes`
    /// - witness: `present::tests::an_empty_range_is_a_position`
    /// - witness: `present::tests::an_inverted_range_is_refused`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(range) => start <= end && range.start == start && range.end == end,
        Err(error) => end < start && error.start == start && error.end == end,
    })]
    pub fn new(
        start: ByteOffset,
        end: ByteOffset,
    ) -> Result<Self, InvertedRange>
    {
        if end < start {
            return Err(InvertedRange { start, end });
        }

        Ok(Self { start, end })
    }

    /// The offset of the first byte covered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(self) -> ByteOffset
    {
        self.start
    }

    /// The offset one byte past the last byte covered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(self) -> ByteOffset
    {
        self.end
    }
}

/// The decode image of a [`ByteRange`]: its two endpoints before the ordering
/// check.
#[cfg(feature = "serde")]
#[derive(serde::Deserialize)]
struct ByteRangeWire
{
    /// The decoded first offset.
    start: ByteOffset,
    /// The decoded one-past-the-end offset.
    end: ByteOffset,
}

#[cfg(feature = "serde")]
impl<'input> serde::Deserialize<'input> for ByteRange
{
    /// Decode a range and refuse it when it is inverted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the range carries exactly the decoded endpoints.
    /// - fails: the deserializer's own error for a malformed image, and a
    ///   custom error carrying the [`InvertedRange`] message when the end lies
    ///   before the start.
    /// - panics: none.
    ///
    /// # Errors
    /// The deserializer's error, or the inverted-range refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — independent JSON images fix endpoint roles; ordered
    ///   and equal endpoints decode while an inversion fails as a data error.
    ///   These witnesses cover JSON, not arbitrary deserializer failures.
    /// - witness: `present::tests::byte_ranges_keep_the_existing_json_shape`
    /// - witness: `present::tests::an_inverted_range_is_refused_on_decode`
    #[inline]
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |range| range.start <= range.end))]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'input>,
    {
        let wire = ByteRangeWire::deserialize(deserializer)?;

        Self::new(wire.start, wire.end).map_err(serde::de::Error::custom)
    }
}

/// The refusal of a byte range whose end lies before its start.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InvertedRange
{
    /// The offered start.
    pub start: ByteOffset,
    /// The offered end, strictly below the start.
    pub end: ByteOffset,
}

impl fmt::Display for InvertedRange
{
    /// Write the refusal with both offsets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: names the offered start and end, in that order.
    /// - provides: the message a decode failure carries.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes write status, not the text
    ///   emitted into the caller's sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ordered numeric parameters are observed in
    ///   successful formatting without pinning the surrounding prose. This
    ///   detects missing, duplicated or swapped parameters on the boundary
    ///   fixtures, not every wording error or rejecting formatter sink.
    /// - witness: `present::tests::range_and_position_errors_preserve_numeric_parameters`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "byte range {}..{} ends before it starts",
            self.start, self.end
        )
    }
}

impl core::error::Error for InvertedRange
{
}

/// A semantic highlight role.
///
/// One vocabulary for every renderer — the language server's token legend,
/// the terminal face's theme and a bus client alike — so a highlighter
/// classifies once and each renderer maps the role to its own styling.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HlRole
{
    /// A language keyword.
    Keyword,
    /// An operator, of a term or of a shell redirection.
    Operator,
    /// A defined function name.
    FunctionDef,
    /// A called function or command name.
    FunctionCall,
    /// A defined value or binder name.
    VariableDef,
    /// A parameter binder.
    VariableParam,
    /// A record or co-record member.
    Member,
    /// A plain variable reference.
    Variable,
    /// A constructor.
    Constructor,
    /// A type identifier.
    Type,
    /// A built-in or primitive type.
    TypeBuiltin,
    /// A type variable.
    TypeVariable,
    /// A numeric literal, grades and file descriptors included.
    Number,
    /// A boolean literal.
    Boolean,
    /// A character literal.
    Character,
    /// A string literal.
    StringLit,
    /// An escape sequence inside a literal.
    Escape,
    /// A comment.
    Comment,
    /// A typed hole, `?` or `?name`.
    Hole,
    /// A label: a session field, a world, a hole's name.
    Label,
    /// A shell word or path.
    Path,
    /// A directive, such as a shebang.
    Directive,
    /// Anything not otherwise classified.
    Other,
}

/// A highlight span: a byte range of the source classified by role.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HlSpan
{
    /// The classified byte range.
    pub range: ByteRange,
    /// The role it is classified by.
    pub role: HlRole,
}

/// What a mark denotes: an error at the marked range, or an empty hole's tint.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MarkKind
{
    /// The marked range is in error.
    Error,
    /// The marked range is an empty hole, tinted rather than underlined.
    EmptyHole,
}

/// A mark span: a byte range a marking pass decorated, with its one-line
/// description.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MarkSpan
{
    /// The marked byte range.
    pub range: ByteRange,
    /// What the mark denotes.
    pub kind: MarkKind,
    /// The mark's description, already rendered.
    pub message: String,
}

/// A diagnostic card: one refusal with its partial derivation.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiagCard
{
    /// The stable registry code.
    pub code: DiagnosticCode,
    /// The primary message, already rendered.
    pub message: String,
    /// The source range, absent when the producer could not locate the
    /// failure — never a guessed enclosing range.
    pub span: Option<ByteRange>,
    /// The offending expression, when the producer recorded one.
    pub expr: Option<String>,
    /// The elaboration note for a synthesized node, absent for one written in
    /// the source.
    pub elaboration: Option<String>,
    /// The partial derivation, outermost first: each entry one "while
    /// checking" step.
    pub chain: Vec<String>,
}

/// A goal card: a hole with its expected type and local context.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GoalCard
{
    /// The display label, `?0` or `?name`.
    pub label: String,
    /// What the hole elides, rendered.
    pub note: String,
    /// The expected type at the hole, rendered, absent when checking did not
    /// reach the hole.
    pub expected: Option<String>,
    /// The local bindings beyond the session context, each `name : type`,
    /// innermost shadowing applied.
    pub ctx: Vec<String>,
    /// The hole's byte range in the source.
    pub range: ByteRange,
}

/// The kind of one rendered transcript line; a renderer styles each kind at
/// draw time, so a theme change restyles the history.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OutKind
{
    /// An echoed source line.
    Source,
    /// A type line, `name : T` or `: T`.
    Type,
    /// An evaluated value line, `= v`.
    Value,
    /// A runtime blame line.
    Blame,
    /// A stuck evaluation line.
    Stuck,
    /// A diagnostic line.
    Diag,
    /// A goal line.
    Goal,
    /// An informational line: a banner or a meta-command's output.
    Info,
}

/// One transcript block: an echoed submission and its rendered results.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TranscriptBlock
{
    /// The submitted source, echoed with highlighting.
    pub source: String,
    /// The highlight spans over [`Self::source`].
    pub source_hl: Vec<HlSpan>,
    /// The rendered result lines, in presentation order.
    pub lines: Vec<(OutKind, String)>,
}

/// Source text addressed by byte offsets.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceText<'source>(&'source str);

impl<'source> From<&'source str> for SourceText<'source>
{
    /// Address `text` by byte offsets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'source str) -> Self
    {
        Self(text)
    }
}

impl<'source> From<SourceText<'source>> for &'source str
{
    /// Read the text back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: SourceText<'source>) -> Self
    {
        text.0
    }
}

/// A zero-based row of a source text.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PositionRow(usize);

impl From<usize> for PositionRow
{
    /// Read a `usize` as a row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(row: usize) -> Self
    {
        Self(row)
    }
}

impl From<PositionRow> for usize
{
    /// Read the row back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(row: PositionRow) -> Self
    {
        row.0
    }
}

/// A zero-based character column within a row.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PositionColumn(usize);

impl From<usize> for PositionColumn
{
    /// Read a `usize` as a column.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(column: usize) -> Self
    {
        Self(column)
    }
}

impl From<PositionColumn> for usize
{
    /// Read the column back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(column: PositionColumn) -> Self
    {
        column.0
    }
}

/// The row and column of a byte offset, both zero-based; the column counts
/// characters, not bytes.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Pos
{
    /// The zero-based row.
    pub row: PositionRow,
    /// The zero-based character column within the row.
    pub col: PositionColumn,
}

/// The refusal of a byte offset that lands inside a character.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PosOfByteError
{
    /// The offered offset, strictly inside a multi-byte character.
    pub byte: ByteOffset,
}

impl fmt::Display for PosOfByteError
{
    /// Write the refusal with the offset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: names the offered offset.
    /// - provides: the message a projection failure carries.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes write status, not the text
    ///   emitted into the caller's sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the ordered numeric parameters are observed in
    ///   successful formatting without pinning the surrounding prose. This
    ///   detects missing, duplicated or swapped parameters on the boundary
    ///   fixtures, not every wording error or rejecting formatter sink.
    /// - witness: `present::tests::range_and_position_errors_preserve_numeric_parameters`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "byte offset {} is inside a character", self.byte)
    }
}

impl core::error::Error for PosOfByteError
{
}

/// The position of `byte` in `text`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for an offset at a character's first byte, the row counts the
///   newlines before it and the column counts the characters between the last
///   of them and it; a newline belongs to the row it ends. An offset at or past
///   the end of the text is the position after its last character, so the empty
///   text has the one position `0:0`.
/// - provides: the row and character column an editor widget addresses.
/// - fails: [`PosOfByteError`], carrying the offset, when `byte` lies strictly
///   inside a multi-byte character.
/// - panics: none.
///
/// # Errors
/// [`PosOfByteError`] when `byte` is inside a character.
///
/// # Adequacy
/// - hypothesis: L3 — exact positions and refusals distinguish ASCII, two-,
///   three- and four-byte characters, interior bytes, newline boundaries, empty
///   text and end clamping. L2 inverse checks cover each character start in
///   finite fixtures, not the entire Unicode/input space.
/// - witness: `present::tests::positions_round_trip_on_ascii`
/// - witness: `present::tests::positions_round_trip_on_multibyte_text`
/// - witness: `present::tests::positions_count_characters_not_bytes`
/// - witness: `present::tests::pos_of_byte_rejects_interior_multibyte_offsets`
/// - witness: `present::tests::out_of_range_positions_clamp`
/// - witness: `present::tests::the_empty_source_has_one_position`
/// - witness: `present::tests::the_end_of_the_source_is_a_position`
#[inline]
#[spec(ensures: |ret| match ret {
    Ok(at) => text.0.get(..byte.0.min(text.0.len())).is_some_and(|prefix|
        at.row.0 == prefix.bytes().filter(|&ch| ch == b'\n').count()
            && at.col.0 == prefix.rsplit('\n').next().map_or(0, |line| line.chars().count())),
    Err(error) => byte.0 < text.0.len() && !text.0.is_char_boundary(byte.0) && error.byte == byte,
})]
pub fn pos_of_byte(
    text: SourceText<'_>,
    byte: ByteOffset,
) -> Result<Pos, PosOfByteError>
{
    // No trait yields a text's characters with their byte offsets, so the
    // walk reads the string here, the one site that needs both.
    // economy: one walk up to `byte` per call; a renderer projecting many
    // offsets over one text keeps its own line index.
    let mut row = 0_usize;
    let mut col = 0_usize;
    for (offset, character) in text.0.char_indices() {
        let offset = ByteOffset(offset);
        if offset == byte {
            return Ok(Pos {
                row: PositionRow(row),
                col: PositionColumn(col),
            });
        }
        if offset > byte {
            return Err(PosOfByteError { byte });
        }
        if character == '\n' {
            row = row.saturating_add(1);
            col = 0;
        }
        else {
            col = col.saturating_add(1);
        }
    }
    if byte < ByteOffset(text.0.len()) {
        return Err(PosOfByteError { byte });
    }

    Ok(Pos {
        row: PositionRow(row),
        col: PositionColumn(col),
    })
}

/// The byte offset of `pos` in `text`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the offset of the character at `pos`; a column past the end of
///   its row is the offset of that row's newline, or of the end of the text on
///   the last row; a row past the last is the end of the text. On every
///   character start `b`, `byte_of_pos(text, pos_of_byte(text, b)) == b`.
/// - provides: the byte offset an editor position addresses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact offsets distinguish character columns, missing
///   rows, overlong columns and empty text. L2 inverse checks cover the
///   character starts of finite ASCII and multibyte fixtures; they do not
///   independently establish a universal inverse.
/// - witness: `present::tests::positions_round_trip_on_ascii`
/// - witness: `present::tests::positions_round_trip_on_multibyte_text`
/// - witness: `present::tests::positions_count_characters_not_bytes`
/// - witness: `present::tests::out_of_range_positions_clamp`
/// - witness: `present::tests::the_empty_source_has_one_position`
/// - witness: `present::tests::the_end_of_the_source_is_a_position`
#[inline]
#[must_use]
#[spec(ensures: |ret| text.0.split('\n').nth(pos.row.0).map_or(
    ret.0 == text.0.len(),
    |line| {
        let start = text.0.split('\n').take(pos.row.0).fold(0_usize,
            |bytes, previous| bytes.saturating_add(previous.len()).saturating_add(1));
        let column = line.char_indices().nth(pos.col.0).map_or(line.len(), |(offset, _)| offset);
        ret.0 == start.saturating_add(column)
    },
))]
pub fn byte_of_pos(
    text: SourceText<'_>,
    pos: Pos,
) -> ByteOffset
{
    // No trait yields a text's characters with their byte offsets, so the
    // walk reads the string here, the one site that needs both.
    // economy: one walk up to `pos` per call; a renderer projecting many
    // positions over one text keeps its own line index.
    let mut row = 0_usize;
    let mut col = 0_usize;
    for (offset, character) in text.0.char_indices() {
        let at_row = PositionRow(row) == pos.row;
        if at_row && PositionColumn(col) == pos.col {
            return ByteOffset(offset);
        }
        if character == '\n' {
            if at_row {
                return ByteOffset(offset);
            }
            row = row.saturating_add(1);
            col = 0;
        }
        else {
            col = col.saturating_add(1);
        }
    }

    ByteOffset(text.0.len())
}

/// A zero-based column within a row, counted in UTF-16 code units: the column
/// a language server addresses.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Utf16Column(usize);

impl From<usize> for Utf16Column
{
    /// Read a `usize` as a UTF-16 column.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(column: usize) -> Self
    {
        Self(column)
    }
}

impl From<Utf16Column> for usize
{
    /// Read the column back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(column: Utf16Column) -> Self
    {
        column.0
    }
}

/// The row and UTF-16 column of a byte offset, both zero-based.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Utf16Pos
{
    /// The zero-based row.
    pub row: PositionRow,
    /// The zero-based column within the row, in UTF-16 code units.
    pub col: Utf16Column,
}

/// One text with the byte offset each of its rows starts at: the projection a
/// renderer reads when it addresses many offsets of one text in UTF-16 code
/// units.
///
/// # Specification
/// - ensures: rows end at `\n`, at `\r\n` and at a `\r` no `\n` follows, the
///   three terminators the language server protocol fixes; a terminator belongs
///   to the row it ends. The index is read off its own text, so no offset is
///   ever projected against another.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LineIndex<'source>
{
    /// The text the rows are read off.
    text: &'source str,
    /// The offset of the first byte of every row, ascending; the first is 0.
    starts: Vec<ByteOffset>,
}

impl<'source> LineIndex<'source>
{
    /// Index the rows of `text`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per terminator plus one, each starting just past the
    ///   terminator before it; the empty text has one row.
    /// - provides: the index every projection of `text` reads.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the text's bytes; a terminator is ASCII, so
    ///   no byte of a multi-byte character is mistaken for one.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact row extents cover all three terminators,
    ///   adjacent empty rows, trailing terminators and empty text. These finite
    ///   boundaries distinguish CRLF coalescing from double counting; they do
    ///   not enumerate arbitrary text.
    /// - witness: `present::tests::utf16_rows_end_at_every_protocol_terminator`
    /// - witness: `present::tests::utf16_positions_clamp_past_the_end`
    /// - witness: `present::tests::adjacent_terminators_preserve_empty_rows_and_crlf_clamping`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref ret| ret.text == text.0
        && ret.starts.iter().map(|start| start.0).eq(core::iter::once(0_usize).chain(
            text.0.match_indices(['\r', '\n'])
                .filter(|&(offset, terminator)| terminator != "\r"
                    || text.0.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n'))
                .map(|(offset, _)| offset.saturating_add(1))
        ))
    )]
    pub fn new(text: SourceText<'source>) -> Self
    {
        let bytes = text.0.as_bytes();
        let mut starts = vec![ByteOffset(0)];
        // No trait yields a text's terminators with their offsets, so the
        // pass reads the bytes here, the one site that needs both.
        for (offset, &byte) in bytes.iter().enumerate() {
            let next = offset.saturating_add(1);
            let ends_row = match byte {
                | b'\n' => true,
                | b'\r' => bytes.get(next) != Some(&b'\n'),
                | _ => false,
            };
            if ends_row {
                starts.push(ByteOffset(next));
            }
        }
        Self {
            text: text.0,
            starts,
        }
    }

    /// The position of `byte`, its column counted in UTF-16 code units.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for an offset at a character's first byte, the row it sits in
    ///   and the UTF-16 code units of the characters between that row's start
    ///   and it: one for a character of the basic plane, two for one beyond it.
    ///   An offset at or past the end of the text is the position after its
    ///   last character.
    /// - provides: the position a language server sends for a byte offset.
    /// - fails: [`PosOfByteError`], carrying the offset, when `byte` lies
    ///   strictly inside a multi-byte character.
    /// - panics: none.
    /// - intension: a binary search for the row, then one walk from the row's
    ///   start to `byte`.
    ///
    /// # Errors
    /// [`PosOfByteError`] when `byte` is inside a character.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are an offset at a character's
    ///   start on either side of one-, two-, three- and four-byte characters,
    ///   each interior byte, a row start after each terminator, the end and
    ///   past it; each separated by an exact position or the exact refusal.
    /// - witness: `present::tests::utf16_columns_count_code_units_across_a_multibyte_boundary`
    /// - witness: `present::tests::utf16_rows_end_at_every_protocol_terminator`
    /// - witness: `present::tests::utf16_positions_clamp_past_the_end`
    /// - witness: `present::tests::adjacent_terminators_preserve_empty_rows_and_crlf_clamping`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(at) => self.starts.get(at.row.0).is_some_and(|start| {
            let end = byte.0.min(self.text.len());
            start.0 <= end
                && self.starts.get(at.row.0.saturating_add(1)).is_none_or(|next| end < next.0)
                && self.text.get(start.0..end).is_some_and(|prefix| prefix.encode_utf16().count() == at.col.0)
        }),
        Err(error) => byte.0 < self.text.len() && !self.text.is_char_boundary(byte.0) && error.byte == byte,
    })]
    pub fn utf16_pos_of_byte(
        &self,
        byte: ByteOffset,
    ) -> Result<Utf16Pos, PosOfByteError>
    {
        let row = self
            .starts
            .partition_point(|start| *start <= byte)
            .saturating_sub(1);
        let start = self.starts.get(row).copied().unwrap_or_default();
        let tail = self.text.get(start.0 ..).unwrap_or_default();
        // No trait yields a text's characters with their byte offsets, so the
        // walk reads the string here, the one site that needs both.
        let mut col = 0_usize;
        for (offset, character) in tail.char_indices() {
            let at = ByteOffset(start.0.saturating_add(offset));
            if at == byte {
                return Ok(Utf16Pos {
                    row: PositionRow(row),
                    col: Utf16Column(col),
                });
            }
            if at > byte {
                return Err(PosOfByteError { byte });
            }
            col = col.saturating_add(character.len_utf16());
        }
        if byte < ByteOffset(self.text.len()) {
            return Err(PosOfByteError { byte });
        }

        Ok(Utf16Pos {
            row: PositionRow(row),
            col: Utf16Column(col),
        })
    }

    /// The byte offset of `pos`, its column counted in UTF-16 code units.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the offset of the character whose code units cover `pos`'s
    ///   column, so a column between the two units of a character beyond the
    ///   basic plane is that character's first byte; a column past the end of
    ///   its row is the offset of the row's terminator, or of the end of the
    ///   text on the last row; a row past the last is the end of the text. On
    ///   each content-character start and the first byte of a terminator, the
    ///   projections are inverse. The LF inside CRLF instead maps back to its
    ///   preceding CR, because an overlong column clamps to the terminator.
    /// - provides: the byte offset a language server position addresses.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact offsets distinguish surrogate-pair flooring,
    ///   each terminator, CRLF-interior clamping, missing rows and empty text.
    ///   L2 inverse checks cover finite content-character boundaries; CRLF's
    ///   second byte is deliberately normalized to the terminator start.
    /// - witness: `present::tests::utf16_columns_count_code_units_across_a_multibyte_boundary`
    /// - witness: `present::tests::utf16_rows_end_at_every_protocol_terminator`
    /// - witness: `present::tests::utf16_positions_clamp_past_the_end`
    /// - witness: `present::tests::adjacent_terminators_preserve_empty_rows_and_crlf_clamping`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| {
        let row = self.row_bytes(pos.row);
        row.start <= ret && ret <= row.end
            && self.text.get(row.start.0..ret.0).is_some_and(|prefix| {
                let column = prefix.encode_utf16().count();
                if ret == row.end { pos.col.0 >= column }
                else {
                    self.text.get(ret.0..row.end.0).and_then(|tail| tail.chars().next())
                        .is_some_and(|ch| column <= pos.col.0
                            && pos.col.0 < column.saturating_add(ch.len_utf16()))
                }
            })
    })]
    pub fn byte_of_utf16_pos(
        &self,
        pos: Utf16Pos,
    ) -> ByteOffset
    {
        let row = self.row_bytes(pos.row);
        let content = self.text.get(row.start.0 .. row.end.0).unwrap_or_default();
        let mut col = 0_usize;
        for (offset, character) in content.char_indices() {
            let next = col.saturating_add(character.len_utf16());
            if pos.col.0 < next {
                return ByteOffset(row.start.0.saturating_add(offset));
            }
            col = next;
        }

        row.end
    }

    /// The bytes of `row`, its terminator excluded.
    ///
    /// # Specification
    /// - requires: nothing; a row past the last is admissible input.
    /// - ensures: the range from the row's first byte up to its terminator, or
    ///   to the end of the text on the last row; a row past the last is the
    ///   empty range at the end of the text.
    /// - provides: the extent a renderer splits a span spanning rows by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact ranges cover each terminator, adjacent empty
    ///   rows, the final row and rows beyond it, including the maximum row
    ///   index. These fixtures distinguish terminator exclusion and clamping,
    ///   without claiming exhaustive Unicode coverage.
    /// - witness: `present::tests::utf16_rows_end_at_every_protocol_terminator`
    /// - witness: `present::tests::utf16_positions_clamp_past_the_end`
    /// - witness: `present::tests::adjacent_terminators_preserve_empty_rows_and_crlf_clamping`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.start <= ret.end && ret.end.0 <= self.text.len()
        && self.starts.get(row.0).map_or(
            ret.start.0 == self.text.len() && ret.end.0 == self.text.len(),
            |&start| ret.start == start
                && self.text.get(ret.start.0..ret.end.0).is_some_and(|content| !content.contains(['\r', '\n']))
                && self.starts.get(row.0.saturating_add(1)).map_or(
                    ret.end.0 == self.text.len(),
                    |next| self.text.get(ret.end.0..next.0)
                        .is_some_and(|terminator| matches!(terminator, "\r" | "\n" | "\r\n")),
                ),
        )
    )]
    pub fn row_bytes(
        &self,
        row: PositionRow,
    ) -> ByteRange
    {
        let end_of_text = ByteOffset(self.text.len());
        let Some(&start) = self.starts.get(row.0)
        else {
            return ByteRange {
                start: end_of_text,
                end: end_of_text,
            };
        };
        let end = match self.starts.get(row.0.saturating_add(1)) {
            | Some(&next) => {
                let bytes = self.text.as_bytes();
                let last = next.0.saturating_sub(1);
                let before = last.checked_sub(1);
                let crlf = bytes.get(last) == Some(&b'\n')
                    && before.and_then(|before| bytes.get(before)) == Some(&b'\r');
                ByteOffset(if crlf { last.saturating_sub(1) } else { last })
            },
            | None => end_of_text,
        };
        ByteRange { start, end }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::string::ToString as _;
    use alloc::vec;

    use anodized::spec;

    use super::ByteOffset;
    use super::ByteRange;
    use super::DiagCard;
    use super::GoalCard;
    use super::HlRole;
    use super::HlSpan;
    use super::InvertedRange;
    use super::LineIndex;
    use super::MarkKind;
    use super::MarkSpan;
    use super::OutKind;
    use super::Pos;
    use super::PosOfByteError;
    use super::PositionColumn;
    use super::PositionRow;
    use super::SourceText;
    use super::TranscriptBlock;
    use super::Utf16Column;
    use super::Utf16Pos;
    use super::byte_of_pos;
    use super::pos_of_byte;
    use crate::diagnostic::DiagnosticCode;

    /// A start and an end offset, written as two counts.
    struct Bytes(usize, usize);

    /// The range a [`Bytes`] pair spells, which the caller knows is ordered.
    ///
    /// # Specification
    /// - requires: the start does not exceed the end.
    /// - ensures: the range retains both offered endpoints.
    /// - fails: never on the admitted domain.
    /// - panics: an inverted pair violates the precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and nonempty ranges support independent row
    ///   extent and JSON-image assertions, distinguishing endpoint swaps on
    ///   those fixtures. Invalid helper input is outside the admitted domain.
    /// - witness: `present::tests::utf16_rows_end_at_every_protocol_terminator`
    /// - witness: `present::tests::byte_ranges_keep_the_existing_json_shape`
    #[spec(
        requires: start <= end,
        ensures: |ret| ret.start.0 == start && ret.end.0 == end,
    )]
    fn range(Bytes(start, end): Bytes) -> ByteRange
    {
        ByteRange::new(ByteOffset::from(start), ByteOffset::from(end)).expect("an ordered range")
    }

    /// A row and a column, written as two counts.
    struct At(usize, usize);

    /// The position an [`At`] pair spells.
    ///
    /// # Specification
    /// trivial.
    fn pos(At(row, col): At) -> Pos
    {
        Pos {
            row: PositionRow::from(row),
            col: PositionColumn::from(col),
        }
    }

    /// The UTF-16 position an [`At`] pair spells.
    ///
    /// # Specification
    /// trivial.
    fn utf16(At(row, col): At) -> Utf16Pos
    {
        Utf16Pos {
            row: PositionRow::from(row),
            col: Utf16Column::from(col),
        }
    }

    #[test]
    fn utf16_columns_count_code_units_across_a_multibyte_boundary()
    {
        // Bytes: a=1 at 0, é=2 at 1, €=3 at 3, 𝄞=4 at 6, b=1 at 10, \n at 11,
        // z at 12. UTF-16 units: a, é and € one each, 𝄞 two, b one.
        let source = "aé€𝄞b\nz";
        let index = LineIndex::new(SourceText::from(source));
        let starts = [
            (0_usize, At(0, 0)),
            (1, At(0, 1)),
            (3, At(0, 2)),
            (6, At(0, 3)),
            (10, At(0, 5)),
            (11, At(0, 6)),
            (12, At(1, 0)),
            (13, At(1, 1)),
        ];
        for (byte, at) in starts {
            let expected = utf16(at);
            assert_eq!(
                Ok(expected),
                index.utf16_pos_of_byte(ByteOffset::from(byte)),
                "byte {byte} projects to its UTF-16 position"
            );
            assert_eq!(
                ByteOffset::from(byte),
                index.byte_of_utf16_pos(expected),
                "byte {byte} round-trips"
            );
        }
        for interior in [2_usize, 4, 5, 7, 8, 9] {
            assert_eq!(
                Err(PosOfByteError {
                    byte: ByteOffset::from(interior),
                }),
                index.utf16_pos_of_byte(ByteOffset::from(interior)),
                "byte {interior} is inside a character"
            );
        }
        assert_eq!(
            ByteOffset::from(6_usize),
            index.byte_of_utf16_pos(utf16(At(0, 4))),
            "a column between the two units of 𝄞 resolves to its first byte"
        );
    }

    #[test]
    fn utf16_rows_end_at_every_protocol_terminator()
    {
        // Rows: "a" ended by \r\n, "b" by a lone \r, "c" by \n, then "d".
        let source = "a\r\nb\rc\nd";
        let index = LineIndex::new(SourceText::from(source));
        let rows = [
            (0_usize, Bytes(0, 1)),
            (1, Bytes(3, 4)),
            (2, Bytes(5, 6)),
            (3, Bytes(7, 8)),
            (4, Bytes(8, 8)),
        ];
        for (row, bytes) in rows {
            assert_eq!(
                range(bytes),
                index.row_bytes(PositionRow::from(row)),
                "row {row} spans its content, its terminator excluded"
            );
        }
        assert_eq!(
            Ok(utf16(At(1, 0))),
            index.utf16_pos_of_byte(ByteOffset::from(3_usize)),
            "the byte after \\r\\n opens the next row"
        );
        assert_eq!(
            Ok(utf16(At(2, 0))),
            index.utf16_pos_of_byte(ByteOffset::from(5_usize)),
            "the byte after a lone \\r opens the next row"
        );
        assert_eq!(
            Ok(utf16(At(0, 2))),
            index.utf16_pos_of_byte(ByteOffset::from(2_usize)),
            "the \\n of \\r\\n belongs to the row it ends"
        );
        assert_eq!(
            ByteOffset::from(1_usize),
            index.byte_of_utf16_pos(utf16(At(0, 9))),
            "a column past a row ended by \\r\\n is its \\r"
        );
        assert_eq!(
            ByteOffset::from(4_usize),
            index.byte_of_utf16_pos(utf16(At(1, 9))),
            "a column past a row ended by a lone \\r is that \\r"
        );
        assert_eq!(
            ByteOffset::from(6_usize),
            index.byte_of_utf16_pos(utf16(At(2, 9))),
            "a column past a row ended by \\n is that \\n"
        );
    }

    #[test]
    fn utf16_positions_clamp_past_the_end()
    {
        let index = LineIndex::new(SourceText::from("ab\ncd"));
        assert_eq!(
            Ok(utf16(At(1, 2))),
            index.utf16_pos_of_byte(ByteOffset::from(999_usize)),
            "an offset past the end is the final position"
        );
        assert_eq!(
            ByteOffset::from(5_usize),
            index.byte_of_utf16_pos(utf16(At(1, 99))),
            "a column past the last row's end is the end of the text"
        );
        assert_eq!(
            ByteOffset::from(5_usize),
            index.byte_of_utf16_pos(utf16(At(9, 0))),
            "a row past the last is the end of the text"
        );

        let empty = LineIndex::new(SourceText::from(""));
        assert_eq!(
            Ok(utf16(At(0, 0))),
            empty.utf16_pos_of_byte(ByteOffset::from(0_usize)),
            "the empty text has the one position 0:0"
        );
        assert_eq!(
            ByteOffset::from(0_usize),
            empty.byte_of_utf16_pos(utf16(At(2, 4))),
            "any position of the empty text is offset 0"
        );
        assert_eq!(
            range(Bytes(0, 0)),
            empty.row_bytes(PositionRow::from(0_usize)),
            "the empty text's one row is empty"
        );

        let trailing = LineIndex::new(SourceText::from("ab\n"));
        assert_eq!(
            Ok(utf16(At(1, 0))),
            trailing.utf16_pos_of_byte(ByteOffset::from(3_usize)),
            "after a trailing newline the end opens an empty row"
        );
    }

    #[test]
    fn byte_range_ordering_includes_offset_extremes()
    {
        let zero = ByteOffset::from(0_usize);
        let maximum = ByteOffset::from(usize::MAX);
        assert_eq!(
            Ok(ByteRange {
                start: zero,
                end: maximum
            }),
            ByteRange::new(zero, maximum)
        );
        assert_eq!(
            Ok(ByteRange {
                start: maximum,
                end: maximum
            }),
            ByteRange::new(maximum, maximum)
        );
        assert_eq!(
            Err(InvertedRange {
                start: maximum,
                end: zero
            }),
            ByteRange::new(maximum, zero)
        );
    }

    #[test]
    fn an_empty_range_is_a_position()
    {
        let empty = ByteRange::new(ByteOffset::from(4_usize), ByteOffset::from(4_usize))
            .expect("an empty range is admitted");
        assert_eq!(
            ByteOffset::from(4_usize),
            empty.start(),
            "the start is kept"
        );
        assert_eq!(ByteOffset::from(4_usize), empty.end(), "the end is kept");
    }

    #[test]
    fn an_inverted_range_is_refused()
    {
        assert_eq!(
            Err(InvertedRange {
                start: ByteOffset::from(5_usize),
                end: ByteOffset::from(4_usize),
            }),
            ByteRange::new(ByteOffset::from(5_usize), ByteOffset::from(4_usize)),
            "an end one below the start is refused with both offsets"
        );
    }

    #[test]
    fn byte_ranges_keep_the_existing_json_shape()
    {
        let hl = HlSpan {
            range: range(Bytes(3, 7)),
            role: HlRole::Keyword,
        };
        let hl_json = serde_json::to_value(hl).expect("serialize highlight");
        assert_eq!(
            serde_json::json!({
                "range": {"start": 3_usize, "end": 7_usize},
                "role": "Keyword",
            }),
            hl_json,
            "a highlight is its range and its role"
        );
        let decoded_hl: HlSpan = serde_json::from_value(hl_json).expect("deserialize highlight");
        assert_eq!(hl, decoded_hl, "the highlight round-trips");

        let mark = MarkSpan {
            range: range(Bytes(2, 5)),
            kind: MarkKind::Error,
            message: "unbound".to_owned(),
        };
        let mark_json = serde_json::to_value(&mark).expect("serialize mark");
        assert_eq!(
            serde_json::json!({
                "range": {"start": 2_usize, "end": 5_usize},
                "kind": "Error",
                "message": "unbound",
            }),
            mark_json,
            "a mark is its range, its kind and its message"
        );
        let decoded_mark: MarkSpan = serde_json::from_value(mark_json).expect("deserialize mark");
        assert_eq!(mark, decoded_mark, "the mark round-trips");

        let diag = DiagCard {
            code: DiagnosticCode::TypeMismatch,
            message: "type mismatch".to_owned(),
            span: Some(range(Bytes(1, 4))),
            expr: Some("f x".to_owned()),
            elaboration: Some("elaborated here".to_owned()),
            chain: vec!["while checking f".to_owned(), "in application".to_owned()],
        };
        let diag_json = serde_json::to_value(&diag).expect("serialize diagnostic");
        assert_eq!(
            serde_json::json!({
                "code": "E0001",
                "message": "type mismatch",
                "span": {"start": 1_usize, "end": 4_usize},
                "expr": "f x",
                "elaboration": "elaborated here",
                "chain": ["while checking f", "in application"],
            }),
            diag_json,
            "a diagnostic card carries its code by its stable spelling"
        );
        let decoded_diag: DiagCard =
            serde_json::from_value(diag_json).expect("deserialize diagnostic");
        assert_eq!(diag, decoded_diag, "the diagnostic card round-trips");

        let unlocated = DiagCard {
            span: None,
            expr: None,
            elaboration: None,
            chain: vec![],
            ..diag
        };
        let unlocated_json = serde_json::to_value(&unlocated).expect("serialize diagnostic");
        assert_eq!(
            serde_json::json!({
                "code": "E0001",
                "message": "type mismatch",
                "span": null,
                "expr": null,
                "elaboration": null,
                "chain": [],
            }),
            unlocated_json,
            "an unlocated card says so rather than claiming a range"
        );
        let decoded_unlocated: DiagCard =
            serde_json::from_value(unlocated_json).expect("deserialize diagnostic");
        assert_eq!(
            unlocated, decoded_unlocated,
            "the unlocated card round-trips"
        );

        let goal = GoalCard {
            label: "?0".to_owned(),
            note: "hole note".to_owned(),
            expected: Some("Nat".to_owned()),
            ctx: vec!["x : Nat".to_owned()],
            range: range(Bytes(10, 12)),
        };
        let goal_json = serde_json::to_value(&goal).expect("serialize goal");
        assert_eq!(
            serde_json::json!({
                "label": "?0",
                "note": "hole note",
                "expected": "Nat",
                "ctx": ["x : Nat"],
                "range": {"start": 10_usize, "end": 12_usize},
            }),
            goal_json,
            "a goal card is its label, note, expected type, context and range"
        );
        let decoded_goal: GoalCard = serde_json::from_value(goal_json).expect("deserialize goal");
        assert_eq!(goal, decoded_goal, "the goal card round-trips");

        let block = TranscriptBlock {
            source: "def x = 1".to_owned(),
            source_hl: vec![HlSpan {
                range: range(Bytes(0, 3)),
                role: HlRole::Keyword,
            }],
            lines: vec![(OutKind::Value, "= 1".to_owned())],
        };
        let block_json = serde_json::to_value(&block).expect("serialize transcript block");
        assert_eq!(
            serde_json::json!({
                "source": "def x = 1",
                "source_hl": [{"range": {"start": 0_usize, "end": 3_usize}, "role": "Keyword"}],
                "lines": [["Value", "= 1"]],
            }),
            block_json,
            "a transcript block is its source, its highlights and its lines"
        );
        let decoded_block: TranscriptBlock =
            serde_json::from_value(block_json).expect("deserialize transcript block");
        assert_eq!(block, decoded_block, "the transcript block round-trips");
    }

    #[test]
    fn an_inverted_range_is_refused_on_decode()
    {
        let refused = serde_json::from_value::<ByteRange>(serde_json::json!({
            "start": 5_usize,
            "end": 4_usize,
        }))
        .expect_err("an inverted image decodes to nothing");
        assert!(refused.is_data());

        let empty = serde_json::from_value::<ByteRange>(serde_json::json!({
            "start": 4_usize,
            "end": 4_usize,
        }))
        .expect("an empty image decodes");
        assert_eq!(range(Bytes(4, 4)), empty, "the empty range is kept");
    }

    #[test]
    fn positions_round_trip_on_ascii()
    {
        let text = SourceText::from("def x = 1;\ndef y = 2;");
        let source: &str = text.into();
        for (byte, _) in source.char_indices() {
            let at = pos_of_byte(text, ByteOffset::from(byte))
                .expect("ASCII offsets are character starts");
            assert_eq!(
                ByteOffset::from(byte),
                byte_of_pos(text, at),
                "byte {byte} round-trips"
            );
        }
    }

    #[test]
    fn positions_round_trip_on_multibyte_text()
    {
        // Two-, three- and four-byte characters on either side of a newline.
        let text = SourceText::from("é€\n𝄞z𝄞");
        let source: &str = text.into();
        for (byte, character) in source.char_indices() {
            let at =
                pos_of_byte(text, ByteOffset::from(byte)).expect("a character start is projected");
            assert_eq!(
                ByteOffset::from(byte),
                byte_of_pos(text, at),
                "byte {byte} round-trips"
            );
            for interior in 1 .. character.len_utf8() {
                let inside = ByteOffset::from(byte.saturating_add(interior));
                assert_eq!(
                    Err(PosOfByteError { byte: inside }),
                    pos_of_byte(text, inside),
                    "byte {inside} is inside a character"
                );
            }
        }
        assert_eq!(
            Ok(pos(At(1, 3))),
            pos_of_byte(text, ByteOffset::from(source.len())),
            "the end follows the last of three characters on the second row"
        );
    }

    #[test]
    fn positions_count_characters_not_bytes()
    {
        let text = SourceText::from("é×é\nz");
        // Bytes: é=2, ×=2, é=2, \n=1, z=1.
        assert_eq!(
            Ok(pos(At(0, 0))),
            pos_of_byte(text, ByteOffset::from(0_usize)),
            "the first character opens the first row"
        );
        assert_eq!(
            Ok(pos(At(0, 1))),
            pos_of_byte(text, ByteOffset::from(2_usize)),
            "the second character is the second column"
        );
        assert_eq!(
            Ok(pos(At(0, 2))),
            pos_of_byte(text, ByteOffset::from(4_usize)),
            "the third character is the third column"
        );
        assert_eq!(
            Ok(pos(At(0, 3))),
            pos_of_byte(text, ByteOffset::from(6_usize)),
            "the newline is the last column of the row it ends"
        );
        assert_eq!(
            Ok(pos(At(1, 0))),
            pos_of_byte(text, ByteOffset::from(7_usize)),
            "the character after the newline opens the next row"
        );
        assert_eq!(
            ByteOffset::from(7_usize),
            byte_of_pos(text, pos(At(1, 0))),
            "the next row's first column is its first byte"
        );
    }

    #[test]
    fn pos_of_byte_rejects_interior_multibyte_offsets()
    {
        let refused = pos_of_byte(SourceText::from("é"), ByteOffset::from(1_usize))
            .expect_err("byte 1 is inside the two-byte é");
        assert_eq!(
            ByteOffset::from(1_usize),
            refused.byte,
            "the refusal carries the offset"
        );
    }

    #[test]
    fn out_of_range_positions_clamp()
    {
        let text = SourceText::from("ab\ncd");
        assert_eq!(
            Ok(pos(At(1, 2))),
            pos_of_byte(text, ByteOffset::from(999_usize)),
            "an offset past the end is the final position"
        );
        assert_eq!(
            ByteOffset::from(2_usize),
            byte_of_pos(text, pos(At(0, 99))),
            "a column past a row's end is that row's newline"
        );
        assert_eq!(
            ByteOffset::from(5_usize),
            byte_of_pos(text, pos(At(1, 99))),
            "a column past the last row's end is the end of the text"
        );
        assert_eq!(
            ByteOffset::from(5_usize),
            byte_of_pos(text, pos(At(9, 0))),
            "a row past the last is the end of the text"
        );
    }

    #[test]
    fn the_empty_source_has_one_position()
    {
        let text = SourceText::from("");
        assert_eq!(
            Ok(pos(At(0, 0))),
            pos_of_byte(text, ByteOffset::from(0_usize)),
            "offset 0 is the origin"
        );
        assert_eq!(
            Ok(pos(At(0, 0))),
            pos_of_byte(text, ByteOffset::from(3_usize)),
            "any offset clamps to the origin"
        );
        assert_eq!(
            ByteOffset::from(0_usize),
            byte_of_pos(text, pos(At(0, 0))),
            "the origin is offset 0"
        );
        assert_eq!(
            ByteOffset::from(0_usize),
            byte_of_pos(text, pos(At(2, 4))),
            "any position clamps to offset 0"
        );
    }

    #[test]
    fn the_end_of_the_source_is_a_position()
    {
        let text = SourceText::from("ab\ncd");
        assert_eq!(
            Ok(pos(At(1, 2))),
            pos_of_byte(text, ByteOffset::from(5_usize)),
            "the end follows the last character"
        );
        assert_eq!(
            ByteOffset::from(5_usize),
            byte_of_pos(text, pos(At(1, 2))),
            "the final position is the end"
        );

        let trailing = SourceText::from("ab\n");
        assert_eq!(
            Ok(pos(At(1, 0))),
            pos_of_byte(trailing, ByteOffset::from(3_usize)),
            "after a trailing newline the end opens an empty row"
        );
        assert_eq!(
            ByteOffset::from(3_usize),
            byte_of_pos(trailing, pos(At(1, 0))),
            "the empty last row is the end"
        );
    }

    #[test]
    fn adjacent_terminators_preserve_empty_rows_and_crlf_clamping()
    {
        let index = LineIndex::new(SourceText::from("\r\n\r\né\r\n\r"));
        for (row, bytes) in [
            Bytes(0, 0),
            Bytes(2, 2),
            Bytes(4, 6),
            Bytes(8, 8),
            Bytes(9, 9),
        ]
        .into_iter()
        .enumerate()
        {
            assert_eq!(range(bytes), index.row_bytes(PositionRow::from(row)));
        }
        for (byte, at, normalized) in [
            (1_usize, At(0, 1), 0_usize),
            (3, At(1, 1), 2),
            (7, At(2, 2), 6),
        ] {
            let at = utf16(at);
            assert_eq!(Ok(at), index.utf16_pos_of_byte(ByteOffset::from(byte)));
            assert_eq!(ByteOffset::from(normalized), index.byte_of_utf16_pos(at));
        }
        assert_eq!(
            Ok(utf16(At(4, 0))),
            index.utf16_pos_of_byte(ByteOffset::from(usize::MAX))
        );
        assert_eq!(
            range(Bytes(9, 9)),
            index.row_bytes(PositionRow::from(usize::MAX))
        );
        assert_eq!(
            ByteOffset::from(6_usize),
            index.byte_of_utf16_pos(utf16(At(2, usize::MAX)))
        );
    }

    #[test]
    fn range_and_position_errors_preserve_numeric_parameters()
    {
        let inverted = InvertedRange {
            start: ByteOffset::from(5_usize),
            end: ByteOffset::from(4_usize),
        }
        .to_string();
        assert!(
            inverted
                .split(|ch: char| !ch.is_ascii_digit())
                .filter(|part| !part.is_empty())
                .eq(["5", "4"])
        );
        let offset = usize::MAX.to_string();
        let interior = PosOfByteError {
            byte: ByteOffset::from(usize::MAX),
        }
        .to_string();
        assert!(
            interior
                .split(|ch: char| !ch.is_ascii_digit())
                .filter(|part| !part.is_empty())
                .eq([offset.as_str()])
        );
    }

    #[test]
    fn byte_offsets_preserve_formatter_options()
    {
        let offset = ByteOffset::from(5_usize);
        assert_eq!(
            "   5|+0005|***5****",
            alloc::format!("{offset:>4}|{offset:+05}|{offset:*^8}")
        );
    }
}
