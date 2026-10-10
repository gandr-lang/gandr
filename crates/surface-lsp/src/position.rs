//! Positions as the protocol carries them: a zero-based line and a zero-based
//! character counted in UTF-16 code units, read through the renderer seam's
//! [`LineIndex`] and never re-derived here.
//!
//! The wire counts in 32-bit unsigned integers; the index counts in `usize`.
//! A wire count past the platform's `usize` saturates, which the index then
//! clamps as it clamps any position past the text, and an index count past
//! `u32` saturates on the way out.

use anodized::spec;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::PosOfByteError;
use gandr_surface_render_remote::PositionRow;
use gandr_surface_render_remote::Utf16Column;
use gandr_surface_render_remote::Utf16Pos;
use serde::Deserialize;
use serde::Serialize;

/// A zero-based line, as the wire counts it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Line(u32);

impl From<u32> for Line
{
    /// Read the count as a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(line: u32) -> Self
    {
        Self(line)
    }
}

/// A zero-based character within a line, counted in UTF-16 code units, as
/// the wire counts it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Character(u32);

impl From<u32> for Character
{
    /// Read the count as a character.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(character: u32) -> Self
    {
        Self(character)
    }
}

/// A position in a document, as the wire carries it.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct Position
{
    /// The zero-based line.
    pub line: Line,
    /// The zero-based character within the line, in UTF-16 code units.
    pub character: Character,
}

impl Position
{
    /// The position of `byte` in the text `index` was built from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the line and UTF-16 column the index projects `byte` to; an
    ///   offset at or past the end of the text is the position after its last
    ///   character.
    /// - provides: the position every range the server sends is made of.
    /// - fails: [`PosOfByteError`] when `byte` lies inside a character.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PosOfByteError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a character beyond the basic plane before the offset,
    ///   an offset inside it, and an offset past the end, each asserted at its
    ///   exact position or refusal.
    /// - witness: `position::tests::utf16_counts_an_astral_character_as_two_units`
    /// - witness: `position::tests::a_line_past_the_end_clamps`
    #[spec(ensures: |ret| match index.utf16_pos_of_byte(byte) {
        Ok(expected) => ret.as_ref().is_ok_and(|actual|
            actual.line.0 == u32::try_from(usize::from(expected.row)).unwrap_or(u32::MAX)
                && actual.character.0 == u32::try_from(usize::from(expected.col)).unwrap_or(u32::MAX)),
        Err(expected) => ret.as_ref().is_err_and(|actual| actual == &expected),
    })]
    #[inline]
    pub fn of_byte(
        index: &LineIndex<'_>,
        byte: ByteOffset,
    ) -> Result<Self, PosOfByteError>
    {
        let pos = index.utf16_pos_of_byte(byte)?;
        Ok(Self {
            line: Line(u32::try_from(usize::from(pos.row)).unwrap_or(u32::MAX)),
            character: Character(u32::try_from(usize::from(pos.col)).unwrap_or(u32::MAX)),
        })
    }

    /// The byte offset this position addresses in the text `index` was built
    /// from.
    ///
    /// # Specification
    /// - requires: nothing; a position past the text is admissible input.
    /// - ensures: the offset the index resolves the position to: a character
    ///   between the two units of a character beyond the basic plane resolves
    ///   to that character's first byte, a character past its line's end to the
    ///   line's terminator, a line past the last to the end of the text.
    /// - provides: the offset a range the client sends is read at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a character after one beyond the basic plane, one
    ///   between its two units, and a line past the last, each asserted at its
    ///   exact offset.
    /// - witness: `position::tests::utf16_counts_an_astral_character_as_two_units`
    /// - witness: `position::tests::a_line_past_the_end_clamps`
    #[spec(ensures: |ret| ret == index.byte_of_utf16_pos(Utf16Pos {
        row: PositionRow::from(usize::try_from(self.line.0).unwrap_or(usize::MAX)),
        col: Utf16Column::from(usize::try_from(self.character.0).unwrap_or(usize::MAX)),
    }))]
    #[inline]
    #[must_use]
    pub fn byte(
        self,
        index: &LineIndex<'_>,
    ) -> ByteOffset
    {
        index.byte_of_utf16_pos(Utf16Pos {
            row: PositionRow::from(usize::try_from(self.line.0).unwrap_or(usize::MAX)),
            col: Utf16Column::from(usize::try_from(self.character.0).unwrap_or(usize::MAX)),
        })
    }
}

/// A range in a document, half-open, as the wire carries it.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
pub struct Range
{
    /// The position of the first character covered.
    pub start: Position,
    /// The position one past the last character covered.
    pub end: Position,
}

impl Range
{
    /// The range covering the bytes from `start` up to `end` in the text
    /// `index` was built from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each end is [`Position::of_byte`] of its offset.
    /// - provides: the range a diagnostic and its related locations carry.
    /// - fails: [`PosOfByteError`] when either offset lies inside a character.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PosOfByteError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — corpus reports agree with their renderer ranges. L3 —
    ///   an astral character, every protocol line terminator, reversed and
    ///   empty ranges, and invalid endpoints distinguish swapped ends, UTF-8
    ///   byte counts and lost or reordered projection errors.
    /// - witness: `session::session::every_corpus_report_is_published_where_the_walk_renders_it`
    /// - witness: `position::tests::ranges_preserve_endpoint_order_and_projection_failures`
    #[spec(ensures: |ret| ret.as_ref().map(|range| (range.start, range.end))
        == Position::of_byte(index, start)
            .and_then(|first| Position::of_byte(index, end).map(|last| (first, last)))
            .as_ref().copied())]
    #[inline]
    pub fn of_bytes(
        index: &LineIndex<'_>,
        start: ByteOffset,
        end: ByteOffset,
    ) -> Result<Self, PosOfByteError>
    {
        let start = Position::of_byte(index, start)?;
        let end = Position::of_byte(index, end)?;
        Ok(Self { start, end })
    }
}

#[cfg(test)]
mod tests
{
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_render_remote::PosOfByteError;
    use gandr_surface_render_remote::SourceText;

    use super::Character;
    use super::Line;
    use super::Position;

    /// The wire position a line and a character spell.
    struct At(u32, u32);

    /// The position an [`At`] pair spells.
    ///
    /// # Specification
    /// trivial.
    fn at(At(line, character): At) -> Position
    {
        Position {
            line: Line::from(line),
            character: Character::from(character),
        }
    }

    #[test]
    fn utf16_counts_an_astral_character_as_two_units()
    {
        // `𝄞` is four bytes and two UTF-16 units: `b` sits at byte 5 and at
        // character 3.
        let index = LineIndex::new(SourceText::from("a𝄞b"));
        assert_eq!(
            Position::of_byte(&index, ByteOffset::from(5_usize)),
            Ok(at(At(0, 3))),
            "the character after an astral one counts it as two units"
        );
        assert_eq!(
            at(At(0, 3)).byte(&index),
            ByteOffset::from(5_usize),
            "and reads back to its byte"
        );
        assert_eq!(
            at(At(0, 2)).byte(&index),
            ByteOffset::from(1_usize),
            "a character between the two units resolves to the astral character's first byte"
        );
        assert_eq!(
            Position::of_byte(&index, ByteOffset::from(3_usize)),
            Err(PosOfByteError {
                byte: ByteOffset::from(3_usize),
            }),
            "a byte inside the astral character has no position"
        );
    }

    #[test]
    fn a_line_past_the_end_clamps()
    {
        let index = LineIndex::new(SourceText::from("ab\ncd"));
        assert_eq!(
            at(At(9, 0)).byte(&index),
            ByteOffset::from(5_usize),
            "a line past the last is the end of the text"
        );
        assert_eq!(
            at(At(u32::MAX, u32::MAX)).byte(&index),
            ByteOffset::from(5_usize),
            "the widest wire position is the end of the text"
        );
        assert_eq!(
            at(At(0, 9)).byte(&index),
            ByteOffset::from(2_usize),
            "a character past its line's end is the line's terminator"
        );
        assert_eq!(
            Position::of_byte(&index, ByteOffset::from(99_usize)),
            Ok(at(At(1, 2))),
            "an offset past the end is the position after the last character"
        );
    }
    #[test]
    fn ranges_preserve_endpoint_order_and_projection_failures()
    {
        let index = LineIndex::new(SourceText::from("a𝄞\r\nb\rc\n"));
        for (start, end, first, last) in [
            (0_usize, 5_usize, At(0, 0), At(0, 3)),
            (7, 8, At(1, 0), At(1, 1)),
            (9, 7, At(2, 0), At(1, 0)),
            (5, 5, At(0, 3), At(0, 3)),
            (11, usize::MAX, At(3, 0), At(3, 0)),
        ] {
            assert_eq!(
                super::Range::of_bytes(&index, ByteOffset::from(start), ByteOffset::from(end)),
                Ok(super::Range {
                    start: at(first),
                    end: at(last)
                }),
            );
        }
        for (start, end, invalid) in [(2_usize, 4_usize, 2_usize), (0, 3, 3), (4, 2, 4)] {
            assert_eq!(
                super::Range::of_bytes(&index, ByteOffset::from(start), ByteOffset::from(end)),
                Err(PosOfByteError {
                    byte: ByteOffset::from(invalid)
                }),
            );
        }
    }
}
