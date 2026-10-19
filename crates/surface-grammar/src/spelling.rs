//! The spellings of a construct: an ASCII one always, a Unicode one besides.
//!
//! Every construct the surface writes has an ASCII spelling, and may have a
//! Unicode one. A construct with both is a glyph tile of the grammar, and
//! [`SPELLED`] pairs it with its ASCII spelling: the one table the labeler
//! reads to mold an ASCII token as the glyph's tile, the printer reads to
//! write the spelling a reader asks for, and the syntax ledger reads to show
//! both. The tile, not either spelling, is the construct's identity: an ASCII
//! token molds the glyph's tile, so the tree, the lowering and every reader
//! after them never see which was written.
//!
//! Most pairs are one token for another (`≃` and `<~>`). One differs in shape:
//! the isomorphism `A ≅ B` is written in ASCII as the call `Iso(A, B)`, which
//! the lowering reads as the same former; that pair is [`Ascii::Head`], and
//! the labeler has nothing to alias for it.
//!
//! The identifier prime `′` (`x′`) is no construct: it continues a word, and
//! an identifier holding it has no ASCII spelling. A printer asked for ASCII
//! refuses such a name rather than spelling another.
//!
//! The alternative, a spelling per token chosen at the lexer, would leave the
//! printer and the ledger a second list to keep in step; a table keyed by the
//! tile is read by all three. Reversal: a construct whose ASCII and Unicode
//! spellings mold different trees beyond a head call would need the table to
//! name both rules.

use anodized::spec;

use crate::model::LabelText;
use crate::model::TileLabel;

/// Which of a construct's spellings a printer writes.
///
/// # Specification
/// - executable: none — a choice between two spellings; [`Spelled::written`]
///   carries the relation to the table.
///
/// # Adequacy
/// - hypothesis: L3 — each glyph tile written under both choices.
/// - witness: `tests::spelling::each_glyph_is_written_in_the_spelling_asked`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Spelling
{
    /// The glyph where the construct has one: `≃`, `≅`, `⇝`, `∷`, `ω`.
    #[default]
    Unicode,
    /// The ASCII spelling every construct has.
    Ascii,
}

/// How a glyph tile is written in ASCII.
///
/// # Specification
/// - executable: none — a tag over the ASCII text; [`SPELLED`] holds the
///   instances.
///
/// # Adequacy
/// - hypothesis: L3 — the table's token and head entries read back.
/// - witness: `tests::spelling::each_glyph_is_written_in_the_spelling_asked`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Ascii
{
    /// A token standing where the glyph stands, molding the glyph's tile.
    Token(LabelText<'static>),
    /// A call of this head over the glyph's operands, read by the lowering as
    /// the glyph's former: `Iso(A, B)` for `A ≅ B`.
    Head(LabelText<'static>),
}

/// A glyph tile and its ASCII spelling.
///
/// # Specification
/// - executable: none — a pair of texts; [`SPELLED`] holds the instances.
///
/// # Adequacy
/// - hypothesis: L3 — every glyph tile of the built-in grammar has one.
/// - witness: `tests::spelling::every_glyph_tile_of_the_grammar_has_an_ascii_spelling`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Spelled
{
    /// The tile, spelled by its glyph.
    pub tile: TileLabel,
    /// Its ASCII spelling.
    pub ascii: Ascii,
}

impl Spelled
{
    /// The text a construct is written with under `spelling`: the glyph, the
    /// ASCII token, or the ASCII head its call is written with.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tile's glyph under [`Spelling::Unicode`], the ASCII
    ///   spelling's text under [`Spelling::Ascii`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the receiver is a table entry, and the relation is
    ///   checked once over the table where it is built: the witness writes each
    ///   entry under both spellings.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each entry under both spellings; swapping the arms
    ///   writes the other text.
    /// - witness: `tests::spelling::each_glyph_is_written_in_the_spelling_asked`
    #[inline]
    #[must_use]
    pub const fn written(
        &self,
        spelling: Spelling,
    ) -> LabelText<'static>
    {
        match (spelling, self.ascii) {
            (Spelling::Unicode, _) => LabelText(self.tile.0),
            (Spelling::Ascii, Ascii::Token(text) | Ascii::Head(text)) => text,
        }
    }
}

/// The equivalence of types, `A ≃ B` or `A <~> B`.
pub const EQUIVALENCE: Spelled = Spelled {
    tile: TileLabel("≃"),
    ascii: Ascii::Token(LabelText("<~>")),
};

/// The flow between types, `A ⇝ B` or `A ~~> B`.
pub const FLOW: Spelled = Spelled {
    tile: TileLabel("⇝"),
    ascii: Ascii::Token(LabelText("~~>")),
};

/// The isomorphism of types, `A ≅ B` or the call `Iso(A, B)`.
pub const ISOMORPHISM: Spelled = Spelled {
    tile: TileLabel("≅"),
    ascii: Ascii::Head(LabelText("Iso")),
};

/// A word's letter before the rest of the word, `g ∷ p` or `g :: p`.
pub const CONS: Spelled = Spelled {
    tile: TileLabel("∷"),
    ascii: Ascii::Token(LabelText("::")),
};

/// The unrestricted grade, `ω` or `inf`.
pub const UNRESTRICTED: Spelled = Spelled {
    tile: TileLabel("ω"),
    ascii: Ascii::Token(LabelText("inf")),
};

/// Every glyph tile of the surface with its ASCII spelling.
pub const SPELLED: &[Spelled] = &[EQUIVALENCE, FLOW, ISOMORPHISM, CONS, UNRESTRICTED];

/// The prime an identifier may carry, `x′`: Unicode with no ASCII spelling.
pub const PRIME: LabelText<'static> = LabelText("′");

/// The glyph tile and its ASCII spelling, for `tile`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the [`SPELLED`] entry whose tile is `tile`, if any.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every entry is found by its tile, and an ASCII tile is
///   found by none.
/// - witness: `tests::spelling::each_glyph_is_written_in_the_spelling_asked`
#[spec(ensures: |ret| ret.is_none_or(|entry| entry.tile == tile && SPELLED.contains(&entry)))]
#[inline]
#[must_use]
pub fn spelled(tile: TileLabel) -> Option<Spelled>
{
    SPELLED.iter().copied().find(|entry| entry.tile == tile)
}

/// The glyph tile an ASCII token stands for, for the labeler to offer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the tile of the [`SPELLED`] entry whose ASCII spelling is the
///   token `text`; nothing for a head, whose call the lowering reads, or for
///   any other text.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each token entry's text resolves to its tile, a head
///   resolves to nothing, and a glyph resolves to nothing.
/// - witness: `tests::spelling::an_ascii_token_stands_for_its_glyph_and_a_head_for_none`
#[spec(ensures: |ret| ret.is_none_or(|tile| SPELLED.iter().any(|entry| entry.tile == tile && matches!(entry.ascii, Ascii::Token(ascii) if ascii.0 == text.0))))]
#[inline]
#[must_use]
pub fn aliased(text: LabelText<'_>) -> Option<TileLabel>
{
    SPELLED.iter().find_map(|entry| match entry.ascii {
        Ascii::Token(ascii) if ascii.0 == text.0 => Some(entry.tile),
        Ascii::Token(_) | Ascii::Head(_) => None,
    })
}
