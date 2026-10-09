//! The node vocabulary of a molded tree: [`NodeLabel`], its pinned digest
//! tags, which labels draw text from the source, and which ones a parent's
//! digest folds.
//!
//! # The node carries its kind
//!
//! A tree whose nodes carry a generic label and whose form is recovered by the
//! reader forces every consumer to re-derive the form from the children it
//! happens to have. A molded tree avoids that without a closed list of forms:
//! a [`NodeLabel::Tile`] and a [`NodeLabel::Meld`] carry a [`MoldId`], and the
//! grammar that numbered the mold resolves it, as a total function over its
//! mold table, to the rule it belongs to and that rule's named kind. A
//! consumer dispatching on forms reads the kind off the label and has nothing
//! to adapt; the forms the grammar admits are the grammar's, not this crate's.
//!
//! # Every token is a node
//!
//! The parser keeps every tile it molded, every piece of grout it inserted,
//! and every run of layout, so the leaves of a tree, read in source order,
//! reproduce the source byte for byte. Layout is a node for that reason alone:
//! a parent's digest does not fold it, so reformatting a declaration leaves its
//! identity unchanged.

use crate::mold::ClosingClass;
use crate::mold::GroutShape;
use crate::mold::GroutSort;
use crate::mold::MoldId;

/// The pinned tag a node label contributes to a content digest.
///
/// The tag is written into the digest preimage instead of the variant's
/// discriminant so that reordering the enum — an ordinary readability edit —
/// cannot silently change every digest a stored checkpoint was keyed by.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LabelTag(u8);

impl From<LabelTag> for u8
{
    /// Read the tag back out as the byte written into a digest preimage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: LabelTag) -> Self
    {
        tag.0
    }
}

/// Whether a node's own source text contributes to its content digest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CarriesText(bool);

impl From<CarriesText> for bool
{
    /// Read the flag back out as a `bool`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(carries: CarriesText) -> Self
    {
        carries.0
    }
}

/// Whether a parent's content digest folds a node's digest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Significance(bool);

impl From<Significance> for bool
{
    /// Read the flag back out as a `bool`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(significance: Significance) -> Self
    {
        significance.0
    }
}

/// What one node of a molded tree is.
///
/// The vocabulary is the parser's material, closed: the tree records what was
/// molded, what was inserted, and what was layout. Which form a molded node
/// realises is the grammar's answer for its [`MoldId`], read under the
/// [`GrammarFingerprint`](crate::GrammarFingerprint) the tree records.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeLabel
{
    /// The root: a source's top-level forms and its layout, in source order.
    Wald,
    /// A completed form, named by the mold of the tile that opened it — the
    /// form's first tile, or the operator of a one-tile operator form.
    Meld(MoldId),
    /// A tile the source wrote, molded.
    Tile(MoldId),
    /// Grout: material standing where the source wrote no term of `sort`, or
    /// over a token the source wrote and no grammar label molds, whose bytes
    /// it then covers.
    Grout
    {
        /// The sort the grout stands in for.
        sort: GroutSort,
        /// Which sides the grout faces.
        shape: GroutShape,
    },
    /// A minted close: postfix grout standing in for a closer of `class` the
    /// source never wrote.
    ///
    /// Distinct from [`NodeLabel::Grout`] so a consumer can pair it against a
    /// closer of the same family written later; a missing closer whose form
    /// has no single family is ordinary postfix grout and pairs with nothing.
    GhostClose
    {
        /// The sort of the form the close completes.
        sort: GroutSort,
        /// The family of the closer it stands in for.
        class: ClosingClass,
    },
    /// Layout: whitespace, a comment, or a shebang line.
    Space,
}

impl NodeLabel
{
    /// The tag this label contributes to a content digest.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: each variant yields its own tag, distinct from every other
    ///   variant's and independent of the payload, and the value is fixed
    ///   rather than derived from declaration order.
    /// - provides: the variant half of a node's digest preimage; the payload
    ///   half is written beside it by the digest.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively against a pinned tag table, with pairwise distinctness
    ///   asserted over the same enumeration; a swapped pair of rows breaks two
    ///   pinned values, and a duplicated row breaks distinctness.
    /// - witness: `label::tests::every_digest_tag_is_pinned`
    /// - witness: `label::tests::the_digest_tags_are_pairwise_distinct`
    #[inline]
    #[must_use]
    pub const fn tag(self) -> LabelTag
    {
        LabelTag(match self {
            | Self::Wald => 0x01_u8,
            | Self::Meld(_) => 0x02_u8,
            | Self::Tile(_) => 0x03_u8,
            | Self::Grout { .. } => 0x04_u8,
            | Self::GhostClose { .. } => 0x05_u8,
            | Self::Space => 0x06_u8,
        })
    }

    /// Whether a node with this label folds its own source text into its
    /// digest.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: every leaf label answers affirmatively — a tile, grout, a
    ///   minted close and layout — and the two interior labels, a form and the
    ///   root, answer negatively: a leaf's text is what the source wrote there
    ///   (empty for inserted grout and a minted close, the token's bytes for
    ///   grout over an unmolded token), and an interior node's text is its
    ///   children's.
    /// - provides: the text half of a node's digest preimage.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each variant's exact answer asserted, so promoting
    ///   or demoting any single variant breaks one assertion.
    /// - witness: `label::tests::only_leaves_carry_text`
    #[inline]
    #[must_use]
    pub const fn carries_text(self) -> CarriesText
    {
        CarriesText(!matches!(self, Self::Wald | Self::Meld(_)))
    }

    /// Whether a parent's digest folds a node with this label.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: every variant but [`NodeLabel::Space`] answers affirmatively.
    /// - provides: the filter a builder applies to a node's children before
    ///   folding their digests, so layout never reaches an ancestor's identity.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each variant's exact answer asserted.
    /// - witness: `label::tests::only_layout_is_insignificant`
    #[inline]
    #[must_use]
    pub const fn significance(self) -> Significance
    {
        Significance(!matches!(self, Self::Space))
    }
}

#[cfg(test)]
mod tests
{
    use super::CarriesText;
    use super::LabelTag;
    use super::NodeLabel;
    use super::Significance;
    use crate::mold::ClosingClass;
    use crate::mold::GroutShape;
    use crate::mold::GroutSort;
    use crate::mold::MoldId;

    /// One label of every variant, in vocabulary order.
    ///
    /// # Specification
    /// trivial.
    fn every_variant() -> [NodeLabel; 6_usize]
    {
        [
            NodeLabel::Wald,
            NodeLabel::Meld(MoldId::from(3_u32)),
            NodeLabel::Tile(MoldId::from(3_u32)),
            NodeLabel::Grout {
                sort: GroutSort::from(1_u16),
                shape: GroutShape::Convex,
            },
            NodeLabel::GhostClose {
                sort: GroutSort::from(1_u16),
                class: ClosingClass::Brace,
            },
            NodeLabel::Space,
        ]
    }

    #[test]
    fn every_digest_tag_is_pinned()
    {
        let expected = [0x01_u8, 0x02_u8, 0x03_u8, 0x04_u8, 0x05_u8, 0x06_u8];
        for (label, tag) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                label.tag(),
                LabelTag(tag),
                "the digest tag table is pinned row by row"
            );
        }
        assert_eq!(
            NodeLabel::Tile(MoldId::from(7_u32)).tag(),
            NodeLabel::Tile(MoldId::from(3_u32)).tag(),
            "the tag names the variant, never its payload"
        );
    }

    #[test]
    fn the_digest_tags_are_pairwise_distinct()
    {
        for (first, left) in every_variant().into_iter().enumerate() {
            for (second, right) in every_variant().into_iter().enumerate() {
                if first == second {
                    continue;
                }
                assert_ne!(
                    left.tag(),
                    right.tag(),
                    "two variants sharing a tag would share a digest preimage"
                );
            }
        }
    }

    #[test]
    fn only_leaves_carry_text()
    {
        let expected = [false, false, true, true, true, true];
        for (label, carries) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                label.carries_text(),
                CarriesText(carries),
                "exactly the leaf labels fold their own source text"
            );
        }
    }

    #[test]
    fn only_layout_is_insignificant()
    {
        let expected = [true, true, true, true, true, false];
        for (label, significant) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                label.significance(),
                Significance(significant),
                "every label but layout reaches its parent's digest"
            );
        }
    }
}
