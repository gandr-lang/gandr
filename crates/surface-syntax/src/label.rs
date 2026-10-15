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
//!
//! # Molded labels
//!
//! A node carries its kind, and the kind is a mold. A `NodeLabel::Tile` is a
//! written tile and a `NodeLabel::Meld` a completed form, each named by a
//! `MoldId` — a form by the mold of the tile that opened it, the operator of a
//! one-tile operator form, or its first tile otherwise. The grammar that
//! numbered the molds resolves an id, as a total function over its mold table,
//! to the rule the mold belongs to and the rule's named kind, so a lowering
//! dispatches on kinds and has nothing to adapt. The forms the language admits
//! are the grammar's to state, once; the tree names no form of its own.
//!
//! The alternative was a closed `NodeKind` enum in this crate, one variant per
//! surface form, which a parser fills by mapping each completed form to a
//! variant. It names forms without a grammar in hand, but restates the
//! grammar's forms in a second place and needs a read adapter from molds to
//! variants that grows with the grammar; a parser-owned second tree beside this
//! one was the other alternative, and it would give every consumer two
//! identities to reconcile. Reversal: if a consumer needs a form vocabulary the
//! grammar's named kinds do not supply, a closed kind returns as that read
//! adapter over the molded tree, and its cost — thousands of lines for this
//! grammar's surface — is what this choice avoids.
//!
//! # Layout in the tree
//!
//! Every token the source wrote is a node, layout included, so the leaves read
//! in source order reproduce the source byte for byte; grout the parser
//! inserted covers no bytes, and grout standing over a token no grammar label
//! molds covers exactly that token's. Every leaf label carries its own text
//! into its form's digest — a tile, grout, a minted close and layout — so two
//! unmolded tokens of different spellings are two identities; a form, the root
//! and documentation carry only their children's. A form's digest reads a node
//! only when the node and every node above it in the form are significant.
//! `NodeLabel::Space` is not, so reformatting a declaration leaves its form's
//! digest and the tree's unchanged while the layout stays in the tree for a
//! re-renderer. `NodeLabel::Doc` is not either: it groups a run of `///` lines
//! or one `doc("…")` attribute entry under the form it documents, so editing
//! documentation, or moving it between the two spellings, leaves that form's
//! identity alone. A missing closer is a `NodeLabel::GhostClose` naming its
//! family, so a consumer can pair it against a closer written later; a missing
//! closer of no single family is postfix grout.

use anodized::spec;

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
/// molded, what was inserted, what was layout and what documents a form. Which
/// form a molded node realises is the grammar's answer for its [`MoldId`], read
/// under the [`GrammarFingerprint`](crate::GrammarFingerprint) the tree
/// records.
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
    /// Documentation: a run of `///` lines or one `doc("…")` attribute entry,
    /// grouped under the form it documents.
    ///
    /// An interior, like a form, so the material it groups stays in the tree;
    /// insignificant, like layout, so editing documentation leaves the
    /// documented form's identity and every ancestor's unchanged.
    Doc,
}

impl NodeLabel
{
    /// Compare represented values during constant evaluation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn const_eq(
        self,
        other: Self,
    ) -> crate::ConstEquality
    {
        if match (self, other) {
            (Self::Wald, Self::Wald) | (Self::Space, Self::Space) | (Self::Doc, Self::Doc) => true,
            (Self::Meld(a), Self::Meld(b)) | (Self::Tile(a), Self::Tile(b)) => {
                matches!(a.const_eq(b), crate::ConstEquality::Equal)
            },
            (Self::Grout { sort: a, shape: sa }, Self::Grout { sort: b, shape: sb }) => {
                matches!(a.const_eq(b), crate::ConstEquality::Equal)
                    && matches!(
                        (sa, sb),
                        (GroutShape::Convex, GroutShape::Convex)
                            | (GroutShape::Prefix, GroutShape::Prefix)
                            | (GroutShape::Postfix, GroutShape::Postfix)
                            | (GroutShape::Infix, GroutShape::Infix)
                    )
            },
            (Self::GhostClose { sort: a, class: ca }, Self::GhostClose { sort: b, class: cb }) => {
                matches!(a.const_eq(b), crate::ConstEquality::Equal)
                    && matches!(
                        (ca, cb),
                        (ClosingClass::Paren, ClosingClass::Paren)
                            | (ClosingClass::Bracket, ClosingClass::Bracket)
                            | (ClosingClass::Brace, ClosingClass::Brace)
                    )
            },
            _ => false,
        } {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }

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
    #[spec(ensures: |ret| ret.0 == match self {
        Self::Wald => 1_u8, Self::Meld(_) => 2_u8, Self::Tile(_) => 3_u8,
        Self::Grout { .. } => 4_u8, Self::GhostClose { .. } => 5_u8, Self::Space => 6_u8,
        Self::Doc => 7_u8,
    })]
    #[inline]
    #[must_use]
    pub const fn tag(self) -> LabelTag
    {
        LabelTag(match self {
            Self::Wald => 0x01_u8,
            Self::Meld(_) => 0x02_u8,
            Self::Tile(_) => 0x03_u8,
            Self::Grout { .. } => 0x04_u8,
            Self::GhostClose { .. } => 0x05_u8,
            Self::Space => 0x06_u8,
            Self::Doc => 0x07_u8,
        })
    }

    /// Whether a node with this label folds its own source text into its
    /// digest.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: every leaf label answers affirmatively — a tile, grout, a
    ///   minted close and layout — and the three interior labels, a form, the
    ///   root and documentation, answer negatively: a leaf's text is what the
    ///   source wrote there (empty for inserted grout and a minted close, the
    ///   token's bytes for grout over an unmolded token), and an interior
    ///   node's text is its children's.
    /// - provides: the text half of a node's digest preimage.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each variant's exact answer asserted, so promoting
    ///   or demoting any single variant breaks one assertion.
    /// - witness: `label::tests::only_leaves_carry_text`
    #[spec(ensures: |ret| ret.0 == matches!(self, Self::Tile(_) | Self::Grout { .. } | Self::GhostClose { .. } | Self::Space))]
    #[inline]
    #[must_use]
    pub const fn carries_text(self) -> CarriesText
    {
        CarriesText(!matches!(self, Self::Wald | Self::Meld(_) | Self::Doc))
    }

    /// Whether a parent's digest folds a node with this label.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: every variant but [`NodeLabel::Space`] and [`NodeLabel::Doc`]
    ///   answers affirmatively.
    /// - provides: the filter a builder applies to a node's children before
    ///   folding their digests, so neither layout nor documentation reaches an
    ///   ancestor's identity.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each variant's exact answer asserted; changing the
    ///   boundary between content and the rest flips an observed answer.
    /// - witness: `label::tests::only_layout_and_documentation_are_insignificant`
    #[spec(ensures: |ret| ret.0 != matches!(self, Self::Space | Self::Doc))]
    #[inline]
    #[must_use]
    pub const fn significance(self) -> Significance
    {
        Significance(!matches!(self, Self::Space | Self::Doc))
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
    fn every_variant() -> [NodeLabel; 7_usize]
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
            NodeLabel::Doc,
        ]
    }

    #[test]
    fn every_digest_tag_is_pinned()
    {
        let expected = [
            0x01_u8, 0x02_u8, 0x03_u8, 0x04_u8, 0x05_u8, 0x06_u8, 0x07_u8,
        ];
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
        let expected = [false, false, true, true, true, true, false];
        for (label, carries) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                label.carries_text(),
                CarriesText(carries),
                "exactly the leaf labels fold their own source text"
            );
        }
    }

    #[test]
    fn only_layout_and_documentation_are_insignificant()
    {
        let expected = [true, true, true, true, true, false, false];
        for (label, significant) in every_variant().into_iter().zip(expected) {
            assert_eq!(
                label.significance(),
                Significance(significant),
                "every label but layout and documentation reaches its parent's digest"
            );
        }
    }
}
