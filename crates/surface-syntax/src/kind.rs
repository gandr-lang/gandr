//! The closed node vocabulary: [`NodeKind`], its pinned digest tags, and which
//! kinds draw text from the source.
//!
//! # The node carries its kind
//!
//! A form-name-free tree — one whose nodes carry a generic label and whose
//! shape is recovered by the reader — forces every consumer to re-derive the
//! form from the children it happens to have. The lowering above this tree
//! dispatches on forms, so the tree names them: a consumer matches on
//! [`NodeKind`] and there is nothing to adapt.
//!
//! # Sort is positional, so a name is one kind
//!
//! An identifier is a [`NodeKind::Name`] wherever it appears. Which sort it is
//! read at — a declared name, a binder, a type head, a term name — is decided
//! by its parent's kind and its position under it, both of which the closed
//! vocabulary fixes. Splitting `Name` per sort would double the vocabulary to
//! restate what the parent already determines.
//!
//! # Punctuation is implied, grouping is not
//!
//! The tree carries no node for a token whose presence the parent's kind
//! determines: a signature's colon and semicolon are recoverable from
//! [`NodeKind::Signature`] alone. A grouping is different — `(x)` and `x`
//! differ in the token stream and in nothing else — so [`NodeKind::Grouped`]
//! is a node, which is what lets a re-render reproduce the lexer's own stream
//! exactly rather than a re-parenthesized variant of it.

/// The pinned tag a node kind contributes to a content digest.
///
/// The tag is written into the digest preimage instead of the variant's
/// discriminant so that reordering the enum — an ordinary readability edit —
/// cannot silently change every digest a stored checkpoint was keyed by.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KindTag(u8);

impl From<KindTag> for u8
{
    /// Read the tag back out as the byte written into a digest preimage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: KindTag) -> Self
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

/// Every form the surface fragment's concrete syntax tree admits.
///
/// The enum is closed: the fragment's grammar is fixed, so a form outside it
/// has no representation here, and widening the grammar breaks every consumer
/// until each has considered the new form.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeKind
{
    /// The root: a module's declaration-sort children, in source order.
    ///
    /// An attribute block is a child of the module rather than of the
    /// declaration it decorates, so that attaching, editing or removing an
    /// attribute leaves the decorated declaration's content digest unchanged —
    /// which is the property the attribute side table is keyed on.
    Module,
    /// `@[ … ]`: a leading attribute block, its attributes as children.
    AttributeBlock,
    /// One attribute: a name, and a payload when the schema takes one.
    Attribute,
    /// `def name : Type ;`: a name and the type it is declared at.
    Signature,
    /// `def name = term ;`: a name and the term it is defined as.
    Definition,

    /// An identifier, at whatever sort its position gives it.
    Name,
    /// An integer literal.
    IntegerLiteral,
    /// A quoted text literal.
    TextLiteral,
    /// `( … )`: a parenthesized subtree, carried so a re-render is exact.
    Grouped,

    /// A type head applied to one argument, as in `U C` and `F A`.
    TypeApplication,
    /// `A -> C`: a domain value type and a codomain computation type.
    TypeArrow,
    /// `A * B`: the reserved product former, parsed so it can be declined.
    TypeProduct,

    /// `thunk { c }`: a suspended computation.
    Thunk,
    /// `return v`: a returner over a value.
    Return,
    /// `force v`: a forced thunk.
    Force,
    /// `\x. c`: a binder and the computation it scopes.
    Lambda,
    /// `c v`: a computation applied to a value argument.
    Application,
    /// `(v, v)`: the reserved pair former, parsed so it can be declined.
    Pair,
}

impl NodeKind
{
    /// Every node kind, in vocabulary order.
    pub const ALL: [Self; 18_usize] = [
        Self::Module,
        Self::AttributeBlock,
        Self::Attribute,
        Self::Signature,
        Self::Definition,
        Self::Name,
        Self::IntegerLiteral,
        Self::TextLiteral,
        Self::Grouped,
        Self::TypeApplication,
        Self::TypeArrow,
        Self::TypeProduct,
        Self::Thunk,
        Self::Return,
        Self::Force,
        Self::Lambda,
        Self::Application,
        Self::Pair,
    ];

    /// The tag this kind contributes to a content digest.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: each kind yields its own tag, distinct from every other
    ///   kind's, and the value is fixed rather than derived from declaration
    ///   order.
    /// - provides: the kind half of a node's digest preimage, so two nodes of
    ///   different forms over identical children have different identities.
    ///   This stays a `const fn` without `#[spec]`: the pinned `anodized`
    ///   expansion calls a non-const evaluator (`E0015`). The distinctness half
    ///   is a law over the whole vocabulary rather than a predicate over one
    ///   call, and the pinned tag table carries it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively against a pinned tag table, with pairwise distinctness
    ///   asserted over the same enumeration; a swapped pair of rows breaks two
    ///   pinned values, and a duplicated row breaks distinctness.
    /// - witness: `kind::tests::every_digest_tag_is_pinned`
    /// - witness: `kind::tests::the_digest_tags_are_pairwise_distinct`
    #[inline]
    #[must_use]
    pub const fn tag(self) -> KindTag
    {
        KindTag(match self {
            | Self::Module => 0x01_u8,
            | Self::AttributeBlock => 0x02_u8,
            | Self::Attribute => 0x03_u8,
            | Self::Signature => 0x04_u8,
            | Self::Definition => 0x05_u8,
            | Self::Name => 0x06_u8,
            | Self::IntegerLiteral => 0x07_u8,
            | Self::TextLiteral => 0x08_u8,
            | Self::Grouped => 0x09_u8,
            | Self::TypeApplication => 0x0a_u8,
            | Self::TypeArrow => 0x0b_u8,
            | Self::TypeProduct => 0x0c_u8,
            | Self::Thunk => 0x0d_u8,
            | Self::Return => 0x0e_u8,
            | Self::Force => 0x0f_u8,
            | Self::Lambda => 0x10_u8,
            | Self::Application => 0x11_u8,
            | Self::Pair => 0x12_u8,
        })
    }

    /// Whether a node of this kind folds its own source text into its digest.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: exactly the three leaf kinds whose meaning is their text —
    ///   [`NodeKind::Name`], [`NodeKind::IntegerLiteral`] and
    ///   [`NodeKind::TextLiteral`] — answer affirmatively; every structural
    ///   kind answers negatively, so an empty module's identity does not depend
    ///   on the whitespace its span happens to cover.
    /// - provides: the text half of a node's digest preimage. This stays a
    ///   `const fn` without `#[spec]`: the pinned `anodized` expansion calls a
    ///   non-const evaluator (`E0015`).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively with each kind's exact answer asserted, so promoting or
    ///   demoting any single kind breaks one assertion.
    /// - witness: `kind::tests::only_the_text_leaves_carry_text`
    #[inline]
    #[must_use]
    pub const fn carries_text(self) -> CarriesText
    {
        CarriesText(matches!(
            self,
            Self::Name | Self::IntegerLiteral | Self::TextLiteral
        ))
    }
}

#[cfg(test)]
mod tests
{
    use super::CarriesText;
    use super::KindTag;
    use super::NodeKind;

    #[test]
    fn every_node_kind_is_listed_once()
    {
        for kind in NodeKind::ALL {
            // Exhaustive by construction: a kind added to the vocabulary does
            // not compile until it is listed here and in `ALL`.
            let ordinal = match kind {
                | NodeKind::Module => 0_usize,
                | NodeKind::AttributeBlock => 1_usize,
                | NodeKind::Attribute => 2_usize,
                | NodeKind::Signature => 3_usize,
                | NodeKind::Definition => 4_usize,
                | NodeKind::Name => 5_usize,
                | NodeKind::IntegerLiteral => 6_usize,
                | NodeKind::TextLiteral => 7_usize,
                | NodeKind::Grouped => 8_usize,
                | NodeKind::TypeApplication => 9_usize,
                | NodeKind::TypeArrow => 10_usize,
                | NodeKind::TypeProduct => 11_usize,
                | NodeKind::Thunk => 12_usize,
                | NodeKind::Return => 13_usize,
                | NodeKind::Force => 14_usize,
                | NodeKind::Lambda => 15_usize,
                | NodeKind::Application => 16_usize,
                | NodeKind::Pair => 17_usize,
            };

            assert_eq!(
                NodeKind::ALL[ordinal],
                kind,
                "the vocabulary list holds each kind at its own position"
            );
        }

        assert_eq!(
            NodeKind::ALL.len(),
            18_usize,
            "the vocabulary has eighteen kinds"
        );
    }

    #[test]
    fn every_digest_tag_is_pinned()
    {
        let expected = [
            (NodeKind::Module, 0x01_u8),
            (NodeKind::AttributeBlock, 0x02_u8),
            (NodeKind::Attribute, 0x03_u8),
            (NodeKind::Signature, 0x04_u8),
            (NodeKind::Definition, 0x05_u8),
            (NodeKind::Name, 0x06_u8),
            (NodeKind::IntegerLiteral, 0x07_u8),
            (NodeKind::TextLiteral, 0x08_u8),
            (NodeKind::Grouped, 0x09_u8),
            (NodeKind::TypeApplication, 0x0a_u8),
            (NodeKind::TypeArrow, 0x0b_u8),
            (NodeKind::TypeProduct, 0x0c_u8),
            (NodeKind::Thunk, 0x0d_u8),
            (NodeKind::Return, 0x0e_u8),
            (NodeKind::Force, 0x0f_u8),
            (NodeKind::Lambda, 0x10_u8),
            (NodeKind::Application, 0x11_u8),
            (NodeKind::Pair, 0x12_u8),
        ];

        for (kind, tag) in expected {
            assert_eq!(
                kind.tag(),
                KindTag(tag),
                "the digest tag table is pinned row by row"
            );
        }

        assert_eq!(
            expected.len(),
            NodeKind::ALL.len(),
            "the pinned table covers the whole vocabulary"
        );
    }

    #[test]
    fn the_digest_tags_are_pairwise_distinct()
    {
        for (first, left) in NodeKind::ALL.into_iter().enumerate() {
            for (second, right) in NodeKind::ALL.into_iter().enumerate() {
                if first == second {
                    continue;
                }

                assert_ne!(
                    left.tag(),
                    right.tag(),
                    "two kinds sharing a tag would share a digest preimage"
                );
            }
        }
    }

    #[test]
    fn only_the_text_leaves_carry_text()
    {
        // Pinned rather than recomputed: a table restating the implementation's
        // own pattern would shift with any mutant that shifts the pattern.
        let expected = [
            (NodeKind::Module, false),
            (NodeKind::AttributeBlock, false),
            (NodeKind::Attribute, false),
            (NodeKind::Signature, false),
            (NodeKind::Definition, false),
            (NodeKind::Name, true),
            (NodeKind::IntegerLiteral, true),
            (NodeKind::TextLiteral, true),
            (NodeKind::Grouped, false),
            (NodeKind::TypeApplication, false),
            (NodeKind::TypeArrow, false),
            (NodeKind::TypeProduct, false),
            (NodeKind::Thunk, false),
            (NodeKind::Return, false),
            (NodeKind::Force, false),
            (NodeKind::Lambda, false),
            (NodeKind::Application, false),
            (NodeKind::Pair, false),
        ];

        for (kind, carries) in expected {
            assert_eq!(
                kind.carries_text(),
                CarriesText(carries),
                "exactly the three text leaves fold their own source text"
            );
        }

        assert_eq!(
            expected.len(),
            NodeKind::ALL.len(),
            "the pinned table covers the whole vocabulary"
        );
    }
}
