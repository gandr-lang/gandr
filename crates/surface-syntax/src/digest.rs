//! The content-derived node identity, [`NodeDigest`], and the preimage it is
//! computed over.
//!
//! # Two identities, and why the distinction is load-bearing
//!
//! A node has an arena position and a content digest, and they answer different
//! questions. The position addresses a node *inside one tree*: it is an offset
//! into that tree's node vector and it means nothing anywhere else, because the
//! next parse of an edited source lays the same declaration out at a different
//! offset. The digest addresses a node *across* trees, runs and processes: it
//! is a function of the node's label and its content and of nothing else, so
//! the same declaration parsed from two files, in two processes, on two
//! machines, carries the same digest.
//!
//! A diagnostic that carries both resolves fast inside the tree in hand and
//! survives the tree. A side table keyed by a position is invalidated by an
//! edit anywhere earlier in the file; a side table keyed by a digest is
//! invalidated only by an edit to the thing it is about, which is why a table
//! that outlives one parse keys on the digest alone.
//!
//! # What the preimage excludes
//!
//! Spans are not hashed. A node's digest must not change when the same text
//! moves, or the cross-tree half of the identity would decay into a
//! position under another name. Neither are the arena positions of the
//! children: a node folds its children's *digests*, so the fold is itself
//! position-free. Layout children are not folded at all, so reformatting a
//! node leaves its identity unchanged.
//!
//! # What the preimage includes, and in what shape
//!
//! The domain string, the label's pinned tag, the label's payload, the
//! significant child count, the node's own text when its label carries text,
//! and the significant children's digests in order. Every variable-width field
//! is preceded by its length at a fixed width, so two sibling texts cannot run
//! together into a third reading: `ab` beside `c` and `a` beside `bc` have
//! different preimages, not one shared one.

use crate::label::NodeLabel;
use crate::mold::ClosingClass;
use crate::mold::GroutShape;
use crate::span::SourceFragment;

/// Byte width of a node identity, fixed by the hash family.
pub const NODE_DIGEST_LEN: usize = 32_usize;

/// The domain every node digest is computed under.
///
/// The version suffix is part of the domain rather than a field beside it: a
/// change to the preimage layout is a change of identity for every node, and
/// the two generations must not be comparable.
const NODE_DOMAIN: &[u8] = b"gandr.surface-syntax.node.v2";

/// The content identity of one node: a digest of its label and its content.
///
/// # Specification
/// - requires: nothing; the type is a carrier and admits any byte array.
/// - ensures: `Display` renders the lowercase hexadecimal of the bytes in
///   order, and `Debug` renders identically, because one identity read in two
///   notations in one log is harder to match by eye than it is worth.
/// - provides: an opaque, fixed-width name for a node's content.
/// - fails: never.
/// - panics: none.
/// - executable: none — the carrier admits every byte array; its rendering
///   obligation concerns trait implementations, not a data invariant.
///
/// # Adequacy
/// - hypothesis: L3 only — the rendering is separated from any other rendering
///   by one pinned digest whose hexadecimal is asserted exactly, with a leading
///   byte below sixteen so a dropped zero pad is visible.
/// - witness: `digest::tests::a_digest_renders_lowercase_hexadecimal`
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeDigest([u8; NODE_DIGEST_LEN]);

impl NodeDigest
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
        let mut left = self.0.as_slice();
        let mut right = other.0.as_slice();
        let mut same = true;
        while let (Some((a, rest_a)), Some((b, rest_b))) = (left.split_first(), right.split_first())
        {
            same = same && *a == *b;
            left = rest_a;
            right = rest_b;
        }
        if same {
            crate::ConstEquality::Equal
        }
        else {
            crate::ConstEquality::Unequal
        }
    }
}

impl From<[u8; NODE_DIGEST_LEN]> for NodeDigest
{
    /// Read a fixed-width byte array as a node identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; NODE_DIGEST_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl From<NodeDigest> for [u8; NODE_DIGEST_LEN]
{
    /// Read the identity back out as its bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(digest: NodeDigest) -> Self
    {
        digest.0
    }
}

impl AsRef<[u8]> for NodeDigest
{
    /// Borrow the identity's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl core::fmt::Display for NodeDigest
{
    /// Write the identity as lowercase hexadecimal.
    ///
    /// # Specification
    /// - requires: nothing; every byte array is an admissible identity.
    /// - ensures: writes each byte in order as exactly two lowercase
    ///   hexadecimal digits, so the rendering is fixed-width and a byte below
    ///   sixteen keeps its leading zero.
    /// - provides: the opaque name for a node's content that a log line and a
    ///   test failure message both carry.
    /// - fails: propagates the formatter's own write failure unchanged,
    ///   stopping at the byte that failed.
    /// - panics: none.
    /// - executable: none — the formatter exposes a write-only sink; neither
    ///   emitted bytes nor the sink's failure state can be read back by a
    ///   predicate, and replaying writes changes the observed sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full-width digest with a leading byte below sixteen
    ///   exposes dropped padding, uppercase digits, reordered bytes and
    ///   divergent notations through exact strings; a rejecting sink detects
    ///   swallowed errors.
    /// - witness: `digest::tests::a_digest_renders_lowercase_hexadecimal`
    /// - witness: `digest::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

impl core::fmt::Debug for NodeDigest
{
    /// Write the identity as its `Display` rendering does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly what [`core::fmt::Display`] writes for the
    ///   same identity, so one identity never appears in two notations in one
    ///   log.
    /// - provides: the single rendering the type's own specification claims.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes a write-only sink; neither
    ///   emitted bytes nor the sink's failure state can be read back by a
    ///   predicate, and replaying writes changes the observed sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full-width digest with a leading byte below sixteen
    ///   exposes dropped padding, uppercase digits, reordered bytes and
    ///   divergent notations through exact strings; a rejecting sink detects
    ///   swallowed errors.
    /// - witness: `digest::tests::a_digest_renders_lowercase_hexadecimal`
    /// - witness: `digest::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        core::fmt::Display::fmt(self, f)
    }
}

/// The content identity of a node labelled `label` spanning `text` over the
/// significant `children`.
///
/// # Specification
/// - requires: `text` is the fragment the node's span covers, and `children`
///   holds the digests of its immediate children whose labels are significant,
///   in the order the node carries them.
/// - ensures: equal `(label, folded text, children)` triples give equal
///   digests, where the label contributes its tag and its payload — a mold id,
///   or a grout's sort and shape, or a minted close's sort and family — and the
///   folded text is `text` exactly when the label carries text and is absent
///   otherwise; the digest is independent of where in a source the node sits,
///   and of the arena the node will be laid out into.
/// - provides: the crate's only hashing entry point, so no node identity is
///   computed outside the domain or with a differently shaped preimage.
/// - fails: never.
/// - panics: none.
/// - executable: none — source provenance is not carried by these arguments,
///   and position-independent identity is a relation between calls. Repeating
///   the same hash in a postcondition supplies no independent observation.
///
/// Counts and lengths enter the preimage at a fixed eight-byte width so the
/// digest does not depend on the pointer width of the machine that computed it.
/// A value above that width saturates at its ceiling — about eighteen
/// quintillion children or bytes, far above what any source produces — so the
/// saturation is a documented ceiling rather than a reachable path.
///
/// # Adequacy
/// - hypothesis: L2 — one node's digest is pinned against an external
///   hexadecimal golden, so any change to the domain, the tag placement, the
///   payload, the count width or the field order moves it; the L3 residue is
///   the set of collisions a fold could admit, separated by two labels over
///   identical children, by two payloads of one variant, by two sibling texts
///   of equal total length split differently, by reversed child order, and by
///   an interior label whose text differs.
/// - witness: `digest::tests::a_pinned_leaf_digest_is_stable`
/// - witness: `digest::tests::two_labels_over_the_same_children_differ`
/// - witness: `digest::tests::every_payload_reaches_the_digest`
/// - witness: `digest::tests::sibling_texts_do_not_run_together`
/// - witness: `digest::tests::child_order_changes_the_digest`
/// - witness: `digest::tests::an_interior_label_ignores_its_own_text`
#[inline]
#[must_use]
pub fn digest_of(
    label: NodeLabel,
    text: SourceFragment<'_>,
    children: &[NodeDigest],
) -> NodeDigest
{
    let mut hasher = blake3::Hasher::new();
    let _domain = hasher.update(NODE_DOMAIN);
    let _tag = hasher.update(&[u8::from(label.tag())]);
    match label {
        | NodeLabel::Wald | NodeLabel::Space => {},
        | NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
            let _mold = hasher.update(&u32::from(mold).to_le_bytes());
        },
        | NodeLabel::Grout { sort, shape } => {
            let _sort = hasher.update(&u16::from(sort).to_le_bytes());
            let _shape = hasher.update(&[match shape {
                | GroutShape::Convex => 0x01_u8,
                | GroutShape::Prefix => 0x02_u8,
                | GroutShape::Postfix => 0x03_u8,
                | GroutShape::Infix => 0x04_u8,
            }]);
        },
        | NodeLabel::GhostClose { sort, class } => {
            let _sort = hasher.update(&u16::from(sort).to_le_bytes());
            let _class = hasher.update(&[match class {
                | ClosingClass::Paren => 0x01_u8,
                | ClosingClass::Bracket => 0x02_u8,
                | ClosingClass::Brace => 0x03_u8,
            }]);
        },
    }
    let child_count = u64::try_from(children.len()).unwrap_or(u64::MAX);
    let _count = hasher.update(&child_count.to_le_bytes());
    if bool::from(label.carries_text()) {
        let bytes = <&str>::from(text).as_bytes();
        let text_length = u64::try_from(bytes.len()).unwrap_or(u64::MAX);
        let _length = hasher.update(&text_length.to_le_bytes());
        let _text = hasher.update(bytes);
    }
    for child in children {
        let _child = hasher.update(child.as_ref());
    }
    let mut output = [0_u8; NODE_DIGEST_LEN];
    hasher.finalize_xof().fill(output.as_mut_slice());

    NodeDigest(output)
}

#[cfg(test)]
mod tests
{
    use alloc::format;

    use super::NODE_DIGEST_LEN;
    use super::NodeDigest;
    use super::digest_of;
    use crate::label::NodeLabel;
    use crate::mold::ClosingClass;
    use crate::mold::GroutShape;
    use crate::mold::GroutSort;
    use crate::mold::MoldId;
    use crate::span::SourceFragment;

    /// The digest of a childless node labelled `label` whose fragment is
    /// `text`.
    ///
    /// # Specification
    /// - requires: `text` is the fragment the node covers, under the same
    ///   reading [`digest_of`] asks of it.
    /// - ensures: the digest of `label` over `text` with no children.
    /// - provides: the childless case every rendering and collision fixture
    ///   below is written against.
    /// - panics: none.
    /// - executable: none — fragment provenance is not carried by the input; an
    ///   equality check would repeat the hashing operation it purports to check
    ///   rather than supply an independent observation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the childless digest is checked against an external
    ///   golden; L3 text-folding boundaries separate interior and leaf labels
    ///   with equal versus changed fragments.
    /// - witness: `digest::tests::a_pinned_leaf_digest_is_stable`
    /// - witness: `digest::tests::an_interior_label_ignores_its_own_text`
    fn leaf(
        label: NodeLabel,
        text: SourceFragment<'_>,
    ) -> NodeDigest
    {
        digest_of(label, text, &[])
    }

    /// A tile of `mold` whose fragment is `text`.
    ///
    /// # Specification
    /// trivial.
    fn tile(
        mold: MoldId,
        text: SourceFragment<'_>,
    ) -> NodeDigest
    {
        leaf(NodeLabel::Tile(mold), text)
    }

    /// A tile of the first mold whose fragment is `text`.
    ///
    /// # Specification
    /// trivial.
    fn word(text: SourceFragment<'_>) -> NodeDigest
    {
        tile(MoldId::from(1_u32), text)
    }

    #[test]
    fn formatters_propagate_sink_failure()
    {
        use core::fmt::Write as _;
        let digest = NodeDigest::from([0_u8; NODE_DIGEST_LEN]);
        let mut sink = crate::test_support::RefusingSink;
        assert!(sink.write_fmt(format_args!("{digest}")).is_err());
        assert!(sink.write_fmt(format_args!("{digest:?}")).is_err());
    }

    #[test]
    fn a_digest_renders_lowercase_hexadecimal()
    {
        let mut bytes = [0_u8; NODE_DIGEST_LEN];
        bytes[0] = 0x0a_u8;
        bytes[1] = 0xff_u8;
        let digest = NodeDigest::from(bytes);

        assert_eq!(
            format!("{digest}"),
            "0aff000000000000000000000000000000000000000000000000000000000000",
            "each byte renders as two lowercase hexadecimal digits"
        );
        assert_eq!(
            format!("{digest:?}"),
            format!("{digest}"),
            "the two notations agree"
        );
    }

    #[test]
    fn a_pinned_leaf_digest_is_stable()
    {
        // The golden is external: it is `b3sum` over the fifty-four preimage
        // bytes this layout specifies — the domain string, the tag `0x03`, the
        // little-endian mold id seven, a little-endian child count of zero, a
        // little-endian text length of five, and `value` — computed outside
        // this crate, so a change to the domain, the tag placement, the
        // payload, a field width or the field order moves the left side and
        // not the right.
        assert_eq!(
            format!(
                "{}",
                tile(MoldId::from(7_u32), SourceFragment::from("value"))
            ),
            "7951888b97e227bb76a1ca6bd9736ed8fb7be0ecb4369a5b4bdb11f43ec9b0b4",
            "the preimage layout is pinned against an external golden"
        );
    }

    #[test]
    fn two_labels_over_the_same_children_differ()
    {
        let child = word(SourceFragment::from("x"));
        let empty = SourceFragment::from("");

        assert_ne!(
            digest_of(NodeLabel::Meld(MoldId::from(2_u32)), empty, &[child]),
            digest_of(NodeLabel::Wald, empty, &[child]),
            "the label tag separates two forms over identical children"
        );
        assert_ne!(
            leaf(NodeLabel::Meld(MoldId::from(2_u32)), empty),
            leaf(NodeLabel::Tile(MoldId::from(2_u32)), empty),
            "a form and a tile of one mold are distinct nodes"
        );
    }

    #[test]
    fn every_payload_reaches_the_digest()
    {
        let empty = SourceFragment::from("");
        assert_ne!(
            leaf(NodeLabel::Meld(MoldId::from(2_u32)), empty),
            leaf(NodeLabel::Meld(MoldId::from(3_u32)), empty),
            "a form's mold reaches its digest"
        );
        assert_ne!(
            tile(MoldId::from(2_u32), SourceFragment::from("x")),
            tile(MoldId::from(3_u32), SourceFragment::from("x")),
            "a tile's mold reaches its digest beside its text"
        );
        let grout = |sort: u16, shape: GroutShape| {
            leaf(
                NodeLabel::Grout {
                    sort: GroutSort::from(sort),
                    shape,
                },
                empty,
            )
        };
        assert_ne!(
            grout(1_u16, GroutShape::Convex),
            grout(2_u16, GroutShape::Convex),
            "a grout's sort reaches its digest"
        );
        let shapes = [
            GroutShape::Convex,
            GroutShape::Prefix,
            GroutShape::Postfix,
            GroutShape::Infix,
        ];
        for (first, left) in shapes.into_iter().enumerate() {
            for (second, right) in shapes.into_iter().enumerate() {
                if first != second {
                    assert_ne!(
                        grout(1_u16, left),
                        grout(1_u16, right),
                        "every grout shape writes its own byte"
                    );
                }
            }
        }
        let close = |sort: u16, class: ClosingClass| {
            leaf(
                NodeLabel::GhostClose {
                    sort: GroutSort::from(sort),
                    class,
                },
                empty,
            )
        };
        assert_ne!(
            close(1_u16, ClosingClass::Paren),
            close(2_u16, ClosingClass::Paren),
            "a minted close's sort reaches its digest"
        );
        let classes = [
            ClosingClass::Paren,
            ClosingClass::Bracket,
            ClosingClass::Brace,
        ];
        for (first, left) in classes.into_iter().enumerate() {
            for (second, right) in classes.into_iter().enumerate() {
                if first != second {
                    assert_ne!(
                        close(1_u16, left),
                        close(1_u16, right),
                        "every closing family writes its own byte"
                    );
                }
            }
        }
    }

    #[test]
    fn sibling_texts_do_not_run_together()
    {
        let empty = SourceFragment::from("");
        let split_early = [
            word(SourceFragment::from("ab")),
            word(SourceFragment::from("c")),
        ];
        let split_late = [
            word(SourceFragment::from("a")),
            word(SourceFragment::from("bc")),
        ];
        let form = NodeLabel::Meld(MoldId::from(5_u32));

        assert_ne!(
            digest_of(form, empty, &split_early),
            digest_of(form, empty, &split_late),
            "a length-prefixed text cannot be re-split across its siblings"
        );
    }

    #[test]
    fn child_order_changes_the_digest()
    {
        let empty = SourceFragment::from("");
        let first = word(SourceFragment::from("f"));
        let second = word(SourceFragment::from("x"));
        let form = NodeLabel::Meld(MoldId::from(5_u32));

        assert_ne!(
            digest_of(form, empty, &[first, second]),
            digest_of(form, empty, &[second, first]),
            "the fold is ordered, so an applied argument is not its own head"
        );
    }

    #[test]
    fn an_interior_label_ignores_its_own_text()
    {
        let form = NodeLabel::Meld(MoldId::from(5_u32));
        assert_eq!(
            leaf(form, SourceFragment::from("def a = b ;")),
            leaf(form, SourceFragment::from("")),
            "an interior label's identity does not read the bytes it spans"
        );
        assert_eq!(
            leaf(NodeLabel::Wald, SourceFragment::from("def a = b ;")),
            leaf(NodeLabel::Wald, SourceFragment::from("")),
            "the root's identity does not read the bytes it spans"
        );
        assert_ne!(
            word(SourceFragment::from("a")),
            word(SourceFragment::from("b")),
            "a tile's identity is exactly its mold and its text"
        );
        assert_ne!(
            leaf(NodeLabel::Space, SourceFragment::from(" ")),
            leaf(NodeLabel::Space, SourceFragment::from("  ")),
            "layout carries its own text"
        );
        assert_ne!(
            leaf(
                NodeLabel::Grout {
                    sort: GroutSort::from(1_u16),
                    shape: GroutShape::Convex,
                },
                SourceFragment::from("~"),
            ),
            leaf(
                NodeLabel::Grout {
                    sort: GroutSort::from(1_u16),
                    shape: GroutShape::Convex,
                },
                SourceFragment::from("^"),
            ),
            "grout over an unmolded token carries that token's bytes"
        );
    }
}
