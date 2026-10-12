//! The content-derived form identity, [`NodeDigest`], and the preimage it is
//! computed over.
//!
//! # Two identities, and why the distinction is load-bearing
//!
//! A node has an arena position and a cross-tree key, and they answer
//! different questions. The position addresses a node *inside one tree*: it is
//! an offset into that tree's node vector and it means nothing anywhere else,
//! because the next parse of an edited source lays the same declaration out at
//! a different offset. The key addresses a node *across* trees, runs and
//! processes: it is the digest of the top-level form holding the node and the
//! node's rank in that form, a function of the form's labels and content and
//! of nothing else, so the same declaration parsed from two files, in two
//! processes, on two machines, carries the same key.
//!
//! A side table keyed by a position is invalidated by an edit anywhere earlier
//! in the file; a side table keyed by a key is invalidated only by an edit to
//! the form it is about, which is why a table that outlives one parse keys on
//! the key alone.
//!
//! # What the preimage excludes
//!
//! Spans are not hashed. A form's digest must not change when the same text
//! moves, or the cross-tree identity would decay into a position under another
//! name. Layout and documentation are not serialized at all, so reformatting or
//! re-documenting a form leaves its identity unchanged.
//!
//! # What the preimage includes, and in what shape
//!
//! A form's preimage is its domain string, then each significant node of the
//! form in preorder: the label's pinned tag, the label's payload, the
//! significant child count, and, when the label carries text, the text's
//! length and the text. Every variable-width field is preceded by its length at
//! a fixed width and every node by its child count, so the bytes read back to
//! one tree: two sibling texts cannot run together into a third reading, and a
//! node cannot pass for its sibling's child. A tree's preimage is its own
//! domain, the root's label read the same way with the form count as its child
//! count, and the forms' digests in order.
//!
//! # Digest preimage
//!
//! A form's preimage is the domain string `gandr.surface-syntax.form.v1`, then
//! each significant node of the form in preorder: the label's pinned tag, the
//! label's payload (a mold id as four little-endian bytes; a grout's sort as
//! two and its shape as one; a minted close's sort as two and its family as
//! one), the significant child count as four little-endian bytes, and, when the
//! label is a leaf label, the text's length as four little-endian bytes and the
//! text. Spans, positions, layout and documentation are excluded, so moving or
//! reformatting text leaves the digest unchanged. Every variable-width field is
//! preceded by its length and every node by its child count, so `ab` beside `c`
//! and `a` beside `bc` hash differently, and `f (x y)` and `(f x) y` do too. A
//! tree's preimage is `gandr.surface-syntax.tree.v1`, the root's label read the
//! same way with the form count as its child count, and the forms' digests in
//! order. The version suffix belongs to the domain: a change to the layout
//! changes every identity, and two layouts never compare equal. The pinned form
//! is asserted against an external BLAKE3 golden rather than a value this crate
//! produced.
//!
//! ### A digest per form, not per node
//!
//! `TreeBuilder::finish` walks each top-level form in preorder once, ranking
//! its nodes and writing their bytes into one buffer, and hashes the buffer in
//! one `blake3::hash` call; the tree's digest hashes the forms' digests.
//! Nothing is hashed while a node is staged.
//!
//! - Choice: one digest per top-level form, the only identity a consumer reads,
//!   with a rank keying every node inside it.
//! - Alternatives: a digest per node, hashed as each node is staged, with each
//!   leaf hashed once per builder and a parser carrying a molded form's digests
//!   across revisions; it cost about a sixth of a parse and nothing read a
//!   digest below a form. Deferring the per-node digests until after lowering
//!   kept that cost, off the critical path but not gone.
//! - Reversal: a consumer that needs a node's own content identity below its
//!   form — reuse of a sub-form's work across a move — needs a digest per node
//!   again.

use alloc::vec::Vec;

use crate::label::NodeLabel;
use crate::mold::ClosingClass;
use crate::mold::GroutShape;
use crate::span::SourceFragment;
use crate::tree::ChildCount;

/// Byte width of a node identity, fixed by the hash family.
pub const NODE_DIGEST_LEN: usize = 32_usize;

/// The domain every form digest is computed under.
///
/// The version suffix is part of the domain rather than a field beside it: a
/// change to the preimage layout is a change of identity for every form, and
/// the two generations must not be comparable.
const FORM_DOMAIN: &[u8] = b"gandr.surface-syntax.form.v1";

/// The domain every tree digest is computed under, apart from the forms' so a
/// tree of one form is never its form.
const TREE_DOMAIN: &[u8] = b"gandr.surface-syntax.tree.v1";

/// The content identity of one top-level form or one whole tree: a digest of
/// its labels and its content.
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

/// A preimage under construction: a domain, then nodes and digests.
///
/// One buffer serves every form of a tree, cleared as each opens, so a tree
/// allocates for its longest form and hashes each form in one call.
///
/// # Specification
/// - ensures: the buffer holds the bytes written since the last opening.
/// - executable: none — the buffer is the state; each writer states what it
///   appends.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Preimage(Vec<u8>);

impl Preimage
{
    /// Start a form's preimage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn open_form(&mut self)
    {
        self.0.clear();
        self.0.extend_from_slice(FORM_DOMAIN);
    }

    /// Start a tree's preimage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn open_tree(&mut self)
    {
        self.0.clear();
        self.0.extend_from_slice(TREE_DOMAIN);
    }

    /// Append a node labelled `label` over `text` with `children` significant
    /// children.
    ///
    /// Counts and lengths enter at a fixed four-byte width, so a digest does
    /// not depend on the pointer width of the machine that computed it. A
    /// value above that width saturates at its ceiling, four gibibytes of text
    /// or four billion children, past the offsets a parser emits, so the
    /// saturation is a documented ceiling rather than a reachable path.
    ///
    /// # Specification
    /// - requires: `text` is the fragment the node covers.
    /// - ensures: appends the label's tag and payload — a mold id, or a grout's
    ///   sort and shape, or a minted close's sort and family — then the child
    ///   count, then the text's length and the text exactly when the label
    ///   carries text.
    /// - panics: none.
    /// - executable: none — the appended bytes are the body; restating them
    ///   observes nothing independent.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a form's digest is pinned against an external golden
    ///   and against the layout spelled field by field; the L3 residue is the
    ///   set of collisions a serialization could admit, separated by two
    ///   labels, two payloads of one variant, sibling texts split differently,
    ///   reversed children, a node moved under its sibling, and an interior
    ///   label whose text differs.
    /// - witness: `digest::tests::a_pinned_form_digest_is_stable`
    /// - witness: `digest::tests::a_form_hashes_its_layout_field_by_field`
    /// - witness: `digest::tests::two_labels_over_the_same_children_differ`
    /// - witness: `digest::tests::every_payload_reaches_the_digest`
    /// - witness: `digest::tests::sibling_texts_do_not_run_together`
    /// - witness: `digest::tests::child_order_changes_the_digest`
    /// - witness: `digest::tests::nesting_changes_the_digest`
    /// - witness: `digest::tests::an_interior_label_ignores_its_own_text`
    pub fn node(
        &mut self,
        label: NodeLabel,
        text: SourceFragment<'_>,
        children: ChildCount,
    )
    {
        let bytes = &mut self.0;
        bytes.push(u8::from(label.tag()));
        match label {
            | NodeLabel::Wald | NodeLabel::Space | NodeLabel::Doc => {},
            | NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
                bytes.extend_from_slice(&u32::from(mold).to_le_bytes());
            },
            | NodeLabel::Grout { sort, shape } => {
                bytes.extend_from_slice(&u16::from(sort).to_le_bytes());
                bytes.push(match shape {
                    | GroutShape::Convex => 0x01_u8,
                    | GroutShape::Prefix => 0x02_u8,
                    | GroutShape::Postfix => 0x03_u8,
                    | GroutShape::Infix => 0x04_u8,
                });
            },
            | NodeLabel::GhostClose { sort, class } => {
                bytes.extend_from_slice(&u16::from(sort).to_le_bytes());
                bytes.push(match class {
                    | ClosingClass::Paren => 0x01_u8,
                    | ClosingClass::Bracket => 0x02_u8,
                    | ClosingClass::Brace => 0x03_u8,
                });
            },
        }
        bytes.extend_from_slice(
            &u32::try_from(usize::from(children))
                .unwrap_or(u32::MAX)
                .to_le_bytes(),
        );
        if bool::from(label.carries_text()) {
            let text = <&str>::from(text).as_bytes();
            bytes.extend_from_slice(&u32::try_from(text.len()).unwrap_or(u32::MAX).to_le_bytes());
            bytes.extend_from_slice(text);
        }
    }

    /// Append a form's digest to a tree's preimage.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn digest(
        &mut self,
        digest: NodeDigest,
    )
    {
        self.0.extend_from_slice(digest.as_ref());
    }

    /// The digest of the bytes written since the last opening.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn hash(&self) -> NodeDigest
    {
        NodeDigest(*blake3::hash(&self.0).as_bytes())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;

    use super::NODE_DIGEST_LEN;
    use super::NodeDigest;
    use super::Preimage;
    use crate::label::NodeLabel;
    use crate::mold::ClosingClass;
    use crate::mold::GroutShape;
    use crate::mold::GroutSort;
    use crate::mold::MoldId;
    use crate::span::SourceFragment;
    use crate::tree::ChildCount;

    /// The digest of a form whose significant nodes, in preorder, are
    /// `nodes`: each a label, its text and its significant child count.
    ///
    /// # Specification
    /// - requires: `nodes` is a preorder whose counts describe one tree.
    /// - ensures: the digest the tree's layout takes for that form.
    /// - panics: none.
    /// - executable: none — the serialization is the body under test.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — pinned against an external golden.
    /// - witness: `digest::tests::a_pinned_form_digest_is_stable`
    fn form(nodes: &[(NodeLabel, SourceFragment<'_>, ChildCount)]) -> NodeDigest
    {
        let mut preimage = Preimage::default();
        preimage.open_form();
        for &(label, text, children) in nodes {
            preimage.node(label, text, children);
        }
        preimage.hash()
    }

    /// [`form`] over nodes spelled as a label, a string and a count.
    macro_rules! spelled {
        ($(($label:expr, $text:expr, $children:expr)),* $(,)?) => {
            form(&[$(($label, SourceFragment::from($text), ChildCount::from($children))),*])
        };
    }

    /// The digest of a form that is one childless node.
    ///
    /// # Specification
    /// trivial.
    fn leaf(
        label: NodeLabel,
        text: SourceFragment<'_>,
    ) -> NodeDigest
    {
        spelled![(label, text, ChildCount::from(0_usize))]
    }

    /// A tile of the first mold.
    ///
    /// # Specification
    /// trivial.
    fn word() -> NodeLabel
    {
        NodeLabel::Tile(MoldId::from(1_u32))
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
    fn a_pinned_form_digest_is_stable()
    {
        // The golden is external: it is `b3sum` over the forty-six preimage
        // bytes this layout specifies — the domain string, the tag `0x03`, the
        // little-endian mold id seven, a little-endian child count of zero, a
        // little-endian text length of five, and `value` — computed outside
        // this crate, so a change to the domain, the tag placement, the
        // payload, a field width or the field order moves the left side and
        // not the right.
        assert_eq!(
            format!(
                "{}",
                leaf(
                    NodeLabel::Tile(MoldId::from(7_u32)),
                    SourceFragment::from("value")
                )
            ),
            "98dcd54a74a087a8bcb01c2c5a74de642faaac7b702038638489779481e80da1",
            "the preimage layout is pinned against an external golden"
        );
    }

    #[test]
    fn a_form_hashes_its_layout_field_by_field()
    {
        // A form of an interior over two tiles, spelled here field by field
        // through the incremental hasher: a field dropped, duplicated or
        // misplaced moves one side only.
        let mold = MoldId::from(9_u32);
        let meld = u8::from(NodeLabel::Meld(mold).tag());
        let tile = u8::from(word().tag());
        let text = "t".repeat(300);
        let mut hasher = blake3::Hasher::new();
        let _spelled = hasher
            .update(b"gandr.surface-syntax.form.v1")
            .update(&[meld])
            .update(&9_u32.to_le_bytes())
            .update(&2_u32.to_le_bytes())
            .update(&[tile])
            .update(&1_u32.to_le_bytes())
            .update(&0_u32.to_le_bytes())
            .update(&1_u32.to_le_bytes())
            .update(b"f")
            .update(&[tile])
            .update(&1_u32.to_le_bytes())
            .update(&0_u32.to_le_bytes())
            .update(&300_u32.to_le_bytes())
            .update(text.as_bytes());
        assert_eq!(
            spelled![
                (NodeLabel::Meld(mold), "", 2),
                (word(), "f", 0),
                (word(), text.as_str(), 0),
            ],
            NodeDigest::from(*hasher.finalize().as_bytes()),
        );
    }

    #[test]
    fn two_labels_over_the_same_children_differ()
    {
        assert_ne!(
            spelled![
                (NodeLabel::Meld(MoldId::from(2_u32)), "", 1),
                (word(), "x", 0)
            ],
            spelled![(NodeLabel::Wald, "", 1), (word(), "x", 0)],
            "the label tag separates two forms over identical children"
        );
        assert_ne!(
            leaf(
                NodeLabel::Meld(MoldId::from(2_u32)),
                SourceFragment::from("")
            ),
            leaf(
                NodeLabel::Tile(MoldId::from(2_u32)),
                SourceFragment::from("")
            ),
            "a form and a tile of one mold are distinct nodes"
        );
    }

    #[test]
    fn every_payload_reaches_the_digest()
    {
        assert_ne!(
            leaf(
                NodeLabel::Meld(MoldId::from(2_u32)),
                SourceFragment::from("")
            ),
            leaf(
                NodeLabel::Meld(MoldId::from(3_u32)),
                SourceFragment::from("")
            ),
            "a form's mold reaches its digest"
        );
        assert_ne!(
            leaf(
                NodeLabel::Tile(MoldId::from(2_u32)),
                SourceFragment::from("x")
            ),
            leaf(
                NodeLabel::Tile(MoldId::from(3_u32)),
                SourceFragment::from("x")
            ),
            "a tile's mold reaches its digest beside its text"
        );
        let grout = |sort: u16, shape: GroutShape| {
            leaf(
                NodeLabel::Grout {
                    sort: GroutSort::from(sort),
                    shape,
                },
                SourceFragment::from(""),
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
                SourceFragment::from(""),
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
        let interior = NodeLabel::Meld(MoldId::from(5_u32));
        assert_ne!(
            spelled![(interior, "", 2), (word(), "ab", 0), (word(), "c", 0)],
            spelled![(interior, "", 2), (word(), "a", 0), (word(), "bc", 0)],
            "a length-prefixed text cannot be re-split across its siblings"
        );
    }

    #[test]
    fn child_order_changes_the_digest()
    {
        let interior = NodeLabel::Meld(MoldId::from(5_u32));
        assert_ne!(
            spelled![(interior, "", 2), (word(), "f", 0), (word(), "x", 0)],
            spelled![(interior, "", 2), (word(), "x", 0), (word(), "f", 0)],
            "the serialization is ordered, so an applied argument is not its own head"
        );
    }

    #[test]
    fn nesting_changes_the_digest()
    {
        // `f (x y)` and `(f x) y` spell the same tiles in the same order; the
        // child counts are what tell the two trees apart.
        let interior = NodeLabel::Meld(MoldId::from(5_u32));
        assert_ne!(
            spelled![
                (interior, "", 2),
                (word(), "f", 0),
                (interior, "", 2),
                (word(), "x", 0),
                (word(), "y", 0),
            ],
            spelled![
                (interior, "", 2),
                (interior, "", 2),
                (word(), "f", 0),
                (word(), "x", 0),
                (word(), "y", 0),
            ],
            "a node cannot pass for its sibling's child"
        );
    }

    #[test]
    fn an_interior_label_ignores_its_own_text()
    {
        let interior = NodeLabel::Meld(MoldId::from(5_u32));
        assert_eq!(
            leaf(interior, SourceFragment::from("def a = b ;")),
            leaf(interior, SourceFragment::from("")),
            "an interior label's identity does not read the bytes it spans"
        );
        assert_eq!(
            leaf(NodeLabel::Wald, SourceFragment::from("def a = b ;")),
            leaf(NodeLabel::Wald, SourceFragment::from("")),
            "the root's identity does not read the bytes it spans"
        );
        assert_ne!(
            leaf(word(), SourceFragment::from("a")),
            leaf(word(), SourceFragment::from("b")),
            "a tile's identity is exactly its mold and its text"
        );
        let grout = NodeLabel::Grout {
            sort: GroutSort::from(1_u16),
            shape: GroutShape::Convex,
        };
        assert_ne!(
            leaf(grout, SourceFragment::from("~")),
            leaf(grout, SourceFragment::from("^")),
            "grout over an unmolded token carries that token's bytes"
        );
    }
}
