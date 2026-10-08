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
//! is a function of the node's form and its content and of nothing else, so the
//! same declaration parsed from two files, in two processes, on two machines,
//! carries the same digest.
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
//! position-free.
//!
//! # What the preimage includes, and in what shape
//!
//! The domain string, the kind's pinned tag, the child count, the node's own
//! text when its kind carries text, and the children's digests in order. Every
//! variable-width field is preceded by its length at a fixed width, so two
//! sibling texts cannot run together into a third reading: `ab` beside `c` and
//! `a` beside `bc` have different preimages, not one shared one.

use crate::kind::NodeKind;
use crate::span::SourceFragment;

/// Byte width of a node identity, fixed by the hash family.
pub const NODE_DIGEST_LEN: usize = 32_usize;

/// The domain every node digest is computed under.
///
/// The version suffix is part of the domain rather than a field beside it: a
/// change to the preimage layout is a change of identity for every node, and
/// the two generations must not be comparable.
const NODE_DOMAIN: &[u8] = b"gandr.surface-syntax.node.v1";

/// The content identity of one node: a digest of its form and its content.
///
/// # Specification
/// - requires: nothing; the type is a carrier and admits any byte array.
/// - ensures: `Display` renders the lowercase hexadecimal of the bytes in
///   order, and `Debug` renders identically, because one identity read in two
///   notations in one log is harder to match by eye than it is worth.
/// - provides: an opaque, fixed-width name for a node's content. The
///   postcondition stays prose: the item is a type, and its rendering claim is
///   about the two implementations beside it, which a data specification's
///   `maintains` does not reach.
/// - fails: never.
/// - panics: none.
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
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        core::fmt::Display::fmt(self, f)
    }
}

/// The content identity of a node of `kind` spanning `text` over `children`.
///
/// # Specification
/// - requires: `text` is the fragment the node's span covers, and `children`
///   holds its immediate children's digests in the order the node carries them.
/// - ensures: equal `(kind, folded text, children)` triples give equal digests,
///   where the folded text is `text` exactly when the kind carries text and is
///   absent otherwise; the digest is independent of where in a source the node
///   sits, and of the arena the node will be laid out into.
/// - provides: the crate's only hashing entry point, so no node identity is
///   computed outside the domain or with a differently shaped preimage. The
///   postcondition stays prose: it is a law relating two calls' inputs to their
///   outputs, which no predicate over one call states, and the precondition is
///   a provenance claim about `text` and `children`.
/// - fails: never.
/// - panics: none.
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
///   count width or the field order moves it; the L3 residue is the set of
///   collisions a fold could admit, separated by two kinds over identical
///   children, by two sibling texts of equal total length split differently, by
///   reversed child order, and by a structural kind whose text differs.
/// - witness: `digest::tests::a_pinned_leaf_digest_is_stable`
/// - witness: `digest::tests::two_kinds_over_the_same_children_differ`
/// - witness: `digest::tests::sibling_texts_do_not_run_together`
/// - witness: `digest::tests::child_order_changes_the_digest`
/// - witness: `digest::tests::a_structural_kind_ignores_its_own_text`
#[inline]
#[must_use]
pub fn digest_of(
    kind: NodeKind,
    text: SourceFragment<'_>,
    children: &[NodeDigest],
) -> NodeDigest
{
    let mut hasher = blake3::Hasher::new();
    let _domain = hasher.update(NODE_DOMAIN);
    let _tag = hasher.update(&[u8::from(kind.tag())]);
    let child_count = u64::try_from(children.len()).unwrap_or(u64::MAX);
    let _count = hasher.update(&child_count.to_le_bytes());
    if bool::from(kind.carries_text()) {
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
    use crate::kind::NodeKind;
    use crate::span::SourceFragment;

    /// The digest of a childless node of `kind` whose fragment is `text`.
    ///
    /// # Specification
    /// - requires: `text` is the fragment the node covers, under the same
    ///   reading [`digest_of`] asks of it.
    /// - ensures: the digest of `kind` over `text` with no children.
    /// - provides: the childless case every rendering and collision fixture
    ///   below is written against.
    /// - panics: none.
    fn leaf(
        kind: NodeKind,
        text: SourceFragment<'_>,
    ) -> NodeDigest
    {
        digest_of(kind, text, &[])
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
        // The golden is external: it is `b3sum` over the fifty preimage bytes
        // this layout specifies — the domain string, the tag `0x06`, a
        // little-endian child count of zero, a little-endian text length of
        // five, and `value` — computed outside this crate, so a change to the
        // domain, the tag placement, a field width or the field order moves the
        // left side and not the right.
        assert_eq!(
            format!("{}", leaf(NodeKind::Name, SourceFragment::from("value"))),
            "3ccf68eac92cc64b9f5b595799ab9f1adfcfee552171c7c7fcdabc6acaee8de1",
            "the preimage layout is pinned against an external golden"
        );
    }

    #[test]
    fn two_kinds_over_the_same_children_differ()
    {
        let child = leaf(NodeKind::Name, SourceFragment::from("x"));
        let empty = SourceFragment::from("");

        assert_ne!(
            digest_of(NodeKind::Return, empty, &[child]),
            digest_of(NodeKind::Force, empty, &[child]),
            "the kind tag separates two forms over identical children"
        );
    }

    #[test]
    fn sibling_texts_do_not_run_together()
    {
        let empty = SourceFragment::from("");
        let split_early = [
            leaf(NodeKind::Name, SourceFragment::from("ab")),
            leaf(NodeKind::Name, SourceFragment::from("c")),
        ];
        let split_late = [
            leaf(NodeKind::Name, SourceFragment::from("a")),
            leaf(NodeKind::Name, SourceFragment::from("bc")),
        ];

        assert_ne!(
            digest_of(NodeKind::Application, empty, &split_early),
            digest_of(NodeKind::Application, empty, &split_late),
            "a length-prefixed text cannot be re-split across its siblings"
        );
    }

    #[test]
    fn child_order_changes_the_digest()
    {
        let empty = SourceFragment::from("");
        let first = leaf(NodeKind::Name, SourceFragment::from("f"));
        let second = leaf(NodeKind::Name, SourceFragment::from("x"));

        assert_ne!(
            digest_of(NodeKind::Application, empty, &[first, second]),
            digest_of(NodeKind::Application, empty, &[second, first]),
            "the fold is ordered, so an applied argument is not its own head"
        );
    }

    #[test]
    fn a_structural_kind_ignores_its_own_text()
    {
        assert_eq!(
            leaf(NodeKind::Module, SourceFragment::from("def a = b ;")),
            leaf(NodeKind::Module, SourceFragment::from("")),
            "a structural kind's identity does not read the bytes it spans"
        );
        assert_ne!(
            leaf(NodeKind::Name, SourceFragment::from("a")),
            leaf(NodeKind::Name, SourceFragment::from("b")),
            "a text leaf's identity is exactly its text"
        );
    }
}
