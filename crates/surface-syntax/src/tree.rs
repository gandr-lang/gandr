//! The flat node arena: [`SyntaxTree`], the [`Node`] it holds, and the
//! [`NodeIndex`] that addresses one.
//!
//! # Children are an index range, so the layout is level-order
//!
//! A node names its children as a contiguous range of arena positions rather
//! than as a list of ids stored somewhere else. That costs two fields per node
//! and no second vector, and it makes "the children of this node" a range walk
//! over memory the parent walk already touched.
//!
//! Contiguity is what fixes the layout. A post-order arena — children before
//! parents, as a bottom-up builder naturally produces — cannot give a node's
//! children a contiguous range: the second child's subtree sits between the
//! first child and the second. Laying the tree out in level order does, and it
//! comes with the invariant in the next paragraph for free.
//!
//! # Parent before child, and the invariant that follows
//!
//! Every child's position is strictly above its parent's, and the root is
//! position zero. So a walk in ascending index order visits every parent before
//! any of its children with no stack at all, an index comparison decides
//! ancestry direction, and a cycle is unrepresentable rather than checked for.
//!
//! # Out-of-range positions fail closed; in-range foreign ones do not
//!
//! Every lookup here is checked, so a position at or above the node count
//! resolves to nothing and a walk over it yields no children rather than
//! panicking.
//!
//! A position carries no tree provenance, though, so a position taken from
//! another tree — or kept across a re-parse — that happens to be in range names
//! whichever node now occupies it. That is the accepted cost of a bare index,
//! and the mitigation is that a position is never the identity that travels:
//! the cross-tree identity is the node's [`NodeDigest`], which is a function of
//! content and cannot be confused with an offset. A caller that needs to hold
//! an identity across trees holds the digest.

use alloc::vec::Vec;

use anodized::spec;

use crate::digest::NodeDigest;
use crate::kind::NodeKind;
use crate::span::ByteSpan;
use crate::span::SourceFragment;
use crate::span::SourceText;

/// The arena position of one node inside one syntax tree.
///
/// A position is meaningful only in the tree it was read from: it carries no
/// tree provenance, so an in-range position from another tree names whichever
/// node sits there. The identity that survives a tree is the node's
/// [`NodeDigest`], and it is the one to hold across trees.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeIndex(usize);

impl From<usize> for NodeIndex
{
    /// Read a `usize` as an arena position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<NodeIndex> for usize
{
    /// Read the position back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: NodeIndex) -> Self
    {
        position.0
    }
}

impl core::fmt::Display for NodeIndex
{
    /// Write the position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried position through the `usize` rendering, so
    ///   the width and fill options the caller set apply to it.
    /// - provides: the arena position a diagnostic or a test message names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.fmt(f)
    }
}

/// A number of nodes in one tree.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeCount(usize);

impl From<usize> for NodeCount
{
    /// Read a `usize` as a node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<NodeCount> for usize
{
    /// Read the node count back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: NodeCount) -> Self
    {
        count.0
    }
}

/// A number of immediate children of one node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildCount(usize);

impl From<usize> for ChildCount
{
    /// Read a `usize` as a child count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<ChildCount> for usize
{
    /// Read the child count back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ChildCount) -> Self
    {
        count.0
    }
}

/// One node: its form, the source it covers, its content identity, and the
/// arena range its children occupy.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Node
{
    /// The form this node is.
    kind: NodeKind,
    /// The bytes of the source this node covers.
    span: ByteSpan,
    /// The content identity of this node and everything under it.
    digest: NodeDigest,
    /// The position of this node's first child, strictly above its own.
    first_child: NodeIndex,
    /// How many children follow that position.
    child_count: ChildCount,
}

impl Node
{
    /// The node's form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> NodeKind
    {
        self.kind
    }

    /// The bytes of the source the node covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }

    /// The node's content identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> NodeDigest
    {
        self.digest
    }

    /// How many immediate children the node has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn child_count(&self) -> ChildCount
    {
        self.child_count
    }

    /// The node with these parts, for the builder that lays a tree out.
    ///
    /// # Specification
    /// - requires: `first_child` is strictly above the position this node will
    ///   itself occupy, and the `child_count` positions from it are this node's
    ///   children; `span` was validated against the source the tree is built
    ///   over, and `digest` was folded over that span's text and those
    ///   children's digests. Only [`TreeBuilder`] establishes all of this,
    ///   which is why the constructor is crate-private.
    /// - ensures: the node carries exactly the parts offered, unchecked and
    ///   unnormalized.
    /// - provides: the one node shape the layout walk assembles a tree from.
    /// - fails: never — parts violating the precondition yield a node whose
    ///   walks are wrong rather than a refusal, which is what confines the
    ///   constructor to one caller.
    /// - panics: none.
    ///
    /// [`TreeBuilder`]: crate::TreeBuilder
    #[inline]
    pub(crate) const fn new(
        kind: NodeKind,
        span: ByteSpan,
        digest: NodeDigest,
        first_child: NodeIndex,
        child_count: ChildCount,
    ) -> Self
    {
        Self {
            kind,
            span,
            digest,
            first_child,
            child_count,
        }
    }
}

/// A forward walk over a contiguous range of arena positions.
///
/// One type serves both walks the arena offers — a node's children and a whole
/// tree — because in a level-order arena both are ranges.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeIndices
{
    /// The next position the walk yields.
    next: usize,
    /// The position one past the last the walk yields.
    end: usize,
}

impl NodeIndices
{
    /// The walk that yields nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a walk whose next position is already its end, so it yields
    ///   nothing and reports a remaining count of zero.
    /// - provides: the fail-closed answer [`SyntaxTree::children`] gives for a
    ///   position the tree does not hold, so an absent node reads as a leaf
    ///   rather than as a panic.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    const fn empty() -> Self
    {
        Self {
            next: 0_usize,
            end: 0_usize,
        }
    }
}

impl Iterator for NodeIndices
{
    type Item = NodeIndex;

    /// Yield the next position in the range.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the positions of the range in strictly ascending order, one
    ///   per call, and nothing once the end is reached; the walk stays
    ///   exhausted afterwards.
    /// - provides: the forward order every walk over the arena sees, which in a
    ///   level-order layout is source order among siblings and
    ///   parent-before-child over a whole tree.
    /// - fails: never — exhaustion is the iterator's own absence, not a
    ///   failure.
    /// - panics: none. The advance saturates, so a range ending at `usize::MAX`
    ///   stops rather than overflowing.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.next >= self.end {
            return None;
        }
        let position = NodeIndex(self.next);
        self.next = self.next.saturating_add(1_usize);

        Some(position)
    }

    /// Report how many positions remain.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an exact bound — the same count as both halves — equal to the
    ///   number of positions the walk will still yield.
    /// - provides: the exactness [`ExactSizeIterator`] and every collecting
    ///   caller rely on to size an allocation once.
    /// - fails: never.
    /// - panics: none. The remaining count saturates, so an exhausted walk
    ///   reports zero rather than underflowing.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let remaining = self.end.saturating_sub(self.next);

        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for NodeIndices
{
}

/// A concrete syntax tree: the source it was parsed from and its nodes, laid
/// out in level order with the root at position zero.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxTree<'source>
{
    /// The text every span in this tree is read against.
    source: SourceText<'source>,
    /// The nodes, in level order: parents before children, siblings adjacent.
    nodes: Vec<Node>,
}

impl<'source> SyntaxTree<'source>
{
    /// The tree over `source` holding `nodes` already laid out in level order.
    ///
    /// # Specification
    /// - requires: `nodes` is a level-order layout — the root first, every
    ///   node's children occupying the contiguous range its `first_child` and
    ///   `child_count` name, and every such range strictly above the node's own
    ///   position; every span in `nodes` was validated against `source`. The
    ///   only producer that establishes all of this is [`TreeBuilder::finish`],
    ///   which is why the constructor is crate-private rather than public.
    /// - ensures: the tree holds exactly `nodes`, in the order given, over
    ///   `source`; the layout is adopted rather than checked or re-derived.
    /// - provides: the seam between the builder's layout walk and the finished
    ///   tree. This stays a `const fn` without `#[spec]`: the pinned `anodized`
    ///   expansion calls a non-const evaluator (`E0015`). The precondition is a
    ///   provenance claim about `nodes`, which no predicate over one call
    ///   states.
    /// - fails: never — a layout violating the precondition yields a tree whose
    ///   walks are wrong rather than a refusal, which is what confines the
    ///   constructor to one caller.
    /// - panics: none.
    ///
    /// [`TreeBuilder::finish`]: crate::TreeBuilder::finish
    #[inline]
    pub(crate) const fn from_layout(
        source: SourceText<'source>,
        nodes: Vec<Node>,
    ) -> Self
    {
        Self { source, nodes }
    }

    /// The text every span in this tree is read against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> SourceText<'source>
    {
        self.source
    }

    /// The position of the root, which the level-order layout fixes at zero.
    ///
    /// # Specification
    /// - requires: nothing; the tree need not hold any node.
    /// - ensures: position zero, whatever the tree holds — the level-order
    ///   layout fixes the root there rather than storing it.
    /// - provides: the entry point of every walk. An empty tree answers with a
    ///   position it does not hold, which [`SyntaxTree::node`] resolves to
    ///   nothing; the alternative would be an absence every caller of a
    ///   non-empty tree would have to discharge.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> NodeIndex
    {
        NodeIndex(0_usize)
    }

    /// How many nodes the tree holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_count(&self) -> NodeCount
    {
        NodeCount(self.nodes.len())
    }

    /// The node at `position`, or nothing when this tree holds no such
    /// position.
    ///
    /// # Specification
    /// - requires: nothing — a position this tree does not hold is admissible
    ///   input, including one carried over from another tree.
    /// - ensures: the node this tree lays out at `position`, for every position
    ///   below the node count.
    /// - provides: the single checked lookup [`SyntaxTree::children`] and
    ///   [`SyntaxTree::fragment`] are both built on, so the out-of-range case
    ///   is decided once rather than at each caller.
    /// - fails: yields nothing at or above the node count. A position from
    ///   another tree that is nevertheless in range resolves to this tree's
    ///   node there; positions carry no tree provenance, and the module header
    ///   states why the digest rather than the position is the identity that
    ///   travels.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one bounds comparison, separated by the boundary
    ///   pair `node_count - 1` / `node_count`, the first asserted as an exact
    ///   node kind and the second asserted absent.
    /// - witness: `build::tests::the_last_position_holds_a_node`
    /// - witness: `build::tests::a_position_past_the_arena_holds_no_node`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.nodes.get(position.0))]
    pub fn node(
        &self,
        position: NodeIndex,
    ) -> Option<&Node>
    {
        self.nodes.get(position.0)
    }

    /// Every position in the tree, in level order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every position the tree holds, once, in ascending order,
    ///   which under the level-order layout visits every parent before any of
    ///   its children.
    /// - provides: the stackless whole-tree walk the layout is chosen for.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn positions(&self) -> NodeIndices
    {
        NodeIndices {
            next: 0_usize,
            end: self.nodes.len(),
        }
    }

    /// The positions of the immediate children of the node at `position`.
    ///
    /// # Specification
    /// - requires: nothing — a position this tree does not hold is admissible
    ///   input.
    /// - ensures: the children's positions in the order the node carries them,
    ///   each strictly above `position` under the level-order layout; the empty
    ///   walk for a leaf and for a position the tree does not hold, which is
    ///   the fail-closed reading.
    /// - provides: the edge relation every walk over the tree follows. The
    ///   postcondition's strictly-above half holds only under the layout
    ///   precondition [`SyntaxTree::from_layout`] adopts without checking, so
    ///   asserting it would turn that documented wrong walk into a panic; the
    ///   range half alone is the body restated, so the line stays prose and the
    ///   witnesses below carry it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three decision surfaces (the lookup, the range start,
    ///   the range end) separated by a node with children, a leaf, and a
    ///   position one past the last node, each asserted as an exact position
    ///   list; the parent-before-child invariant is asserted over every node of
    ///   a tree of depth four, with the edge count asserted so the walk cannot
    ///   pass vacuously.
    /// - witness: `build::tests::children_are_contiguous_and_in_source_order`
    /// - witness: `build::tests::a_leaf_has_no_children`
    /// - witness: `build::tests::a_position_past_the_arena_has_no_children`
    /// - witness: `build::tests::every_child_sits_above_its_parent`
    #[inline]
    #[must_use]
    pub fn children(
        &self,
        position: NodeIndex,
    ) -> NodeIndices
    {
        let Some(node) = self.node(position)
        else {
            return NodeIndices::empty();
        };
        let first = node.first_child.0;

        NodeIndices {
            next: first,
            end: first.saturating_add(node.child_count.0),
        }
    }

    /// The source fragment the node at `position` covers.
    ///
    /// # Specification
    /// - requires: nothing — a position this tree does not hold is admissible
    ///   input.
    /// - ensures: exactly the bytes the node's span covers, which resolve
    ///   because the builder validated the span against this same source before
    ///   minting the node.
    /// - provides: the lexeme a diagnostic quotes and a lowering reads a name
    ///   from.
    /// - fails: yields nothing for a position the tree does not hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two decision surfaces (the position lookup and the
    ///   span read) separated by a text leaf whose fragment is asserted exactly
    ///   and by a position one past the last node, asserted absent.
    /// - witness: `build::tests::a_node_names_the_fragment_it_spans`
    /// - witness: `build::tests::a_position_past_the_arena_names_no_fragment`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| {
        ret == self.node(position).and_then(|node| self.source.fragment(node.span).ok())
    })]
    pub fn fragment(
        &self,
        position: NodeIndex,
    ) -> Option<SourceFragment<'source>>
    {
        let node = self.node(position)?;

        self.source.fragment(node.span).ok()
    }
}
