//! The node arena: [`SyntaxTree`], the [`Node`] it holds, and the
//! [`NodeIndex`] that addresses one by its layout block and its offset there.
//!
//! # Children are an index range, so the layout is level order by form
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
//! The root's children are laid out side by side after the root, and then each
//! child's descendants follow in level order, one child after another. A
//! top-level form's descendants are then one contiguous range
//! ([`SyntaxTree::descendants`]), which a stage keyed by form reads without a
//! walk. Whole-tree level order would spread a form's nodes over the arena, one
//! run per depth.
//!
//! # A position names its block
//!
//! The layout is cut into blocks ([`LayoutBlock`]): a root with its children,
//! then the descendants of each of its children with any, one block each. A
//! position is a block and an offset in it ([`BlockOffset`]), so a node of one
//! form keeps its position whatever another form holds. A table kept per node
//! keeps one segment per block, and a form's segment is its own.
//!
//! # Parent before child, and the invariant that follows
//!
//! Every child's position is strictly after its parent's, block first and then
//! offset, and a parse's root is the first offset of the first block. So a walk
//! in ascending position order visits every parent before any of its children
//! with no stack at all, a comparison of positions decides ancestry direction,
//! and a cycle is unrepresentable rather than checked for.
//!
//! # Out-of-range positions fail closed; in-range foreign ones do not
//!
//! Every lookup here is checked, so a position in a block the tree does not
//! hold, or past its block's end, resolves to nothing and a walk over it
//! yields no children rather than panicking.
//!
//! A position carries no tree provenance, though, so a position taken from
//! another tree — or kept across a re-parse — that happens to be in range names
//! whichever node now occupies it. That is the accepted cost of a bare index,
//! and the mitigation is that a position is never the identity that travels:
//! the cross-tree identity is the node's [`NodeKey`], its top-level form's
//! [`NodeDigest`] and its rank in that form, which is a function of content and
//! cannot be confused with an offset. A caller that needs to hold an identity
//! across trees holds the key.
//!
//! # Identity is per form
//!
//! Only a top-level form, a significant child of the root, has a digest: one
//! hash over a preorder serialization of its significant nodes, taken when the
//! tree is laid out. A node inside a form is keyed by that digest and its
//! preorder rank, and the whole tree's digest folds its forms'. A node below a
//! form has no content identity of its own.
//!
//! # Joined trees
//!
//! [`SyntaxTree::joined`] lays one tree's blocks after another's, over the text
//! that lays their sources end to end: the second tree's positions move up by
//! the first's block count and its spans by the first source's length, and the
//! join has one root per tree joined ([`SyntaxTree::roots`]). Every position of
//! the first tree names the same node in the join, so what was read of the
//! first tree by position stays true of the join. Each root's nodes keep their
//! layout, so an ascending scan still visits every parent before its children
//! and each form's descendants stay one block. The join's forms are the two
//! trees' forms in order, and its digest is the one a parse of the whole text
//! gives when its forms are those.

use alloc::vec::Vec;

use anodized::spec;

use crate::digest::NodeDigest;
use crate::digest::Preimage;
use crate::error::SyntaxError;
use crate::key::FormRank;
use crate::key::NodeKey;
use crate::label::NodeLabel;
use crate::mold::GrammarFingerprint;
use crate::span::ByteLength;
use crate::span::ByteOffset;
use crate::span::ByteSpan;
use crate::span::SourceFragment;
use crate::span::SourceText;

/// One block of a tree's layout: a root with its children side by side, or the
/// descendants of one of a root's children.
///
/// The blocks follow the layout's order, so the block of a top-level form's
/// descendants holds the form's whole subtree below the form itself.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LayoutBlock(u32);

impl From<usize> for LayoutBlock
{
    /// Read a `usize` as a block, saturating past `u32::MAX`, beyond any
    /// layout a builder lays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(block: usize) -> Self
    {
        Self(u32::try_from(block).unwrap_or(u32::MAX))
    }
}

impl From<LayoutBlock> for usize
{
    /// Read the block back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(block: LayoutBlock) -> Self
    {
        Self::try_from(block.0).unwrap_or(Self::MAX)
    }
}

/// A node's place within its layout block, counted from the block's first
/// node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BlockOffset(u32);

impl From<usize> for BlockOffset
{
    /// Read a `usize` as an offset, saturating past `u32::MAX`, beyond any
    /// block a builder lays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: usize) -> Self
    {
        Self(u32::try_from(offset).unwrap_or(u32::MAX))
    }
}

impl From<BlockOffset> for usize
{
    /// Read the offset back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: BlockOffset) -> Self
    {
        Self::try_from(offset.0).unwrap_or(Self::MAX)
    }
}

/// The position of one node inside one syntax tree: the layout block holding
/// it and its offset there.
///
/// Positions order as the layout does, block before block and offset before
/// offset within one, so an ascending scan visits every parent before its
/// children. A top-level form's descendants are one block, and a position
/// inside it names the form's node by the block and an offset the forms
/// around it leave alone.
///
/// A position is meaningful only in the tree it was read from: it carries no
/// tree provenance, so a position another tree also holds names whichever
/// node sits there. The identity that survives a tree is the node's
/// [`NodeKey`], and it is the one to hold across trees.
///
/// The block is the high half of one word and the offset the low half, so
/// the word's order is the layout's and the next offset in a block is the
/// next word.
#[repr(transparent)]
#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeIndex(u64);

impl NodeIndex
{
    /// The position at `offset` within `block`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(
        block: LayoutBlock,
        offset: BlockOffset,
    ) -> Self
    {
        let [o0, o1, o2, o3] = offset.0.to_le_bytes();
        let [b0, b1, b2, b3] = block.0.to_le_bytes();
        Self(u64::from_le_bytes([o0, o1, o2, o3, b0, b1, b2, b3]))
    }

    /// The layout block holding the node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn block(self) -> LayoutBlock
    {
        let [_, _, _, _, b0, b1, b2, b3] = self.0.to_le_bytes();
        LayoutBlock(u32::from_le_bytes([b0, b1, b2, b3]))
    }

    /// The node's offset within its block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn offset(self) -> BlockOffset
    {
        let [o0, o1, o2, o3, _, _, _, _] = self.0.to_le_bytes();
        BlockOffset(u32::from_le_bytes([o0, o1, o2, o3]))
    }

    /// The same offset in the block as far past `past` as this one lies past
    /// the first, as a join moves the second tree's positions past the first's
    /// blocks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn moved(
        self,
        past: LayoutBlock,
    ) -> Self
    {
        Self::at(
            LayoutBlock(self.block().0.saturating_add(past.0)),
            self.offset(),
        )
    }
}

impl core::fmt::Debug for NodeIndex
{
    /// Write the position as its block and its offset, the fields a derived
    /// form would write.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes `NodeIndex` with the block and the offset as fields.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes a write-only sink; neither
    ///   emitted bytes nor the sink's failure state can be read back by a
    ///   predicate, and replaying writes changes the observed sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position in a block past the first writes that
    ///   block and that offset, so a swapped or dropped half changes the text.
    /// - witness: `tree::tests::a_position_debugs_as_its_block_and_offset`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("NodeIndex")
            .field("block", &self.block())
            .field("offset", &self.offset())
            .finish()
    }
}

impl core::fmt::Display for NodeIndex
{
    /// Write the position as its block and its offset, `block.offset`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the block, a full stop and the offset, padded as one
    ///   string, so the width and fill options the caller set apply to it.
    /// - provides: the position a diagnostic or a test message names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes a write-only sink; neither
    ///   emitted bytes nor the sink's failure state can be read back by a
    ///   predicate, and replaying writes changes the observed sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first position, an ordinary one and the last a
    ///   layout can hold keep their block and offset and the requested fill and
    ///   width. A rejecting sink separates propagation from swallowed errors.
    /// - witness: `tree::tests::formatters_preserve_padding_options`
    /// - witness: `tree::tests::formatters_propagate_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.pad(&alloc::format!("{}.{}", self.block().0, self.offset().0))
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

/// One node: its label, the source it covers, and the arena range its
/// children occupy.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Node
{
    /// What this node is.
    label: NodeLabel,
    /// The bytes of the source this node covers.
    span: ByteSpan,
    /// The position of this node's first child, strictly above its own.
    first_child: NodeIndex,
    /// How many children follow that position.
    child_count: ChildCount,
}

impl Node
{
    /// What the node is: a molded form or tile, inserted grout, layout, or the
    /// root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn label(&self) -> NodeLabel
    {
        self.label
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
    ///   children, and `span` was validated against the source the tree is
    ///   built over. Only [`TreeBuilder`] establishes all of this, which is why
    ///   the constructor is crate-private.
    /// - ensures: the node carries exactly the parts offered, unchecked and
    ///   unnormalized.
    /// - provides: the one node shape the layout walk assembles a tree from.
    /// - fails: never — parts violating the precondition yield a node whose
    ///   walks are wrong rather than a refusal, which is what confines the
    ///   constructor to one caller.
    /// - panics: none.
    ///
    /// [`TreeBuilder`]: crate::TreeBuilder
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a depth-four layout supplies interior nodes and
    ///   leaves; exact labels, fragments and child ranges detect dropped or
    ///   substituted constructor parts.
    /// - witness: `build::tests::children_are_contiguous_and_in_source_order`
    /// - witness: `build::tests::a_node_names_the_fragment_it_spans`
    #[spec(ensures: |ret| ret.first_child.0 == first_child.0 && ret.child_count.0 == child_count.0
        && matches!(ret.label.const_eq(label), crate::ConstEquality::Equal)
        && matches!(ret.span.const_eq(span), crate::ConstEquality::Equal))]
    #[inline]
    pub(crate) const fn new(
        label: NodeLabel,
        span: ByteSpan,
        first_child: NodeIndex,
        child_count: ChildCount,
    ) -> Self
    {
        Self {
            label,
            span,
            first_child,
            child_count,
        }
    }
}

/// A forward walk over a contiguous range of positions within one layout
/// block.
///
/// A node's children and a top-level form's descendants are such a range, so
/// one type serves both walks.
///
/// # Specification
/// - ensures: the walk yields a contiguous ascending range of one block's
///   offsets and remains exhausted after its end.
/// - executable: none — this type has no entry or return boundary; the
///   construction and observation methods state its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — empty, nonzero and maximum-ended ranges are observed
///   through exact indices and remaining sizes, separating endpoint shifts,
///   gaps and resumed exhaustion.
/// - witness: `tree::tests::index_ranges_advance_exactly_and_stay_exhausted`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeIndices
{
    /// The position the walk yields next.
    next: NodeIndex,
    /// The position one past the last the walk yields, in the same block.
    end: NodeIndex,
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty range yields no positions and has exact zero
    ///   size before and after repeated polls; a spurious element or nonzero
    ///   hint changes those observations.
    /// - witness: `tree::tests::index_ranges_advance_exactly_and_stay_exhausted`
    #[spec(ensures: |ret| ret.next.0 == ret.end.0)]
    #[inline]
    const fn empty() -> Self
    {
        Self {
            next: NodeIndex(0_u64),
            end: NodeIndex(0_u64),
        }
    }

    /// The walk over `count` offsets of `first`'s block from `first`'s,
    /// saturating at the last offset a block holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run(
        first: NodeIndex,
        count: ChildCount,
    ) -> Self
    {
        let end = BlockOffset(
            first
                .offset()
                .0
                .saturating_add(u32::try_from(count.0).unwrap_or(u32::MAX)),
        );
        Self {
            next: first,
            end: NodeIndex::at(first.block(), end),
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
    /// - provides: the forward order every walk over a block sees, which in a
    ///   layout by form is source order among siblings.
    /// - fails: never — exhaustion is the iterator's own absence, not a
    ///   failure.
    /// - panics: none. The advance saturates, so a range ending at the last
    ///   offset a block holds stops rather than overflowing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, nonzero-origin and maximum-ended ranges are
    ///   observed by exact yielded indices and remaining sizes before and after
    ///   each step; repeated exhaustion detects restarting, skipped endpoints,
    ///   double advancement and arithmetic overflow.
    /// - witness: `tree::tests::index_ranges_advance_exactly_and_stay_exhausted`
    #[inline]
    #[spec(
        captures: cursor = self.next,
        ensures: |ret| ret == (cursor < self.end).then_some(cursor)
            && self.next == if cursor < self.end { NodeIndex(cursor.0.saturating_add(1)) } else { cursor },
    )]
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.next >= self.end {
            return None;
        }
        let position = self.next;
        self.next = NodeIndex(self.next.0.saturating_add(1_u64));

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact remaining cardinality is checked at each step
    ///   of empty, ordinary and maximum-ended ranges. Both hint endpoints and
    ///   `ExactSizeIterator::len` detect loose bounds and premature exhaustion.
    /// - witness: `tree::tests::index_ranges_advance_exactly_and_stay_exhausted`
    #[inline]
    #[spec(ensures: |ret| ret.0 == usize::try_from(self.end.0.saturating_sub(self.next.0)).unwrap_or(usize::MAX) && ret.1 == Some(ret.0))]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let remaining =
            usize::try_from(self.end.0.saturating_sub(self.next.0)).unwrap_or(usize::MAX);

        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for NodeIndices
{
}

/// A forward walk over every position of a tree, in its layout's order: block
/// after block, each block's offsets in turn.
///
/// # Specification
/// - ensures: every position the tree holds, once, ascending, and nothing past
///   its end.
/// - executable: none — this type has no entry or return boundary;
///   [`SyntaxTree::positions`] and the walk's methods state its obligations.
///
/// # Adequacy
/// - hypothesis: L3 — empty, one-block and many-block layouts are walked whole
///   and compared position by position with the blocks they hold.
/// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
/// - witness: `build::tests::each_form_s_descendants_are_one_range`
#[derive(Clone, Debug)]
pub struct Positions<'tree>
{
    /// Where each block starts among the tree's nodes, in layout order.
    starts: &'tree [NodeCount],
    /// How many nodes the tree holds.
    count: usize,
    /// How many positions the walk has yielded.
    yielded: usize,
    /// The block the next position lies in.
    block: usize,
}

impl Iterator for Positions<'_>
{
    type Item = NodeIndex;

    /// Yield the next position of the tree.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the position of the node after the last one yielded, as its
    ///   block and its offset there; nothing once every node is yielded.
    /// - provides: the stackless whole-tree walk, every parent before its
    ///   children.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Positions`].
    /// - witness: `build::tests::each_form_s_descendants_are_one_range`
    #[inline]
    #[spec(
        captures: before = self.yielded,
        ensures: |ret| ret.is_some() == (before < self.count)
            && self.yielded == if before < self.count { before.saturating_add(1) } else { before },
    )]
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.yielded >= self.count {
            return None;
        }
        while self
            .starts
            .get(self.block.saturating_add(1))
            .is_some_and(|next| next.0 <= self.yielded)
        {
            self.block = self.block.saturating_add(1);
        }
        let start = self.starts.get(self.block).map_or(0, |start| start.0);
        let position = NodeIndex::at(
            LayoutBlock::from(self.block),
            BlockOffset::from(self.yielded.saturating_sub(start)),
        );
        self.yielded = self.yielded.saturating_add(1);

        Some(position)
    }

    /// Report how many positions remain.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the exact count of positions the walk will still yield.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Positions`].
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    #[inline]
    #[spec(ensures: |ret| ret == (self.count.saturating_sub(self.yielded), Some(self.count.saturating_sub(self.yielded))))]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let remaining = self.count.saturating_sub(self.yielded);

        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for Positions<'_>
{
}

/// A concrete syntax tree: its source, its grammar, and its nodes laid out by
/// form.
///
/// A parse's root is at position zero, its children follow side by side, and
/// then each child's descendants follow in level order, one child after
/// another. The root with its children is one layout block, and each child's
/// descendants are the next, so a top-level form's descendants are one block.
/// A join's second root and its blocks follow the first tree's.
///
/// # Specification
/// - ensures: every stored child range lies within one block and strictly above
///   its parent; each top-level form's descendants are one block; source and
///   grammar describe the same immutable layout.
/// - executable: none — this type has no entry or return boundary; the
///   construction and observation methods state its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — a depth-four tree and an empty layout are observed
///   through root resolution, exact child lists, fragments and grammar; shifts,
///   reordered siblings and dropped provenance change the answers.
/// - witness: `build::tests::every_child_sits_above_its_parent`
/// - witness: `build::tests::children_are_contiguous_and_in_source_order`
/// - witness: `build::tests::a_tree_records_its_grammar`
/// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxTree<'source>
{
    /// The text every span in this tree is read against.
    source: SourceText<'source>,
    /// The grammar whose mold table every [`MoldId`](crate::MoldId) in this
    /// tree indexes.
    grammar: GrammarFingerprint,
    /// The nodes, each root's laid out by form — parents before children,
    /// siblings adjacent, each form's descendants together — and the roots'
    /// runs in source order.
    nodes: Vec<Node>,
    /// Where each layout block starts among `nodes`, ascending: a position's
    /// block names its start here and its offset counts from it.
    starts: Vec<NodeCount>,
    /// The positions of the roots, in source order.
    roots: Vec<NodeIndex>,
    /// The top-level forms, their digests, each node's form and rank, and
    /// the whole tree's digest.
    index: FormIndex,
}

/// Where `position` lies among `count` nodes whose blocks start at `starts`:
/// the count of nodes laid out before it, or nothing for a block or an offset
/// the layout does not hold.
///
/// Every lookup by position runs through this, so it carries no checked
/// wrapper of its own: [`SyntaxTree::node`] and the layout's own
/// specification state what it yields.
///
/// # Specification
/// trivial.
#[inline]
fn flat(
    starts: &[NodeCount],
    count: NodeCount,
    position: NodeIndex,
) -> Option<NodeCount>
{
    let block = usize::from(position.block());
    let start = starts.get(block)?.0;
    let end = starts
        .get(block.saturating_add(1))
        .map_or(count.0, |end| end.0);
    let at = start.checked_add(usize::from(position.offset()))?;
    (at < end).then_some(NodeCount(at))
}

impl<'source> SyntaxTree<'source>
{
    /// The tree over `source` under `grammar` holding `nodes` already laid out
    /// by form.
    ///
    /// # Specification
    /// - requires: `nodes` is empty or a layout by form — the root first, then
    ///   its children, then each child's descendants as one block, every node's
    ///   children occupying the range of one block its `first_child` and
    ///   `child_count` name, and every such range strictly above the node's own
    ///   position; `starts` holds each block's first node, ascending, the first
    ///   zero; every span in `nodes` was validated against `source`. The only
    ///   producer that establishes all of this is [`TreeBuilder::finish`],
    ///   which is why the constructor is crate-private rather than public.
    /// - ensures: the tree holds exactly `nodes`, in the order given, over
    ///   `source` and under `grammar`; the layout is adopted rather than
    ///   checked or re-derived.
    /// - provides: the seam between the builder's layout walk and the finished
    ///   tree.
    /// - fails: never — a layout violating the precondition yields a tree whose
    ///   walks are wrong rather than a refusal, which is what confines the
    ///   constructor to one caller.
    /// - panics: none.
    ///
    /// [`TreeBuilder::finish`]: crate::TreeBuilder::finish
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated layouts preserve source, grammar
    ///   and exact node order. Root lookup, child ranges and fragment observers
    ///   separate dropped fields, reordering and a spurious empty root.
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    /// - witness: `build::tests::the_root_is_the_first_position`
    /// - witness: `build::tests::children_are_contiguous_and_in_source_order`
    /// - witness: `build::tests::a_node_names_the_fragment_it_spans`
    #[spec(ensures: |ref ret| matches!(ret.source.const_eq(source), crate::ConstEquality::Equal)
        && matches!(ret.grammar.const_eq(grammar), crate::ConstEquality::Equal)
        && ret.nodes.iter().enumerate().all(|(position, node)| node.child_count.0 == 0_usize
            || flat(&ret.starts, NodeCount(ret.nodes.len()), node.first_child).is_some_and(|first| first.0 > position
                && flat(
                    &ret.starts,
                    NodeCount(ret.nodes.len()),
                    NodeIndex::at(node.first_child.block(), BlockOffset::from(usize::from(node.first_child.offset()).saturating_add(node.child_count.0).saturating_sub(1))),
                ).is_some())))]
    #[inline]
    pub(crate) fn from_layout(
        source: SourceText<'source>,
        grammar: GrammarFingerprint,
        nodes: Vec<Node>,
        starts: Vec<NodeCount>,
    ) -> Self
    {
        let index = index_forms(source, &nodes, &starts);
        let roots = if nodes.is_empty() {
            Vec::new()
        }
        else {
            Vec::from([NodeIndex::default()])
        };
        Self {
            source,
            grammar,
            nodes,
            starts,
            roots,
            index,
        }
    }

    /// The tree laying `after`'s nodes after `before`'s, over `source`, the
    /// text that lays their sources end to end.
    ///
    /// # Specification
    /// - requires: nothing; a source that does not lay the two texts end to
    ///   end, and trees of two grammars, are refused.
    /// - ensures: on success, the tree over `source` under the two trees'
    ///   grammar holding `before`'s nodes and blocks as they are, then
    ///   `after`'s, each block moved up by `before`'s block count — its child
    ///   range likewise — and each span by `before`'s source length; its roots
    ///   are `before`'s then `after`'s, moved likewise; its forms are
    ///   `before`'s then `after`'s, moved likewise, each with its digest, so
    ///   every node keeps its key; its digest is the one a parse of `source`
    ///   gives when its forms are those.
    /// - provides: a closure's parse kept across edits with the document's
    ///   parse laid after it, so a position read in the closure's tree names
    ///   the same node in the join.
    /// - fails: [`SyntaxError::GrammarsDisagree`] for trees of two grammars;
    ///   [`SyntaxError::SourcesDisagree`] for a `source` that is not `before`'s
    ///   text then `after`'s.
    /// - panics: none.
    /// - intension: one copy of each node and of each form's index entry; the
    ///   forms are not hashed again.
    ///
    /// # Errors
    /// [`SyntaxError::GrammarsDisagree`] and [`SyntaxError::SourcesDisagree`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two trees joined keep every node, fragment and key at
    ///   the moved position, the join's digest is the whole text's parse's, and
    ///   a text out of order and a grammar of its own are refused by name.
    /// - witness: `build::tests::a_join_lays_the_second_tree_after_the_first`
    /// - witness: `build::tests::a_join_refuses_a_text_or_a_grammar_of_its_own`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref joined) => joined.nodes.len() == before.nodes.len().saturating_add(after.nodes.len())
            && joined.starts.len() == before.starts.len().saturating_add(after.starts.len())
            && joined.roots.len() == before.roots.len().saturating_add(after.roots.len())
            && joined.index.forms.len() == before.index.forms.len().saturating_add(after.index.forms.len())
            && joined.nodes.get(.. before.nodes.len()) == Some(before.nodes.as_slice())
            && joined.source == source
            && joined.grammar == before.grammar,
        Err(SyntaxError::GrammarsDisagree { before: first, after: second }) =>
            first == before.grammar && second == after.grammar && first != second,
        Err(SyntaxError::SourcesDisagree { at }) => usize::from(at) == <&str>::from(before.source).len(),
        Err(_) => false,
    })]
    #[inline]
    pub fn joined(
        before: &SyntaxTree<'_>,
        after: &SyntaxTree<'_>,
        source: SourceText<'source>,
    ) -> Result<Self, SyntaxError>
    {
        if before.grammar != after.grammar {
            return Err(SyntaxError::GrammarsDisagree {
                before: before.grammar,
                after: after.grammar,
            });
        }
        let text = <&str>::from(source);
        let first = <&str>::from(before.source);
        let at = first.len();
        if text.get(.. at) != Some(first) || text.get(at ..) != Some(<&str>::from(after.source)) {
            return Err(SyntaxError::SourcesDisagree {
                at: ByteOffset::from(at),
            });
        }
        let past = LayoutBlock::from(before.starts.len());
        let by = ByteLength::from(at);
        let mut nodes = Vec::with_capacity(before.nodes.len().saturating_add(after.nodes.len()));
        nodes.extend_from_slice(&before.nodes);
        nodes.extend(after.nodes.iter().map(|node| Node {
            span: node.span.shifted(by),
            first_child: node.first_child.moved(past),
            ..*node
        }));
        let mut starts = Vec::with_capacity(before.starts.len().saturating_add(after.starts.len()));
        starts.extend_from_slice(&before.starts);
        starts.extend(
            after
                .starts
                .iter()
                .map(|start| NodeCount(start.0.saturating_add(before.nodes.len()))),
        );
        let mut roots = Vec::with_capacity(before.roots.len().saturating_add(after.roots.len()));
        roots.extend_from_slice(&before.roots);
        roots.extend(after.roots.iter().map(|root| root.moved(past)));
        let index = joined_index((&before.index, &after.index), source, &nodes, past);

        Ok(Self {
            source,
            grammar: before.grammar,
            nodes,
            starts,
            roots,
            index,
        })
    }

    /// The content digest of the whole tree: its root's label and text and
    /// its forms' digests, in order.
    ///
    /// # Specification
    /// - requires: nothing; the tree need not hold any node.
    /// - ensures: a digest for a tree holding a node, nothing for an empty
    ///   tree.
    /// - provides: the identity a reparse is compared by, which neither layout
    ///   nor documentation reaches.
    /// - fails: yields nothing for an empty tree.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two builds of one source agree, an empty layout
    ///   yields nothing.
    /// - witness: `build::tests::two_builds_of_one_source_agree_digest_by_digest`
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() != self.nodes.is_empty())]
    pub const fn digest(&self) -> Option<NodeDigest>
    {
        self.index.digest
    }

    /// The positions of the top-level forms: the root's significant
    /// children, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn forms(&self) -> &[NodeIndex]
    {
        self.index.forms.as_slice()
    }

    /// The positions of the descendants of the top-level form at `form`, the
    /// one layout block they make up, and nothing for a position no top-level
    /// form stands at.
    ///
    /// # Specification
    /// - requires: nothing — a position this tree does not hold is admissible
    ///   input.
    /// - ensures: for a top-level form, every node reachable from it but
    ///   itself, each once, in ascending order, and no other; nothing
    ///   otherwise.
    /// - provides: a form's nodes as one block, which a stage keyed by form
    ///   reads without walking the tree.
    /// - fails: yields nothing for a position that is no top-level form.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each form of the corpus's sources reaches exactly its
    ///   block, and the forms' blocks with the root and its children cover the
    ///   layout once.
    /// - witness: `build::tests::each_form_s_descendants_are_one_range`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.as_ref().is_some() == self.index.forms.binary_search(&form).is_ok()
        && ret.as_ref().is_none_or(|walk| walk.next <= walk.end))]
    pub fn descendants(
        &self,
        form: NodeIndex,
    ) -> Option<NodeIndices>
    {
        let (slot, rank) = self
            .index
            .ranks
            .get(self.flat(form)?.0)
            .copied()
            .flatten()?;
        if rank != FormRank::default() {
            return None;
        }
        self.index.ranges.get(slot.0).cloned()
    }

    /// The cross-tree key of the node at `position`: its top-level form's
    /// digest and its preorder rank among that form's significant nodes.
    ///
    /// # Specification
    /// - requires: nothing — a position this tree does not hold is admissible
    ///   input.
    /// - ensures: for a significant node inside a top-level form, the form's
    ///   digest and the node's rank, the form's own root ranked zero; nothing
    ///   for the root, for layout and documentation and the nodes they hold,
    ///   and for a position the tree does not hold.
    /// - provides: the key a table that outlives one parse files a node under,
    ///   which an edit to another form, layout or documentation leaves alone.
    /// - fails: yields nothing where the node has no key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-form source keys each form's root at rank zero
    ///   and its nested nodes in preorder; a layout edit and an edit to the
    ///   other form keep a key, an edit inside the form changes it, and the
    ///   root and layout have none.
    /// - witness: `build::tests::keys_rank_a_forms_nodes_in_preorder`
    /// - witness: `build::tests::keys_survive_layout_and_another_forms_edit`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_none_or(|key| self.flat(position).and_then(|at| self.index.ranks.get(at.0).copied().flatten())
        .and_then(|(slot, rank)| self.index.digests.get(slot.0).map(|&form| (form, rank)))
        == Some((key.form(), key.rank()))))]
    pub fn key(
        &self,
        position: NodeIndex,
    ) -> Option<NodeKey>
    {
        let (slot, rank) = self
            .index
            .ranks
            .get(self.flat(position)?.0)
            .copied()
            .flatten()?;
        let form = self.index.digests.get(slot.0).copied()?;

        Some(NodeKey::new(form, rank))
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

    /// The fingerprint of the grammar whose mold table this tree's labels
    /// index; a consumer resolves a [`MoldId`](crate::MoldId) only against a
    /// grammar with this fingerprint.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn grammar(&self) -> GrammarFingerprint
    {
        self.grammar
    }

    /// The position of the first root, which the layout fixes at the first
    /// offset of the first block.
    ///
    /// # Specification
    /// - requires: nothing; the tree need not hold any node.
    /// - ensures: the first offset of the first block, whatever the tree holds
    ///   — the layout fixes the first root there rather than storing it.
    /// - provides: the entry point of every walk of a parse. An empty tree
    ///   answers with a position it does not hold, which [`SyntaxTree::node`]
    ///   resolves to nothing; the alternative would be an absence every caller
    ///   of a non-empty tree would have to discharge. A walk of a join starts
    ///   from each of [`SyntaxTree::roots`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — populated and empty layouts both designate the first
    ///   position; the former resolves its root while the latter does not. A
    ///   shifted root or fabricated empty node changes these observations.
    /// - witness: `build::tests::the_root_is_the_first_position`
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    #[spec(ensures: |ret| ret.0 == 0_u64)]
    #[inline]
    #[must_use]
    pub const fn root(&self) -> NodeIndex
    {
        NodeIndex::at(LayoutBlock(0), BlockOffset(0))
    }

    /// The positions of the roots, in source order: a parse's one root, one
    /// root per tree a join laid end to end, and none for an empty tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn roots(&self) -> &[NodeIndex]
    {
        self.roots.as_slice()
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
    ///   whose block the tree holds and whose offset falls within that block.
    /// - provides: the single checked lookup [`SyntaxTree::children`] and
    ///   [`SyntaxTree::fragment`] are both built on, so the out-of-range case
    ///   is decided once rather than at each caller.
    /// - fails: yields nothing for a block the tree does not hold and for an
    ///   offset past its block. A position from another tree that this tree
    ///   also holds resolves to this tree's node there; positions carry no tree
    ///   provenance, and the module header states why the digest rather than
    ///   the position is the identity that travels.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one bounds comparison per block, separated by
    ///   the boundary pair of the last node and the position past it, the first
    ///   asserted as an exact label and the second asserted absent.
    /// - witness: `build::tests::the_last_position_holds_a_node`
    /// - witness: `build::tests::a_position_past_the_arena_holds_no_node`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_none_or(|_| usize::from(position.block()) < self.starts.len()))]
    pub fn node(
        &self,
        position: NodeIndex,
    ) -> Option<&Node>
    {
        self.nodes.get(self.flat(position)?.0)
    }

    /// Where `position` lies among this tree's nodes, or nothing for a
    /// position it does not hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn flat(
        &self,
        position: NodeIndex,
    ) -> Option<NodeCount>
    {
        flat(&self.starts, NodeCount(self.nodes.len()), position)
    }

    /// How many nodes each layout block holds, block by block.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one count per block, in block order, the counts summing to
    ///   [`Self::node_count`].
    /// - provides: the shape a table kept per block widens to.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — an iterator; the witness reads it against the
    ///   positions it covers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each form's block holds the count of its walk, and
    ///   the counts cover the layout once.
    /// - witness: `build::tests::each_form_s_descendants_are_one_range`
    #[must_use]
    #[inline]
    pub fn blocks(&self) -> impl ExactSizeIterator<Item = NodeCount> + '_
    {
        let count = self.nodes.len();
        self.starts.iter().enumerate().map(move |(block, start)| {
            let end = self
                .starts
                .get(block.saturating_add(1))
                .map_or(count, |end| end.0);
            NodeCount(end.saturating_sub(start.0))
        })
    }

    /// Every position in the tree, in its layout's order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every position the tree holds, once, in ascending order,
    ///   which under the layout by form visits every parent before any of its
    ///   children.
    /// - provides: the stackless whole-tree walk the layout is chosen for.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and seven-node layouts expose the entire
    ///   ordered index sequence and exact remaining size. Omitted zero, a
    ///   skipped position and an inclusive end differ from these observations.
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    /// - witness: `build::tests::the_root_is_the_first_position`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.len() == self.nodes.len())]
    pub fn positions(&self) -> Positions<'_>
    {
        self.positions_from(LayoutBlock(0))
    }

    /// Every position from block `first` on, in the layout's order.
    ///
    /// # Specification
    /// - requires: nothing; a block past the last yields nothing.
    /// - ensures: the suffix of [`Self::positions`] whose positions lie in
    ///   block `first` or after it, reached without walking the blocks before.
    /// - provides: the walk over the forms a resumed lowering adds after the
    ///   blocks it already read.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-form tree walked from each of its blocks, and
    ///   from one past the last, yields the whole walk's suffix from there.
    /// - witness: `build::tests::a_walk_from_a_block_is_the_suffix_from_it`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.len() == self.nodes.len().saturating_sub(self.starts.get(usize::from(first)).map_or(self.nodes.len(), |start| start.0)))]
    pub fn positions_from(
        &self,
        first: LayoutBlock,
    ) -> Positions<'_>
    {
        let block = usize::from(first);
        Positions {
            starts: &self.starts,
            count: self.nodes.len(),
            yielded: self
                .starts
                .get(block)
                .map_or(self.nodes.len(), |start| start.0),
            block,
        }
    }

    /// The positions of the immediate children of the node at `position`.
    ///
    /// # Specification
    /// - requires: nothing — a position this tree does not hold is admissible
    ///   input.
    /// - ensures: the children's positions in the order the node carries them,
    ///   each strictly above `position` under the layout by form; the empty
    ///   walk for a leaf and for a position the tree does not hold, which is
    ///   the fail-closed reading.
    /// - provides: the edge relation every walk over the tree follows.
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
    #[spec(ensures: |ret| self.node(position).map_or_else(
        || ret.next == ret.end,
        |node| ret == NodeIndices::run(node.first_child, node.child_count),
    ))]
    pub fn children(
        &self,
        position: NodeIndex,
    ) -> NodeIndices
    {
        self.node(position).map_or_else(NodeIndices::empty, |node| {
            NodeIndices::run(node.first_child, node.child_count)
        })
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

    /// The source fragment `span` covers, read against the text this tree was
    /// built over.
    ///
    /// # Specification
    /// - requires: nothing — a span past the text is admissible input.
    /// - ensures: exactly the bytes `span` covers; nothing for a span the text
    ///   does not hold or that does not fall on character boundaries.
    /// - provides: the spelling of a form several nodes write, as an import's
    ///   module path `text.greet` is three.
    /// - fails: yields nothing for a span the text does not hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a span over several nodes reads their bytes as
    ///   written, and one past the text reads nothing.
    /// - witness: `build::tests::a_span_names_the_fragment_it_covers_2687`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.source.fragment(span).ok())]
    pub fn spanned(
        &self,
        span: ByteSpan,
    ) -> Option<SourceFragment<'source>>
    {
        self.source.fragment(span).ok()
    }
}

/// Where a form stands in its tree's form list.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FormSlot(usize);

/// What a tree knows of its top-level forms.
///
/// # Specification
/// - ensures: one digest and one block walk per form, index for index; one rank
///   entry per node.
/// - executable: none — [`index_forms`] states the shape it builds.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FormIndex
{
    /// The positions of the root's significant children, the top-level forms,
    /// in source order.
    forms: Vec<NodeIndex>,
    /// Each form's digest, index for index with `forms`.
    digests: Vec<NodeDigest>,
    /// Each form's descendants, index for index with `forms`: the walk over
    /// the one layout block they make up, empty for a form with no children.
    ranges: Vec<NodeIndices>,
    /// Per node, in the order of the tree's nodes, the slot of the form
    /// holding the node and its rank there; nothing for the root and for
    /// layout, documentation and what they hold.
    ranks: Vec<Option<(FormSlot, FormRank)>>,
    /// The whole tree's digest; nothing for an empty tree.
    digest: Option<NodeDigest>,
}

/// The top-level forms of `nodes` laid out by form over `source`, their
/// digests, each node's form and preorder rank among that form's significant
/// nodes, and the whole tree's digest.
///
/// # Specification
/// - requires: `nodes` is empty or a layout by form whose blocks start at
///   `starts` and whose spans were validated against `source`, as
///   [`SyntaxTree::from_layout`] asks.
/// - ensures: the forms are the root's significant children in order, each with
///   the digest of its preorder serialization — every significant node
///   reachable from the form through significant nodes, each as its label, its
///   significant child count and, when its label carries text, its text; such a
///   node holds its form's slot and preorder rank, the form's root first, and
///   every other node holds nothing. Each form's walk is the whole block its
///   first child opens, and empty for a form with no children. The tree's
///   digest is the root's label, text and form count with the forms' digests in
///   order, and is absent exactly when `nodes` is empty.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// Each node is pushed at most once: the layout is a tree, and the walk
/// descends from each form's root along child ranges only.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SyntaxTree::key`] and [`SyntaxTree::digest`].
/// - witness: `build::tests::keys_rank_a_forms_nodes_in_preorder`
/// - witness: `build::tests::two_builds_of_one_source_agree_digest_by_digest`
/// - witness: `build::tests::each_form_s_descendants_are_one_range`
#[spec(ensures: |ret| ret.ranks.len() == nodes.len()
    && ret.digests.len() == ret.forms.len()
    && ret.ranges.len() == ret.forms.len()
    && ret.digest.is_some() != nodes.is_empty()
    && ret.forms.iter().enumerate().all(|(slot, &form)| {
        flat(starts, NodeCount(nodes.len()), form).and_then(|at| ret.ranks.get(at.0).copied().flatten())
            == Some((FormSlot(slot), FormRank::default()))
    }))]
fn index_forms(
    source: SourceText<'_>,
    nodes: &[Node],
    starts: &[NodeCount],
) -> FormIndex
{
    let mut index = FormIndex::default();
    index.ranks.resize(nodes.len(), None);
    let Some(root) = nodes.first()
    else {
        return index;
    };
    let significant = |position: usize| {
        nodes
            .get(position)
            .is_some_and(|node| bool::from(node.label.significance()))
    };
    let text = |node: &Node| {
        source
            .fragment(node.span)
            .unwrap_or_else(|_refused| SourceFragment::from(""))
    };
    // A node's children lie in one block, so they are one run of the flat
    // layout from where its first child lies.
    let first_of = |node: &Node| {
        if node.child_count.0 == 0 {
            None
        }
        else {
            flat(starts, NodeCount(nodes.len()), node.first_child).map(|first| first.0)
        }
    };
    let mut preimage = Preimage::default();
    let mut pending: Vec<usize> = Vec::new();
    let tops = NodeIndices::run(root.first_child, root.child_count);
    for top in tops {
        let Some(position) = flat(starts, NodeCount(nodes.len()), top).map(|at| at.0)
        else {
            continue;
        };
        if !significant(position) {
            continue;
        }
        let slot = FormSlot(index.forms.len());
        index.forms.push(top);
        let range = nodes.get(position).map_or_else(NodeIndices::empty, |node| {
            if node.child_count.0 == 0 {
                return NodeIndices::empty();
            }
            let block = usize::from(node.first_child.block());
            let length = starts.get(block).map_or(0, |start| {
                starts
                    .get(block.saturating_add(1))
                    .map_or(nodes.len(), |end| end.0)
                    .saturating_sub(start.0)
            });
            NodeIndices::run(
                NodeIndex::at(node.first_child.block(), BlockOffset(0)),
                ChildCount(length),
            )
        });
        index.ranges.push(range);
        preimage.open_form();
        let mut rank = 0_u32;
        pending.push(position);
        while let Some(at) = pending.pop() {
            let Some(node) = nodes.get(at)
            else {
                continue;
            };
            if let Some(entry) = index.ranks.get_mut(at) {
                *entry = Some((slot, FormRank::from(rank)));
            }
            rank = rank.saturating_add(1_u32);
            let before = pending.len();
            if let Some(start) = first_of(node) {
                pending.extend(
                    (start .. start.saturating_add(node.child_count.0))
                        .rev()
                        .filter(|&child| significant(child)),
                );
            }
            preimage.node(
                node.label,
                text(node),
                ChildCount(pending.len().saturating_sub(before)),
            );
        }
        index.digests.push(preimage.hash());
    }
    preimage.open_tree();
    preimage.node(root.label, text(root), ChildCount(index.digests.len()));
    for &form in &index.digests {
        preimage.digest(form);
    }
    index.digest = Some(preimage.hash());

    index
}

/// The form index of `nodes` over `source`, the join of the trees `before` and
/// `after` index, `after`'s blocks moved up past `before`'s, to start at
/// `past`.
///
/// # Specification
/// - requires: `nodes` is `before`'s tree's nodes then `after`'s, whose blocks
///   are moved up to start at `past`, the count of `before`'s tree's blocks.
/// - ensures: `before`'s forms, digests, walks and ranks, then `after`'s, each
///   form and each walk moved up past `past` and each rank's slot moved past
///   `before`'s; the digest folds the first node's label and text, the form
///   count and every form's digest in order, as [`index_forms`] folds a
///   parse's, and is absent exactly when `nodes` is empty.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`SyntaxTree::joined`].
/// - witness: `build::tests::a_join_lays_the_second_tree_after_the_first`
#[spec(ensures: |ret| ret.ranks.len() == before.ranks.len().saturating_add(after.ranks.len())
    && ret.digests.len() == ret.forms.len()
    && ret.forms.len() == before.forms.len().saturating_add(after.forms.len())
    && ret.digest.is_some() != nodes.is_empty())]
fn joined_index(
    (before, after): (&FormIndex, &FormIndex),
    source: SourceText<'_>,
    nodes: &[Node],
    past: LayoutBlock,
) -> FormIndex
{
    let slots = before.forms.len();
    let mut forms = Vec::with_capacity(slots.saturating_add(after.forms.len()));
    forms.extend_from_slice(&before.forms);
    forms.extend(after.forms.iter().map(|form| form.moved(past)));
    let mut digests = Vec::with_capacity(forms.len());
    digests.extend_from_slice(&before.digests);
    digests.extend_from_slice(&after.digests);
    let mut ranges = Vec::with_capacity(forms.len());
    ranges.extend_from_slice(&before.ranges);
    ranges.extend(after.ranges.iter().map(|walk| NodeIndices {
        next: walk.next.moved(past),
        end: walk.end.moved(past),
    }));
    let mut ranks = Vec::with_capacity(before.ranks.len().saturating_add(after.ranks.len()));
    ranks.extend_from_slice(&before.ranks);
    ranks.extend(
        after
            .ranks
            .iter()
            .map(|held| held.map(|(slot, rank)| (FormSlot(slot.0.saturating_add(slots)), rank))),
    );
    let digest = nodes.first().map(|root| {
        let mut preimage = Preimage::default();
        preimage.open_tree();
        preimage.node(
            root.label,
            source
                .fragment(root.span)
                .unwrap_or_else(|_refused| SourceFragment::from("")),
            ChildCount(digests.len()),
        );
        for &form in &digests {
            preimage.digest(form);
        }
        preimage.hash()
    });

    FormIndex {
        forms,
        digests,
        ranges,
        ranks,
        digest,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::BlockOffset;
    use super::ChildCount;
    use super::LayoutBlock;
    use super::NodeIndex;
    use super::NodeIndices;
    use super::SyntaxTree;
    use crate::GrammarFingerprint;
    use crate::SourceText;

    #[test]
    fn index_ranges_advance_exactly_and_stay_exhausted()
    {
        let block = LayoutBlock::from(4_usize);
        for (start, count) in [
            (0_usize, 0_usize),
            (3, 0),
            (3, 3),
            (usize::try_from(u32::MAX - 1).unwrap_or(usize::MAX), 1),
        ] {
            let first = NodeIndex::at(block, BlockOffset::from(start));
            let mut range = NodeIndices::run(first, ChildCount(count));
            for step in 0 .. count {
                let remaining = count.saturating_sub(step);
                assert_eq!(range.size_hint(), (remaining, Some(remaining)));
                assert_eq!(range.len(), remaining);
                assert_eq!(
                    range.next(),
                    Some(NodeIndex::at(
                        block,
                        BlockOffset::from(start.saturating_add(step))
                    ))
                );
            }
            for _ in 0_u8 .. 2_u8 {
                assert_eq!(range.next(), None);
                assert_eq!(range.size_hint(), (0, Some(0)));
                assert_eq!(range.len(), 0);
            }
        }
        let mut empty = NodeIndices::empty();
        assert_eq!(empty.next(), None);
        assert_eq!(empty.size_hint(), (0, Some(0)));
    }

    #[test]
    fn an_empty_layout_has_no_resolvable_positions()
    {
        let source = SourceText::from("");
        let grammar = GrammarFingerprint::from(7_u64);
        let tree = SyntaxTree::from_layout(source, grammar, Vec::new(), Vec::new());
        assert_eq!(tree.source(), source);
        assert_eq!(tree.grammar(), grammar);
        assert_eq!(tree.root(), NodeIndex::default());
        assert_eq!(tree.node(tree.root()), None);
        assert_eq!(tree.positions().next(), None);
        assert_eq!(tree.blocks().len(), 0);
        assert_eq!(tree.children(tree.root()).next(), None);
        assert_eq!(tree.fragment(tree.root()), None);
        assert_eq!(tree.digest(), None);
        assert!(tree.forms().is_empty());
        assert_eq!(tree.key(tree.root()), None);
    }

    #[test]
    fn formatters_preserve_padding_options()
    {
        let last = usize::try_from(u32::MAX).unwrap_or(usize::MAX);
        for (block, offset) in [(0_usize, 0_usize), (2, 17), (last, 9)] {
            let position = NodeIndex::at(LayoutBlock::from(block), BlockOffset::from(offset));
            assert_eq!(
                alloc::format!("{position:*>24}"),
                alloc::format!("{:*>24}", alloc::format!("{block}.{offset}"))
            );
        }
    }

    #[test]
    fn a_position_debugs_as_its_block_and_offset()
    {
        let last = usize::try_from(u32::MAX).unwrap_or(usize::MAX);
        for (block, offset) in [(0_usize, 0_usize), (2, 17), (last, 9)] {
            let (block, offset) = (LayoutBlock::from(block), BlockOffset::from(offset));
            assert_eq!(
                alloc::format!("{:?}", NodeIndex::at(block, offset)),
                alloc::format!("NodeIndex {{ block: {block:?}, offset: {offset:?} }}")
            );
        }
    }

    #[test]
    fn formatters_propagate_sink_failure()
    {
        use core::fmt::Write as _;
        assert!(
            crate::test_support::RefusingSink
                .write_fmt(format_args!("{}", NodeIndex::default()))
                .is_err()
        );
    }
}
