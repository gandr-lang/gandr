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
//! Every child's position is strictly above its parent's, and a parse's root is
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
//! [`SyntaxTree::joined`] lays one tree's nodes after another's, over the text
//! that lays their sources end to end: the second tree's positions move up by
//! the first's node count and its spans by the first source's length, and the
//! join has one root per tree joined ([`SyntaxTree::roots`]). Every position of
//! the first tree names the same node in the join, so what was read of the
//! first tree by position stays true of the join. Each root's nodes keep their
//! level order, so an ascending scan still visits every parent before its
//! children. The join's forms are the two trees' forms in order, and its digest
//! is the one a parse of the whole text gives when its forms are those.
//!
//! # Level-order layout
//!
//! A node names its children as a contiguous range of strictly higher arena
//! positions: two fields per node and no second vector. A post-order arena,
//! which a bottom-up builder produces naturally, cannot give a node's children
//! a contiguous range, because the second child's subtree sits between the
//! first child and the second; level order can. The root is position zero,
//! every child sits above its parent, so an ascending scan visits parents first
//! and an index comparison decides ancestry direction.

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

/// The arena position of one node inside one syntax tree.
///
/// A position is meaningful only in the tree it was read from: it carries no
/// tree provenance, so an in-range position from another tree names whichever
/// node sits there. The identity that survives a tree is the node's
/// [`NodeKey`], and it is the one to hold across trees.
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
    /// - executable: none — the formatter exposes a write-only sink; neither
    ///   emitted bytes nor the sink's failure state can be read back by a
    ///   predicate, and replaying writes changes the observed sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, an ordinary index and the maximum host index
    ///   retain their exact decimal value and requested fill, width and sign. A
    ///   rejecting sink separates propagation from swallowed errors.
    /// - witness: `tree::tests::formatters_preserve_numeric_options`
    /// - witness: `tree::tests::formatters_propagate_sink_failure`
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

/// A forward walk over a contiguous range of arena positions.
///
/// One type serves both walks the arena offers — a node's children and a whole
/// tree — because in a level-order arena both are ranges.
///
/// # Specification
/// - ensures: the walk yields a contiguous ascending range and remains
///   exhausted after its end.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty range yields no positions and has exact zero
    ///   size before and after repeated polls; a spurious element or nonzero
    ///   hint changes those observations.
    /// - witness: `tree::tests::index_ranges_advance_exactly_and_stay_exhausted`
    #[spec(ensures: |ret| ret.next == ret.end)]
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
        ensures: |ret| ret == (cursor < self.end).then_some(NodeIndex(cursor))
            && self.next == if cursor < self.end { cursor.saturating_add(1) } else { cursor },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact remaining cardinality is checked at each step
    ///   of empty, ordinary and maximum-ended ranges. Both hint endpoints and
    ///   `ExactSizeIterator::len` detect loose bounds and premature exhaustion.
    /// - witness: `tree::tests::index_ranges_advance_exactly_and_stay_exhausted`
    #[inline]
    #[spec(ensures: |ret| ret == (self.end.saturating_sub(self.next), Some(self.end.saturating_sub(self.next))))]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let remaining = self.end.saturating_sub(self.next);

        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for NodeIndices
{
}

/// A concrete syntax tree: its source, its grammar, and its nodes in level
/// order.
///
/// A parse's root is at position zero; a join's second root follows the first
/// tree's nodes.
///
/// # Specification
/// - ensures: every stored child range is contiguous and strictly above its
///   parent; source and grammar describe the same immutable layout.
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
    /// The nodes, each root's in level order — parents before children,
    /// siblings adjacent — and the roots' runs in source order.
    nodes: Vec<Node>,
    /// The positions of the roots, in source order.
    roots: Vec<NodeIndex>,
    /// The top-level forms, their digests, each node's form and rank, and
    /// the whole tree's digest.
    index: FormIndex,
}

impl<'source> SyntaxTree<'source>
{
    /// The tree over `source` under `grammar` holding `nodes` already laid out
    /// in level order.
    ///
    /// # Specification
    /// - requires: `nodes` is empty or a level-order layout — the root first,
    ///   every node's children occupying the contiguous range its `first_child`
    ///   and `child_count` name, and every such range strictly above the node's
    ///   own position; every span in `nodes` was validated against `source`.
    ///   The only producer that establishes all of this is
    ///   [`TreeBuilder::finish`], which is why the constructor is crate-private
    ///   rather than public.
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
    #[spec(ensures: |ref ret| {
        let mut nodes = ret.nodes.as_slice();
        let count = nodes.len();
        let mut position = 0_usize;
        let mut valid = matches!(ret.source.const_eq(source), crate::ConstEquality::Equal)
            && matches!(ret.grammar.const_eq(grammar), crate::ConstEquality::Equal);
        while let Some((node, tail)) = nodes.split_first() {
            let first = node.first_child.0;
            let children = node.child_count.0;
            valid = valid && (children == 0_usize
                || (first > position && first <= count && children <= count.saturating_sub(first)));
            position = position.saturating_add(1_usize);
            nodes = tail;
        }
        valid
    })]
    #[inline]
    pub(crate) fn from_layout(
        source: SourceText<'source>,
        grammar: GrammarFingerprint,
        nodes: Vec<Node>,
    ) -> Self
    {
        let index = index_forms(source, &nodes);
        let roots = if nodes.is_empty() {
            Vec::new()
        }
        else {
            Vec::from([NodeIndex(0_usize)])
        };
        Self {
            source,
            grammar,
            nodes,
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
    ///   grammar holding `before`'s nodes as they are, then `after`'s, each
    ///   moved up by `before`'s node count — its child range likewise — and its
    ///   span by `before`'s source length; its roots are `before`'s then
    ///   `after`'s, moved likewise; its forms are `before`'s then `after`'s,
    ///   moved likewise, each with its digest, so every node keeps its key; its
    ///   digest is the one a parse of `source` gives when its forms are those.
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
        let moved = before.nodes.len();
        let by = ByteLength::from(at);
        let mut nodes = Vec::with_capacity(moved.saturating_add(after.nodes.len()));
        nodes.extend_from_slice(&before.nodes);
        nodes.extend(after.nodes.iter().map(|node| Node {
            span: node.span.shifted(by),
            first_child: NodeIndex(node.first_child.0.saturating_add(moved)),
            ..*node
        }));
        let mut roots = Vec::with_capacity(before.roots.len().saturating_add(after.roots.len()));
        roots.extend_from_slice(&before.roots);
        roots.extend(
            after
                .roots
                .iter()
                .map(|root| NodeIndex(root.0.saturating_add(moved))),
        );
        let index = joined_index(
            (&before.index, &after.index),
            source,
            &nodes,
            NodeIndex(moved),
        );

        Ok(Self {
            source,
            grammar: before.grammar,
            nodes,
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
    #[spec(ensures: |ret| ret.is_none_or(|key| self.index.ranks.get(position.0).copied().flatten()
        .and_then(|(slot, rank)| self.index.digests.get(slot.0).map(|&form| (form, rank)))
        == Some((key.form(), key.rank()))))]
    pub fn key(
        &self,
        position: NodeIndex,
    ) -> Option<NodeKey>
    {
        let (slot, rank) = self.index.ranks.get(position.0).copied().flatten()?;
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

    /// The position of the first root, which the level-order layout fixes at
    /// zero.
    ///
    /// # Specification
    /// - requires: nothing; the tree need not hold any node.
    /// - ensures: position zero, whatever the tree holds — the level-order
    ///   layout fixes the first root there rather than storing it.
    /// - provides: the entry point of every walk of a parse. An empty tree
    ///   answers with a position it does not hold, which [`SyntaxTree::node`]
    ///   resolves to nothing; the alternative would be an absence every caller
    ///   of a non-empty tree would have to discharge. A walk of a join starts
    ///   from each of [`SyntaxTree::roots`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — populated and empty layouts both designate zero; the
    ///   former resolves its root while the latter does not. A shifted root or
    ///   fabricated empty node changes these observations.
    /// - witness: `build::tests::the_root_is_the_first_position`
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    #[spec(ensures: |ret| ret.0 == 0_usize)]
    #[inline]
    #[must_use]
    pub const fn root(&self) -> NodeIndex
    {
        NodeIndex(0_usize)
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
    ///   label and the second asserted absent.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and seven-node layouts expose the entire
    ///   ordered index sequence and exact remaining size. Omitted zero, a
    ///   skipped position and an inclusive end differ from these observations.
    /// - witness: `tree::tests::an_empty_layout_has_no_resolvable_positions`
    /// - witness: `build::tests::the_root_is_the_first_position`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.next == 0 && ret.end == self.nodes.len())]
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
        |node| ret.next == node.first_child.0 && ret.end == node.first_child.0.saturating_add(node.child_count.0),
    ))]
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
/// - ensures: one digest per form, index for index; one rank entry per node.
/// - executable: none — [`index_forms`] states the shape it builds.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FormIndex
{
    /// The positions of the root's significant children, the top-level forms,
    /// in source order.
    forms: Vec<NodeIndex>,
    /// Each form's digest, index for index with `forms`.
    digests: Vec<NodeDigest>,
    /// Per position, the slot of the form holding the node and its rank
    /// there; nothing for the root and for layout, documentation and what
    /// they hold.
    ranks: Vec<Option<(FormSlot, FormRank)>>,
    /// The whole tree's digest; nothing for an empty tree.
    digest: Option<NodeDigest>,
}

/// The top-level forms of a level-order `nodes` over `source`, their digests,
/// each node's form and preorder rank among that form's significant nodes, and
/// the whole tree's digest.
///
/// # Specification
/// - requires: `nodes` is empty or a level-order layout whose spans were
///   validated against `source`, as [`SyntaxTree::from_layout`] asks.
/// - ensures: the forms are the root's significant children in order, each with
///   the digest of its preorder serialization — every significant node
///   reachable from the form through significant nodes, each as its label, its
///   significant child count and, when its label carries text, its text; such a
///   node holds its form's slot and preorder rank, the form's root first, and
///   every other position holds nothing. The tree's digest is the root's label,
///   text and form count with the forms' digests in order, and is absent
///   exactly when `nodes` is empty.
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
#[spec(ensures: |ret| ret.ranks.len() == nodes.len()
    && ret.digests.len() == ret.forms.len()
    && ret.digest.is_some() != nodes.is_empty()
    && ret.forms.iter().enumerate().all(|(slot, &form)| {
        ret.ranks.get(form.0).copied().flatten() == Some((FormSlot(slot), FormRank::default()))
    }))]
fn index_forms(
    source: SourceText<'_>,
    nodes: &[Node],
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
    let mut preimage = Preimage::default();
    let mut pending: Vec<usize> = Vec::new();
    let first = root.first_child.0;
    for position in first .. first.saturating_add(root.child_count.0) {
        if !significant(position) {
            continue;
        }
        let slot = FormSlot(index.forms.len());
        index.forms.push(NodeIndex(position));
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
            let start = node.first_child.0;
            let before = pending.len();
            pending.extend(
                (start .. start.saturating_add(node.child_count.0))
                    .rev()
                    .filter(|&child| significant(child)),
            );
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
/// `after` index, `after`'s nodes moved up to start at `moved`.
///
/// # Specification
/// - requires: `nodes` is `before`'s tree's nodes then `after`'s, moved up by
///   `moved`, the position past `before`'s tree's last node.
/// - ensures: `before`'s forms, digests and ranks, then `after`'s, each form
///   and each rank's slot moved past `before`'s; the digest folds the first
///   node's label and text, the form count and every form's digest in order, as
///   [`index_forms`] folds a parse's, and is absent exactly when `nodes` is
///   empty.
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
    moved: NodeIndex,
) -> FormIndex
{
    let slots = before.forms.len();
    let mut forms = Vec::with_capacity(slots.saturating_add(after.forms.len()));
    forms.extend_from_slice(&before.forms);
    forms.extend(
        after
            .forms
            .iter()
            .map(|form| NodeIndex(form.0.saturating_add(moved.0))),
    );
    let mut digests = Vec::with_capacity(forms.len());
    digests.extend_from_slice(&before.digests);
    digests.extend_from_slice(&after.digests);
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
        ranks,
        digest,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::NodeIndex;
    use super::NodeIndices;
    use super::SyntaxTree;
    use crate::GrammarFingerprint;
    use crate::SourceText;

    #[test]
    fn index_ranges_advance_exactly_and_stay_exhausted()
    {
        for (start, end) in [
            (0_usize, 0_usize),
            (3, 3),
            (3, 6),
            (usize::MAX.saturating_sub(1), usize::MAX),
        ] {
            let mut range = NodeIndices { next: start, end };
            for index in start .. end {
                let remaining = end.saturating_sub(index);
                assert_eq!(range.size_hint(), (remaining, Some(remaining)));
                assert_eq!(range.len(), remaining);
                assert_eq!(range.next(), Some(NodeIndex(index)));
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
        let tree = SyntaxTree::from_layout(source, grammar, Vec::new());
        assert_eq!(tree.source(), source);
        assert_eq!(tree.grammar(), grammar);
        assert_eq!(tree.root(), NodeIndex(0));
        assert_eq!(tree.node(tree.root()), None);
        assert_eq!(tree.positions().next(), None);
        assert_eq!(tree.children(tree.root()).next(), None);
        assert_eq!(tree.fragment(tree.root()), None);
        assert_eq!(tree.digest(), None);
        assert!(tree.forms().is_empty());
        assert_eq!(tree.key(tree.root()), None);
    }

    #[test]
    fn formatters_preserve_numeric_options()
    {
        for count in [0_usize, 17, usize::MAX] {
            assert_eq!(
                alloc::format!("{:*>+24}", NodeIndex(count)),
                alloc::format!("{count:*>+24}")
            );
        }
    }

    #[test]
    fn formatters_propagate_sink_failure()
    {
        use core::fmt::Write as _;
        assert!(
            crate::test_support::RefusingSink
                .write_fmt(format_args!("{}", NodeIndex(0)))
                .is_err()
        );
    }
}
