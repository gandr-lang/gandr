//! A run of a tree's top-level children cut out with their blocks
//! ([`TreeSlice`]), and a tree laid out again from such runs
//! ([`SyntaxTree::assembled`]).
//!
//! The descendants of a top-level child are one block, so some top-level
//! children with their blocks are one part of the tree's nodes after the
//! root's block. A slice holds such a part. Its spans count from an anchor,
//! and its child ranges count from its first block. A later tree over a text
//! that holds the same bytes at another anchor takes the slice up with one copy
//! of each node: each span moves by the new anchor, and each child range moves
//! by the blocks before the slice. Each form keeps its digest, so the
//! assembled tree hashes one digest per form and no node.

use alloc::vec::Vec;
use core::ops::Range;

use anodized::spec;

use super::BlockOffset;
use super::BlockStarts;
use super::ChildCount;
use super::FormIndex;
use super::FormSlot;
use super::LayoutBlock;
use super::Node;
use super::NodeCount;
use super::NodeIndex;
use super::NodeIndices;
use super::SyntaxTree;
use crate::digest::NodeDigest;
use crate::digest::Preimage;
use crate::error::SyntaxError;
use crate::key::FormRank;
use crate::label::NodeLabel;
use crate::mold::GrammarFingerprint;
use crate::span::ByteLength;
use crate::span::ByteOffset;
use crate::span::ByteSpan;
use crate::span::SourceFragment;
use crate::span::SourceText;

/// Some top-level children of a tree, with the blocks of their descendants,
/// cut out of the tree so that a later tree takes them up whole.
///
/// # Specification
/// - ensures: the children are in source order; each span counts from the
///   anchor the slice was cut at; each child range counts from the slice's
///   first block; one rank entry per child and then one per node; one digest
///   and one walk per form.
/// - executable: none — this data type has no call boundary;
///   [`SyntaxTree::slice`] and [`SyntaxTree::assembled`] carry the executable
///   clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a tree cut into slices at each split of its top-level
///   children and assembled again equals the tree; two trees' slices laid end
///   to end equal the tree of the two texts. A slice that drops a block, a rank
///   or a digest changes the assembled tree.
/// - witness: `build::tests::a_tree_cut_into_slices_assembles_to_itself`
/// - witness: `build::tests::a_slice_moves_with_its_anchor`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TreeSlice
{
    /// The top-level children, in source order.
    children: Vec<Node>,
    /// The nodes of the children's blocks, block after block.
    nodes: Vec<Node>,
    /// Where each block starts among `nodes`.
    starts: Vec<NodeCount>,
    /// Per child and then per node, the slot of the form that holds the node
    /// among the slice's forms, and the node's rank there.
    ranks: Vec<Option<(FormSlot, FormRank)>>,
    /// Where each form stands among `children`.
    forms: Vec<BlockOffset>,
    /// Each form's digest, form for form.
    digests: Vec<NodeDigest>,
    /// Each form's descendants, form for form, with the block counted from the
    /// slice's first block; empty for a form with no children.
    ranges: Vec<NodeIndices>,
    /// The furthest end of a span, counted from the anchor.
    extent: ByteOffset,
}

impl TreeSlice
{
    /// The top-level children, in source order, each span counted from the
    /// anchor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn children(&self) -> &[Node]
    {
        &self.children
    }

    /// The children of the first top-level child that end at or before
    /// `before`, counted from the anchor: the comments a form holds from the
    /// text before its own start.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the longest run of the first child's children, from its
    ///   first, whose spans each end at or before `before`; nothing for a slice
    ///   with no children or a first child with none.
    /// - provides: the documentation a form takes from the text before it,
    ///   which a commit of that text finds at its root.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a form with a documentation child before its start
    ///   yields that child alone; a bound before the child yields nothing.
    /// - witness: `build::tests::a_slice_names_the_comments_its_first_form_leads_with`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.len() <= self.nodes.len())]
    pub fn leading(
        &self,
        before: ByteOffset,
    ) -> &[Node]
    {
        let Some(first) = self.children.first()
        else {
            return &[];
        };
        if first.child_count.0 == 0 {
            return &[];
        }
        let blocks = BlockStarts::new(&self.starts, NodeCount(self.nodes.len()));
        let Some(start) = blocks.flat(first.first_child)
        else {
            return &[];
        };
        let held = self
            .nodes
            .get(start.0 .. start.0.saturating_add(first.child_count.0))
            .unwrap_or_default();
        let count = held
            .iter()
            .take_while(|child| child.span.end() <= before)
            .count();
        held.get(.. count).unwrap_or_default()
    }
}

impl<'source> SyntaxTree<'source>
{
    /// The children of the tree's first root, in source order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the nodes the first root's child range names; nothing for a
    ///   tree with no node.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`SyntaxTree::slice`], whose ordinals count these
    ///   children.
    /// - witness: `build::tests::a_tree_cut_into_slices_assembles_to_itself`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.len() <= self.nodes.len())]
    pub fn top_level(&self) -> &[Node]
    {
        let Some(root) = self.nodes.first()
        else {
            return &[];
        };
        let blocks = BlockStarts::new(&self.starts, NodeCount(self.nodes.len()));
        blocks.flat(root.first_child).map_or(&[], |first| {
            self.nodes
                .get(first.0 .. first.0.saturating_add(root.child_count.0))
                .unwrap_or_default()
        })
    }

    /// Cut the top-level children at the ordinals `children`, except the
    /// ordinals `without`, out of the tree with their blocks, each span counted
    /// from `anchor`. An ordinal counts the top-level children before it.
    ///
    /// # Specification
    /// - requires: `without` is ascending; an ordinal past the top-level
    ///   children is passed over.
    /// - ensures: on success, a slice of each such child in order, each with
    ///   the block of its descendants, its forms' digests, walks and ranks, and
    ///   every span moved back by `anchor`.
    /// - provides: the part of a parse that a later parse takes up whole when
    ///   the same bytes stand at another anchor.
    /// - fails: [`SyntaxError::SpanBeforeAnchor`] when a node of the slice
    ///   starts before `anchor`.
    /// - panics: none.
    /// - intension: one copy of each node of the slice and of each of its
    ///   forms' index entries; nothing is hashed.
    ///
    /// # Errors
    /// [`SyntaxError::SpanBeforeAnchor`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree cut into slices at each split of its top-level
    ///   children assembles to itself; a slice that passes over a child
    ///   assembles without it; a node before the anchor is refused by name.
    /// - witness: `build::tests::a_tree_cut_into_slices_assembles_to_itself`
    /// - witness: `build::tests::a_slice_names_the_comments_its_first_form_leads_with`
    #[inline]
    #[spec(captures: asked = children.end.0.saturating_sub(children.start.0),
        ensures: |ret| ret.as_ref().map_or_else(
            |error| matches!(*error, SyntaxError::SpanBeforeAnchor { anchor: at, .. } if at == anchor),
            |slice| slice.children.len() <= asked
                && slice.ranks.len() == slice.children.len().saturating_add(slice.nodes.len())
                && slice.digests.len() == slice.forms.len()
                && slice.ranges.len() == slice.forms.len(),
        ))]
    pub fn slice(
        &self,
        children: Range<ChildCount>,
        without: &[ChildCount],
        anchor: ByteOffset,
    ) -> Result<TreeSlice, SyntaxError>
    {
        let asked = children.end.0.saturating_sub(children.start.0);
        let blocks = BlockStarts::new(&self.starts, NodeCount(self.nodes.len()));
        let tops = self.top_level();
        let first_top = self
            .nodes
            .first()
            .and_then(|root| blocks.flat(root.first_child))
            .map_or(0, |first| first.0);
        let back = |span: ByteSpan| {
            let start = usize::from(span.start()).checked_sub(usize::from(anchor));
            let end = usize::from(span.end()).checked_sub(usize::from(anchor));
            match (start, end) {
                (Some(start), Some(end)) => {
                    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
                },
                _ => Err(SyntaxError::SpanBeforeAnchor { span, anchor }),
            }
        };
        let mut slice = TreeSlice {
            children: Vec::with_capacity(asked),
            nodes: Vec::new(),
            starts: Vec::new(),
            ranks: Vec::new(),
            forms: Vec::new(),
            digests: Vec::new(),
            ranges: Vec::new(),
            extent: ByteOffset::from(0_usize),
        };
        let mut passed = without.iter().copied().peekable();
        let mut child_ranks = Vec::with_capacity(asked);
        for ordinal in children.start.0 .. children.end.0 {
            if passed.next_if(|skip| skip.0 == ordinal).is_some() {
                continue;
            }
            let Some(&top) = tops.get(ordinal)
            else {
                continue;
            };
            let flat = first_top.saturating_add(ordinal);
            let block = LayoutBlock::from(slice.starts.len());
            let held = self.index.ranks.get(flat).copied().flatten();
            let slot = held.map(|_| FormSlot(slice.digests.len()));
            let span = back(top.span)?;
            slice.extent = slice.extent.max(span.end());
            if let Some((form, _)) = held {
                slice.forms.push(BlockOffset::from(slice.children.len()));
                slice
                    .digests
                    .extend(self.index.digests.get(form.0).copied());
            }
            slice.children.push(Node {
                span,
                first_child: NodeIndex::at(block, top.first_child.offset()),
                ..top
            });
            child_ranks.push(held.and_then(|(_, rank)| slot.map(|slot| (slot, rank))));
            let bounds = if top.child_count.0 == 0 {
                None
            }
            else {
                blocks.bounds(top.first_child.block())
            };
            let Some((start, end)) = bounds
            else {
                if slot.is_some() {
                    slice.ranges.push(NodeIndices::empty());
                }
                continue;
            };
            slice.starts.push(NodeCount(slice.nodes.len()));
            for at in start.0 .. end.0 {
                let Some(&node) = self.nodes.get(at)
                else {
                    continue;
                };
                let span = back(node.span)?;
                slice.extent = slice.extent.max(span.end());
                slice.nodes.push(Node {
                    span,
                    first_child: NodeIndex::at(block, node.first_child.offset()),
                    ..node
                });
                slice.ranks.push(
                    self.index
                        .ranks
                        .get(at)
                        .copied()
                        .flatten()
                        .and_then(|(_, rank)| slot.map(|slot| (slot, rank))),
                );
            }
            if slot.is_some() {
                slice.ranges.push(NodeIndices::run(
                    NodeIndex::at(block, BlockOffset(0)),
                    ChildCount(end.0.saturating_sub(start.0)),
                ));
            }
        }
        child_ranks.append(&mut slice.ranks);
        slice.ranks = child_ranks;

        Ok(slice)
    }

    /// The tree over `source` whose root is a [`NodeLabel::Wald`] over the
    /// whole text and whose top-level children are `pieces`' children in
    /// order, each piece laid at its anchor.
    ///
    /// # Specification
    /// - requires: each piece was cut from a tree whose text holds, from the
    ///   piece's own anchor, the bytes `source` holds from the anchor given
    ///   here; the pieces stand in source order and do not overlap.
    /// - ensures: on success, the root over the whole text with every piece's
    ///   children as its own, in order; then every piece's blocks, in order,
    ///   each span moved by its piece's anchor and each child range by the
    ///   blocks before its piece; the forms, digests, walks and ranks of the
    ///   pieces, moved likewise; and the digest that [`index_forms`] gives a
    ///   tree of those forms. Where the pieces partition a parse of `source`,
    ///   the tree equals that parse.
    /// - provides: a parse that takes the forms an edit did not reach up whole
    ///   from the parse before it.
    /// - fails: [`SyntaxError::SpanOutsideSource`] when a piece reaches past
    ///   the end of `source`.
    /// - panics: none.
    /// - intension: one copy of each node and of each form's index entry; the
    ///   tree's digest hashes one digest per form.
    ///
    /// [`index_forms`]: super::index_forms
    ///
    /// # Errors
    /// [`SyntaxError::SpanOutsideSource`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree cut into slices at each split of its top-level
    ///   children assembles to itself, node for node, block for block and
    ///   digest for digest; two trees' slices laid end to end equal the tree of
    ///   the two texts; a piece past the text is refused by name.
    /// - witness: `build::tests::a_tree_cut_into_slices_assembles_to_itself`
    /// - witness: `build::tests::a_slice_moves_with_its_anchor`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |tree| tree.source == source
        && tree.grammar == grammar
        && tree.nodes.len() == pieces.iter().map(|&(piece, _)| piece.children.len().saturating_add(piece.nodes.len())).sum::<usize>().saturating_add(1)
        && tree.index.ranks.len() == tree.nodes.len()
        && tree.index.digests.len() == pieces.iter().map(|&(piece, _)| piece.digests.len()).sum::<usize>()))]
    pub fn assembled(
        source: SourceText<'source>,
        grammar: GrammarFingerprint,
        pieces: &[(&TreeSlice, ByteOffset)],
    ) -> Result<Self, SyntaxError>
    {
        let end = source.end();
        let mut tops = 0_usize;
        let mut below = 0_usize;
        let mut blocks = 1_usize;
        let mut forms = 0_usize;
        for &(piece, anchor) in pieces {
            let reach = usize::from(anchor).saturating_add(usize::from(piece.extent));
            if reach > usize::from(end) {
                return Err(SyntaxError::SpanOutsideSource {
                    span: ByteSpan::new(anchor, ByteOffset::from(reach))?,
                    source_end: end,
                });
            }
            tops = tops.saturating_add(piece.children.len());
            below = below.saturating_add(piece.nodes.len());
            blocks = blocks.saturating_add(piece.starts.len());
            forms = forms.saturating_add(piece.digests.len());
        }
        let count = tops.saturating_add(below).saturating_add(1);
        let mut nodes = Vec::with_capacity(count);
        let mut starts = Vec::with_capacity(blocks);
        let mut index = FormIndex {
            forms: Vec::with_capacity(forms),
            digests: Vec::with_capacity(forms),
            ranges: Vec::with_capacity(forms),
            ranks: Vec::with_capacity(count),
            digest: None,
        };
        nodes.push(Node::new(
            NodeLabel::Wald,
            ByteSpan::new(ByteOffset::from(0_usize), end)?,
            NodeIndex::at(LayoutBlock(0), BlockOffset(1)),
            ChildCount(tops),
        ));
        starts.push(NodeCount(0));
        index.ranks.push(None);
        // The root's block: every piece's children, then each piece's blocks.
        let mut past = 1_usize;
        let mut slots = 0_usize;
        for &(piece, anchor) in pieces {
            let by = ByteLength::from(usize::from(anchor));
            let moved = LayoutBlock::from(past);
            let first = nodes.len();
            nodes.extend(piece.children.iter().map(|child| Node {
                span: child.span.shifted(by),
                first_child: child.first_child.moved(moved),
                ..*child
            }));
            index.ranks.extend(
                piece
                    .ranks
                    .get(.. piece.children.len())
                    .unwrap_or_default()
                    .iter()
                    .map(|held| {
                        held.map(|(slot, rank)| (FormSlot(slot.0.saturating_add(slots)), rank))
                    }),
            );
            index.forms.extend(piece.forms.iter().map(|&form| {
                NodeIndex::at(
                    LayoutBlock(0),
                    BlockOffset::from(first.saturating_add(usize::from(form))),
                )
            }));
            index.digests.extend_from_slice(&piece.digests);
            index
                .ranges
                .extend(piece.ranges.iter().map(|walk| moved_walk(walk, moved)));
            past = past.saturating_add(piece.starts.len());
            slots = slots.saturating_add(piece.digests.len());
        }
        let mut past = 1_usize;
        let mut slots = 0_usize;
        for &(piece, anchor) in pieces {
            let by = ByteLength::from(usize::from(anchor));
            let moved = LayoutBlock::from(past);
            let base = nodes.len();
            starts.extend(
                piece
                    .starts
                    .iter()
                    .map(|start| NodeCount(start.0.saturating_add(base))),
            );
            nodes.extend(piece.nodes.iter().map(|node| Node {
                span: node.span.shifted(by),
                first_child: node.first_child.moved(moved),
                ..*node
            }));
            let before = slots;
            index.ranks.extend(
                piece
                    .ranks
                    .get(piece.children.len() ..)
                    .unwrap_or_default()
                    .iter()
                    .map(|held| {
                        held.map(|(slot, rank)| (FormSlot(slot.0.saturating_add(before)), rank))
                    }),
            );
            past = past.saturating_add(piece.starts.len());
            slots = slots.saturating_add(piece.digests.len());
        }
        let mut preimage = Preimage::default();
        preimage.open_tree();
        preimage.node(
            NodeLabel::Wald,
            source
                .fragment(ByteSpan::new(ByteOffset::from(0_usize), end)?)
                .unwrap_or_else(|_refused| SourceFragment::from("")),
            ChildCount(index.digests.len()),
        );
        for &form in &index.digests {
            preimage.digest(form);
        }
        index.digest = Some(preimage.hash());

        Ok(Self {
            source,
            grammar,
            nodes,
            starts,
            roots: Vec::from([NodeIndex::default()]),
            index,
        })
    }
}

/// `walk` with its block moved up past `past`; an empty walk stays empty, as
/// [`index_forms`](super::index_forms) gives a form with no children.
///
/// # Specification
/// trivial.
#[inline]
fn moved_walk(
    walk: &NodeIndices,
    past: LayoutBlock,
) -> NodeIndices
{
    if walk.next == walk.end {
        return NodeIndices::empty();
    }
    NodeIndices {
        next: walk.next.moved(past),
        end: walk.end.moved(past),
    }
}
