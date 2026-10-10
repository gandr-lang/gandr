//! Readers over a committed tree, shared by the unit tests.

use alloc::borrow::ToOwned as _;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;

/// A formatter destination that refuses every write.
pub struct RefusingSink;

impl core::fmt::Write for RefusingSink
{
    /// Refuse the supplied fragment.
    ///
    /// # Specification
    /// trivial.
    fn write_str(
        &mut self,
        _text: &str,
    ) -> core::fmt::Result
    {
        Err(core::fmt::Error)
    }
}

/// The immediate children of the node at `at`, in order.
///
/// # Specification
/// trivial.
pub fn children(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Vec<NodeIndex>
{
    tree.children(at).collect()
}

/// The label of the node at `at`, when the tree holds it.
///
/// # Specification
/// trivial.
pub fn label(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<NodeLabel>
{
    tree.node(at).map(Node::label)
}

/// The content digest of the root.
///
/// # Specification
/// trivial.
pub fn root_digest(tree: &SyntaxTree<'_>) -> Option<NodeDigest>
{
    tree.node(tree.root()).map(Node::digest)
}

/// The texts of the tiles under the node at `at`, in source order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per [`NodeLabel::Tile`] leaf of the subtree, left to
///   right; grout, minted closes and layout contribute nothing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a nested tree with reversed source positions, non-tile
///   text and an absent position is observed through exact text lists.
///   Breadth-first traversal, source sorting, including grout and missing
///   subtree boundaries each change those lists.
/// - witness: `testing::tests::readers_distinguish_tree_order_from_source_order`
#[spec(ensures: |ret| {
    let all_texts_are_tiles = ret.iter().all(|text| tree.positions().any(|position| {
        matches!(label(tree, position), Some(NodeLabel::Tile(_)))
            && tree.fragment(position).is_some_and(|fragment| fragment.as_ref() == text)
    }));
    all_texts_are_tiles && tree.node(at).map_or_else(|| ret.is_empty(), |node| {
        (!matches!(node.label(), NodeLabel::Tile(_)) || ret.first().map(String::as_str) == tree.fragment(at).map(<&str>::from))
            && (at != tree.root() || ret.len() == tree.positions().filter(|&position| matches!(label(tree, position), Some(NodeLabel::Tile(_)))).count())
    })
})]
pub fn tile_texts(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Vec<String>
{
    let mut out = Vec::new();
    let mut pending = Vec::from([at]);
    while let Some(next) = pending.pop() {
        if let Some(NodeLabel::Tile(_)) = label(tree, next)
            && let Some(text) = tree.fragment(next)
        {
            out.push(<&str>::from(text).to_owned());
        }
        let below = children(tree, next);
        pending.extend(below.into_iter().rev());
    }
    out
}

/// The source spelled by the tree's text-carrying leaves, in offset order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: concatenates every text-carrying node's fragment in span order.
///   Grout over an unmolded token retains that token's bytes; inserted grout
///   and minted closes have empty spans. A lossless tree returns its source.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — tile traversal order differs from source order and a
///   nonempty grout fragment occupies the gap. Exact reconstructed bytes detect
///   unsorted traversal, omitted grout and duplicated text.
/// - witness: `testing::tests::readers_distinguish_tree_order_from_source_order`
/// - witness: `parse::tests::parse_is_lossless_and_hash_stable`
#[spec(ensures: |ret| tree.positions().filter_map(|position| {
    let node = tree.node(position)?;
    if bool::from(node.label().carries_text()) { tree.source().fragment(node.span()).ok() } else { None }
}).try_fold(0_usize, |length, fragment| length.checked_add(fragment.as_ref().len())) == Some(ret.len()))]
pub fn reconstruct(tree: &SyntaxTree<'_>) -> String
{
    let mut leaves = Vec::new();
    let mut pending = Vec::from([tree.root()]);
    while let Some(next) = pending.pop() {
        if let Some(node) = tree.node(next)
            && bool::from(node.label().carries_text())
            && let Some(text) = tree.fragment(next)
        {
            let span = node.span();
            leaves.push(((span.start(), span.end()), <&str>::from(text)));
        }
        pending.extend(children(tree, next));
    }
    leaves.sort_unstable_by_key(|&(span, _)| span);
    leaves.into_iter().map(|(_, text)| text).collect()
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::GroutSort;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeIndex;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceText;
    use gandr_surface_syntax::TreeBuilder;

    #[test]
    fn readers_distinguish_tree_order_from_source_order()
    {
        let mut builder =
            TreeBuilder::new(SourceText::from("a#b"), GrammarFingerprint::from(0_u64)).unwrap();
        let span =
            |start, end| ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).unwrap();
        let first = builder
            .node(NodeLabel::Tile(MoldId::from(0_u32)), span(0, 1), &[])
            .unwrap();
        let last = builder
            .node(NodeLabel::Tile(MoldId::from(0_u32)), span(2, 3), &[])
            .unwrap();
        let form = builder
            .node(NodeLabel::Meld(MoldId::from(0_u32)), span(2, 3), &[last])
            .unwrap();
        let grout = builder
            .node(
                NodeLabel::Grout {
                    sort: GroutSort::from(0_u16),
                    shape: GroutShape::Convex,
                },
                span(1, 2),
                &[],
            )
            .unwrap();
        let root = builder
            .node(NodeLabel::Wald, span(0, 3), &[form, grout, first])
            .unwrap();
        let tree = builder.finish(root).unwrap();
        assert_eq!(super::tile_texts(&tree, tree.root()), ["b", "a"]);
        assert_eq!(super::tile_texts(&tree, NodeIndex::from(1_usize)), ["b"]);
        assert!(super::tile_texts(&tree, NodeIndex::from(2_usize)).is_empty());
        assert!(
            super::tile_texts(&tree, NodeIndex::from(usize::from(tree.node_count()))).is_empty()
        );
        assert_eq!(super::reconstruct(&tree), "a#b");
    }
}
