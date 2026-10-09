//! Readers over a committed tree, shared by the unit tests.

use alloc::borrow::ToOwned as _;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;

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
/// - ensures: the concatenation of every tile and layout leaf's text, ordered
///   by span; grout and minted closes are empty and contribute nothing, so a
///   lossless tree returns exactly its source.
/// - panics: none.
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
