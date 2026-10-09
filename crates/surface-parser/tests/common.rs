//! Shared fixtures and tree readers for the `gandr-surface-parser` integration
//! suites.

use std::path::Path;
use std::path::PathBuf;
use std::sync::LazyLock;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeDigest;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;

/// The real built-in grammar, built once per test process and shared across
/// the suites in this funnel binary.
///
/// Nextest runs every test in its own process, so one cache here is the
/// per-process floor — a second cache elsewhere in the funnel would double
/// the cost of `built_in()` a grammar-touching test pays.
///
/// # Specification
/// - panics: when the built-in grammar fails to assemble, which its own suite
///   rules out.
pub fn built() -> &'static Pbg
{
    /// The process-wide cached grammar.
    static BUILT_IN: LazyLock<Pbg> =
        LazyLock::new(|| built_in().expect("built-in grammar assembles"));
    &BUILT_IN
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

/// The immediate children of the node at `at` that are not layout, in order.
///
/// # Specification
/// trivial.
pub fn significant_children(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Vec<NodeIndex>
{
    tree.children(at)
        .filter(|&child| label_of(tree, child) != Some(NodeLabel::Space))
        .collect()
}

/// The label of the node at `at`, when the tree holds it.
///
/// # Specification
/// trivial.
pub fn label_of(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<NodeLabel>
{
    tree.node(at).map(Node::label)
}

/// The span of the node at `at`, when the tree holds it.
///
/// # Specification
/// trivial.
pub fn span(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<ByteSpan>
{
    tree.node(at).map(Node::span)
}

/// The source text the node at `at` spans; empty when the tree holds no such
/// node.
///
/// # Specification
/// trivial.
pub fn text(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> String
{
    tree.fragment(at)
        .map(|fragment| <&str>::from(fragment).to_owned())
        .unwrap_or_default()
}

/// The content digest of the root.
///
/// # Specification
/// trivial.
pub fn root_digest(tree: &SyntaxTree<'_>) -> Option<NodeDigest>
{
    tree.node(tree.root()).map(Node::digest)
}

/// The language's source corpus, which the corpus crate owns: the strict
/// root, the fixture root and its pending set.
///
/// # Specification
/// trivial.
pub fn corpus_root() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus")
}

/// Every `.gandr` file under `dir`, sorted.
///
/// # Specification
/// - ensures: a walk of `dir` and its subdirectories, unreadable entries
///   skipped, the paths sorted so a run is deterministic.
/// - panics: none.
pub fn gandr_files(dir: &Path) -> Vec<PathBuf>
{
    let mut out = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next_dir) = pending.pop() {
        if let Ok(entries) = std::fs::read_dir(next_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    pending.push(path);
                }
                else if path.extension().is_some_and(|ext| ext == "gandr") {
                    out.push(path);
                }
            }
        }
    }
    out.sort();
    out
}
