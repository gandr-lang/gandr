//! Every comment of a source beside the node it belongs to: the record a
//! layout keeps, a rewrite carries and a reflow reads.
//!
//! The parser already places each comment among its owner's children (the
//! rule `gandr-surface-parser` documents under "A comment belongs to the node
//! it describes"). This module reads that placement back as a record beside
//! the tree — the tree itself is not changed — and adds what the placement
//! leaves implicit: the comment's role among its owner's children, its kind,
//! its source column and the width of its text.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::layout::BRACKETS;

/// What a comment is written as.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CommentKind
{
    /// A comment running to the end of its line, `// …`.
    Line,
    /// A delimited comment, `/* … */`.
    Block,
    /// A documentation line, `/// …`.
    Documentation,
}

/// Where a comment stands among its owner's children.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Role
{
    /// On its own line, before material of its owner: the owner's first
    /// child, or one between two of its children.
    Leading,
    /// On the line of the material before it, which it follows.
    Trailing,
    /// On its own line with nothing of its owner after it but the owner's
    /// closing bracket: the end of a block, an empty bracket.
    Dangling,
}

/// A column of the source, counted in characters from its line's start.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Column(pub usize);

/// The width of a comment's text in characters: its longest line's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Width(pub usize);

/// One comment and the node it belongs to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Comment<'source>
{
    /// The bytes the comment covers.
    pub span: ByteSpan,
    /// Those bytes.
    pub text: SourceFragment<'source>,
    /// What it is written as.
    pub kind: CommentKind,
    /// Where it stands among its owner's children.
    pub role: Role,
    /// The node it belongs to, in this tree: the root, or a form.
    pub owner: NodeIndex,
    /// The owner's key across trees; none for the root.
    pub key: Option<NodeKey>,
    /// The column it starts at in the source.
    pub column: Column,
    /// The width of its text.
    pub width: Width,
}

/// What a layout keeps of a comment: its text, kind and role and its
/// owner's key, but not its column, which a layout moves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Attachment<'source>
{
    /// The comment's bytes.
    pub text: SourceFragment<'source>,
    /// What it is written as.
    pub kind: CommentKind,
    /// Where it stands among its owner's children.
    pub role: Role,
    /// The owner's key across trees; none for the root.
    pub key: Option<NodeKey>,
}

impl<'source> Comment<'source>
{
    /// What a layout must keep of the comment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn attachment(&self) -> Attachment<'source>
    {
        Attachment {
            text: self.text,
            kind: self.kind,
            role: self.role,
            key: self.key,
        }
    }
}

/// Every comment of `tree`, in source order, each beside its owner.
///
/// # Specification
/// - requires: nothing; a repaired tree is read as it stands.
/// - ensures: one comment per layout leaf spelling `//` or `/*`, in ascending
///   offset order. Its owner is the node holding it, or the node holding the
///   documentation it is a line of; its key is the owner's, none for the root.
///   Its role reads the owner's significant children: trailing when one ends
///   before it and nothing but spaces and tabs separate the two; otherwise
///   leading when a child starts after it that is not the owner's closing
///   bracket; otherwise dangling. A line under documentation is
///   [`CommentKind::Documentation`]; any other comment is a line or a block
///   comment by its opening. Its column counts the characters between the line
///   break before it and its start; its width is its longest line's.
/// - provides: the record a layout keeps, a rewrite carries and a reflow reads.
/// - fails: never.
/// - panics: none.
/// - intension: one walk of the tree with an explicit stack, one sort.
///
/// # Adequacy
/// - hypothesis: L3 — a leading, a trailing and a dangling comment, a
///   documentation line and a comment at the root are each read with their
///   owner and role; the formatter compares every corpus source's comments with
///   its output's, so a layout that moves a comment off its owner or changes
///   its role is refused.
/// - witness: `tests::attach::a_comment_on_its_own_line_leads_the_form_below_it`
/// - witness: `tests::attach::a_comment_after_material_on_its_line_trails_it`
/// - witness: `tests::attach::a_comment_before_a_closing_bracket_dangles_on_its_block`
/// - witness: `tests::attach::documentation_and_the_root_keep_their_owners`
/// - witness: `tests::format::sweeps::every_source_keeps_its_meaning_and_formats_once`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [left, right] if left.span.end() <= right.span.start())))]
#[inline]
#[must_use]
pub fn comments<'source>(tree: &SyntaxTree<'source>) -> Vec<Comment<'source>>
{
    let mut found: Vec<Comment<'source>> = Vec::new();
    let mut pending: Vec<NodeIndex> = Vec::from([tree.root()]);
    let mut children: Vec<NodeIndex> = Vec::new();
    let mut significant: Vec<NodeIndex> = Vec::new();
    let mut lines: Vec<(NodeIndex, CommentKind)> = Vec::new();
    while let Some(owner) = pending.pop() {
        children.clear();
        children.extend(tree.children(owner));
        significant.clear();
        significant.extend(children.iter().copied().filter(|&child| {
            tree.node(child)
                .is_some_and(|node| bool::from(node.label().significance()))
        }));
        for &child in &children {
            let Some(node) = tree.node(child)
            else {
                continue;
            };
            lines.clear();
            match node.label() {
                NodeLabel::Space => {
                    lines.extend(written(tree, child).into_iter().map(|kind| (child, kind)));
                },
                NodeLabel::Doc => lines.extend(
                    tree.children(child)
                        .filter(|&line| written(tree, line).is_some())
                        .map(|line| (line, CommentKind::Documentation)),
                ),
                NodeLabel::Wald
                | NodeLabel::Meld(_)
                | NodeLabel::Tile(_)
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. } => {
                    pending.push(child);
                    continue;
                },
            }
            for &(line, kind) in &lines {
                let (Some(leaf), Some(text)) = (tree.node(line), tree.fragment(line))
                else {
                    continue;
                };
                let span = leaf.span();
                found.push(Comment {
                    span,
                    text,
                    kind,
                    role: role(tree, &significant, span),
                    owner,
                    key: tree.key(owner),
                    column: column(tree.source(), span),
                    width: width(text),
                });
            }
        }
    }
    found.sort_by_key(|comment| comment.span.start());
    found
}

/// What the layout leaf at `at` is written as, when it is a comment.
///
/// # Specification
/// trivial.
fn written(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<CommentKind>
{
    let node = tree.node(at)?;
    if node.label() != NodeLabel::Space {
        return None;
    }
    let text = <&str>::from(tree.fragment(at)?);
    if text.starts_with("///") && !text.starts_with("////") {
        Some(CommentKind::Documentation)
    }
    else if text.starts_with("//") {
        Some(CommentKind::Line)
    }
    else if text.starts_with("/*") {
        Some(CommentKind::Block)
    }
    else {
        None
    }
}

/// The role of the comment at `span` among `significant`, its owner's
/// significant children in source order.
///
/// # Specification
/// trivial.
fn role(
    tree: &SyntaxTree<'_>,
    significant: &[NodeIndex],
    span: ByteSpan,
) -> Role
{
    let source = <&str>::from(tree.source());
    let spanned = |at: NodeIndex| tree.node(at).map(gandr_surface_syntax::Node::span);
    let before = significant
        .iter()
        .rev()
        .filter_map(|&child| spanned(child))
        .find(|child| child.end() <= span.start());
    if let Some(before) = before
        && source
            .get(usize::from(before.end()) .. usize::from(span.start()))
            .is_some_and(|between| !between.contains('\n'))
    {
        return Role::Trailing;
    }
    let closes = |at: NodeIndex| match tree.node(at).map(gandr_surface_syntax::Node::label) {
        Some(NodeLabel::GhostClose { .. }) => true,
        Some(NodeLabel::Tile(_)) => tree.fragment(at).is_some_and(|text| {
            BRACKETS
                .iter()
                .any(|&(_, closer)| closer == <&str>::from(text))
        }),
        Some(
            NodeLabel::Wald
            | NodeLabel::Meld(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::Space
            | NodeLabel::Doc,
        )
        | None => false,
    };
    let after = significant
        .iter()
        .copied()
        .find(|&child| spanned(child).is_some_and(|child| child.start() >= span.end()));
    match after {
        Some(after) if !closes(after) => Role::Leading,
        Some(_) | None => Role::Dangling,
    }
}

/// The column `span` starts at in `source`.
///
/// # Specification
/// trivial.
fn column(
    source: SourceText<'_>,
    span: ByteSpan,
) -> Column
{
    let line = <&str>::from(source)
        .get(.. usize::from(span.start()))
        .unwrap_or_default();
    let start = line.rfind('\n').map_or(0_usize, |at| at.saturating_add(1));
    Column(
        line.get(start ..)
            .map_or(0_usize, |prefix| prefix.chars().count()),
    )
}

/// The width of `text`: the characters of its longest line.
///
/// # Specification
/// trivial.
fn width(text: SourceFragment<'_>) -> Width
{
    Width(
        <&str>::from(text)
            .lines()
            .map(|line| line.trim_end_matches('\r').chars().count())
            .max()
            .unwrap_or_default(),
    )
}
