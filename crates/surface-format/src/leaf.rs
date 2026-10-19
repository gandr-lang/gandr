//! The source read as a flat run of leaves: every token, comment and
//! whitespace run in offset order, each beside the top-level form it belongs
//! to.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;

/// The forms the formatter copies byte for byte, by the grammar rule's name
/// before any sort suffix: a string's fragments are its text, a shell
/// block's line breaks separate its commands, and a hole is left as written.
const VERBATIM_RULES: [&str; 3] = ["string", "shell_block", "hole"];

/// What a leaf of the flattened source is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Material
{
    /// A token the source wrote.
    Token,
    /// A form copied byte for byte.
    Verbatim,
    /// A comment running to the end of its line, documentation included.
    LineComment,
    /// A delimited comment.
    BlockComment,
    /// The interpreter line at the start of the source.
    Shebang,
    /// A run of spaces, tabs and line breaks.
    Whitespace,
}

/// The top-level position a leaf belongs to.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Owner
{
    /// Layout at the root, between top-level forms.
    Root,
    /// The top-level form at this child position of the root.
    Form(NodeIndex),
}

/// One leaf of the flattened source.
#[derive(Clone, Copy, Debug)]
pub struct Leaf<'source>
{
    /// The bytes the leaf covers.
    pub span: ByteSpan,
    /// Those bytes.
    pub text: SourceFragment<'source>,
    /// What the leaf is.
    pub material: Material,
    /// The top-level position it belongs to.
    pub owner: Owner,
    /// Whether it is documentation's material.
    pub documentation: Documentation,
}

/// Whether a leaf is documentation's material.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Documentation
{
    /// It is not.
    Outside,
    /// It is under this documentation node: a `///` run or a `doc` entry.
    Inside(NodeIndex),
}

/// Whether a top-level form may be laid out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Integrity
{
    /// The form parsed cleanly.
    Clean,
    /// The parser repaired the form, or an obligation touches it: it is
    /// copied as written.
    Repaired,
}

/// The flattened source.
#[derive(Debug)]
pub struct Leaves<'source>
{
    /// Every leaf, in offset order.
    pub leaves: Vec<Leaf<'source>>,
    /// The top-level forms the parser repaired, ascending.
    pub repaired: Vec<NodeIndex>,
}

impl Leaves<'_>
{
    /// Whether the top-level form `form` may be laid out.
    ///
    /// # Specification
    /// trivial.
    pub fn integrity(
        &self,
        form: NodeIndex,
    ) -> Integrity
    {
        if self.repaired.binary_search(&form).is_ok() {
            Integrity::Repaired
        }
        else {
            Integrity::Clean
        }
    }
}

/// The leaves of `tree` in offset order, each beside its top-level form.
///
/// # Specification
/// - requires: `tree` was parsed under `grammar`, and `obligations` are that
///   parse's.
/// - ensures: one leaf per tile, layout leaf and nonempty grout, except that a
///   form [`VERBATIM_RULES`] names is one [`Material::Verbatim`] leaf over its
///   span and the layout inside that span is dropped; leaves are in ascending,
///   disjoint offset order. A leaf under the root's child at `c` belongs to the
///   form `c` unless it is layout directly under the root. A top-level form
///   holding grout or a minted close, or whose leaves' extent meets an
///   obligation's span, is listed as repaired.
/// - provides: the formatter's only reading of the tree.
/// - fails: never.
/// - panics: none.
/// - intension: one walk of the tree with an explicit stack, one sort.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source is formatted and its token and
///   comment texts compared with the source's in order; a dropped, duplicated
///   or reordered leaf breaks that comparison, and a repaired source is copied
///   byte for byte.
/// - witness: `tests::format::sweeps::every_source_keeps_its_meaning_and_formats_once`
/// - witness: `tests::format::a_repaired_form_is_copied_as_written`
/// - witness: `tests::format::strings_shell_blocks_and_holes_are_copied_as_written`
#[spec(ensures: |ret| ret.leaves.windows(2).all(|pair| matches!(pair, [left, right] if left.span.end() <= right.span.start()))
    && ret.repaired.windows(2).all(|pair| matches!(pair, [left, right] if left < right)))]
pub fn flatten<'source>(
    grammar: &Pbg,
    tree: &SyntaxTree<'source>,
    obligations: &[ObligationInstance],
) -> Leaves<'source>
{
    let mut leaves: Vec<Leaf<'source>> = Vec::new();
    let mut repaired: Vec<NodeIndex> = Vec::new();
    let mut pending: Vec<(NodeIndex, Owner, Documentation)> = tree
        .children(tree.root())
        .map(|child| (child, Owner::Form(child), Documentation::Outside))
        .collect();
    while let Some((at, owner, documentation)) = pending.pop() {
        let Some(node) = tree.node(at)
        else {
            continue;
        };
        let Some(text) = tree.fragment(at)
        else {
            continue;
        };
        let material = match node.label() {
            NodeLabel::Meld(mold) => match copied(grammar, mold) {
                Copied::Verbatim => Material::Verbatim,
                Copied::LaidOut => {
                    pending.extend(tree.children(at).map(|child| (child, owner, documentation)));
                    continue;
                },
            },
            NodeLabel::Wald => {
                pending.extend(tree.children(at).map(|child| (child, owner, documentation)));
                continue;
            },
            NodeLabel::Doc => {
                pending.extend(
                    tree.children(at)
                        .map(|child| (child, owner, Documentation::Inside(at))),
                );
                continue;
            },
            NodeLabel::Tile(_) => Material::Token,
            NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } => {
                if let Owner::Form(form) = owner {
                    repaired.push(form);
                }
                if node.span().start() == node.span().end() {
                    continue;
                }
                Material::Token
            },
            NodeLabel::Space => layout_of(text),
        };
        let owner = match (owner, material) {
            (
                Owner::Form(form),
                Material::Whitespace
                | Material::LineComment
                | Material::BlockComment
                | Material::Shebang,
            ) if form == at => Owner::Root,
            (owner, _) => owner,
        };
        leaves.push(Leaf {
            span: node.span(),
            text,
            material,
            owner,
            documentation,
        });
    }
    leaves.sort_by_key(|leaf| (leaf.span.start(), leaf.span.end()));
    let mut kept: Vec<Leaf<'source>> = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        match kept.last() {
            Some(last) if leaf.span.start() < last.span.end() => {},
            Some(_) | None => kept.push(leaf),
        }
    }
    for obligation in obligations {
        for leaf in &kept {
            if let Owner::Form(form) = leaf.owner
                && leaf.span.start() <= obligation.span.end()
                && obligation.span.start() <= leaf.span.end()
            {
                repaired.push(form);
            }
        }
    }
    repaired.sort_unstable();
    repaired.dedup();
    Leaves {
        leaves: kept,
        repaired,
    }
}

/// Whether a form is laid out or copied byte for byte.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Copied
{
    /// A form [`VERBATIM_RULES`] names: copied as written.
    Verbatim,
    /// Any other form: laid out.
    LaidOut,
}

/// Whether the form `mold` molds is copied byte for byte: its grammar rule's
/// name before any sort suffix is one [`VERBATIM_RULES`] names.
///
/// # Specification
/// trivial.
pub fn copied(
    grammar: &Pbg,
    mold: MoldId,
) -> Copied
{
    let verbatim = grammar.rule_of(mold).is_ok_and(|rule| {
        let name = rule.name().0;
        let base = name.split_once('.').map_or(name, |(base, _)| base);
        VERBATIM_RULES.contains(&base)
    });
    if verbatim {
        Copied::Verbatim
    }
    else {
        Copied::LaidOut
    }
}

/// What a layout leaf spelling `text` is.
///
/// # Specification
/// trivial.
fn layout_of(text: SourceFragment<'_>) -> Material
{
    let text = <&str>::from(text);
    if text.starts_with("//") {
        Material::LineComment
    }
    else if text.starts_with("/*") {
        Material::BlockComment
    }
    else if text.starts_with("#!") {
        Material::Shebang
    }
    else {
        Material::Whitespace
    }
}
