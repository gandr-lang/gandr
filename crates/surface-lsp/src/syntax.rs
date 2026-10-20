//! The syntax tree view: a document's molded tree, its layout and its repairs,
//! printed as text for a client to show beside the document.
//!
//! A client opens the tree of the document at `file:///p` as the virtual
//! document `gandr-tree:///p` (or `gandr-tree:/p`, the same URI without its
//! empty authority) and asks for its text with `workspace/textDocumentContent`.
//! The tree is printed once per held text, on the first request after the text
//! changed, and the server asks the client to request it again after each
//! change to the document it views.
//!
//! # Examples
//!
//! The printed tree of `def f = 1 ;` and its newline: the form and its tiles,
//! then the layout, which the parser hangs off the root rather than the form
//! it falls inside, then the obligations, none here.
//!
//! ```text
//! wald@0..12
//!   form def_value@0..11
//!     tile def_value@0..3 "def"
//!     tile def_value@4..5 "f"
//!     tile def_value@6..7 "="
//!     tile number.expression@8..9 "1"
//!     tile def_value@10..11 ";"
//!   space@3..4 " "
//!   space@5..6 " "
//!   space@7..8 " "
//!   space@9..10 " "
//!   space@11..12 "\n"
//! obligations: none
//! ```

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_parser::Oblig;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GroutShape;
use gandr_surface_syntax::GroutSort;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;

use crate::recheck::grammar;

/// The scheme of the virtual documents the syntax tree view is served under.
pub const TREE_SCHEME: &str = "gandr-tree";

/// How deep below the root a node of the printed tree stands.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Depth(usize);

/// The molded tree of `text`, printed: one line per node, then the parser's
/// obligations.
///
/// # Specification
/// - requires: nothing; any text is admissible input.
/// - ensures: when the process's grammar built and the parser committed a tree,
///   one line per node in preorder, each indented two spaces per level below
///   the root and naming the node — `wald` for the root, a form or a tile by
///   its rule, grout by its sort and the sides it faces, a minted close by its
///   sort and the closer it stands in for, `space` for layout, `doc` for
///   documentation — then `@` and its byte span, a tile, layout or grout over
///   written bytes followed by the text it covers, quoted; then `obligations:
///   none`, or `obligations` and one indented line per obligation, its class
///   and span, in the parser's order. Otherwise one line naming why the text
///   has no tree.
/// - provides: the text a client shows for a document of [`TREE_SCHEME`].
/// - fails: never; a text with no tree says why.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a definition, and one whose value and closer are missing,
///   are each asserted at their exact printed tree, so a node skipped,
///   misnamed, misplaced in the preorder or at the wrong depth, a wrong span or
///   text, and an obligation lost or misnamed each differ.
/// - witness: `syntax::tests::a_definition_prints_each_node_at_its_depth`
/// - witness: `syntax::tests::a_repaired_definition_prints_its_repairs`
#[spec(ensures: |ret| ret.ends_with('\n'))]
#[must_use]
pub fn printed(text: SourceText<'_>) -> String
{
    let Ok(grammar) = grammar()
    else {
        return String::from("no tree: the grammar did not build\n");
    };
    let Ok(parsed) = parse(grammar, text)
    else {
        return String::from("no tree: the parser committed none\n");
    };
    let mut out = String::new();
    let tree = parsed.tree();
    let mut pending = Vec::from([(tree.root(), Depth(0))]);
    while let Some((at, depth)) = pending.pop() {
        let Some(node) = tree.node(at)
        else {
            continue;
        };
        for _ in 0 .. depth.0 {
            out.push_str("  ");
        }
        named(&mut out, grammar, node.label());
        let span = node.span();
        let _written = write!(
            out,
            "@{}..{}",
            usize::from(span.start()),
            usize::from(span.end())
        );
        let quoted = match node.label() {
            NodeLabel::Tile(_) | NodeLabel::Space | NodeLabel::Grout { .. } => tree
                .fragment(at)
                .map(<&str>::from)
                .filter(|text| !text.is_empty()),
            NodeLabel::Wald
            | NodeLabel::Meld(_)
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Doc => None,
        };
        if let Some(text) = quoted {
            let _written = write!(out, " \"{}\"", text.escape_debug());
        }
        out.push('\n');
        let below = Depth(depth.0.saturating_add(1));
        let first = pending.len();
        pending.extend(tree.children(at).map(|child| (child, below)));
        if let Some(added) = pending.get_mut(first ..) {
            added.reverse();
        }
    }
    if parsed.obligations().is_empty() {
        out.push_str("obligations: none\n");
    }
    else {
        out.push_str("obligations\n");
        for obligation in parsed.obligations() {
            let _written = writeln!(
                out,
                "  {}@{}..{}",
                class(obligation.class),
                usize::from(obligation.span.start()),
                usize::from(obligation.span.end())
            );
        }
    }
    out
}

/// Write the name the printed tree gives a node labelled `label` to `out`.
///
/// # Specification
/// trivial.
fn named(
    out: &mut String,
    grammar: &Pbg,
    label: NodeLabel,
)
{
    let rule = |mold: MoldId| grammar.rule_of(mold).map_or("unknown", |rule| rule.name);
    let sort = |sort: GroutSort| Sort::try_from_tag(sort).map_or("unknown", |sort| sort.name().0);
    let _written = match label {
        NodeLabel::Wald => write!(out, "wald"),
        NodeLabel::Meld(mold) => write!(out, "form {}", rule(mold)),
        NodeLabel::Tile(mold) => write!(out, "tile {}", rule(mold)),
        NodeLabel::Grout {
            sort: grouted,
            shape,
        } => write!(out, "grout {} {}", sort(grouted), match shape {
            GroutShape::Convex => "convex",
            GroutShape::Prefix => "prefix",
            GroutShape::Postfix => "postfix",
            GroutShape::Infix => "infix",
        }),
        NodeLabel::GhostClose {
            sort: closed,
            class,
        } => write!(out, "close {} {}", sort(closed), match class {
            ClosingClass::Paren => "`)`",
            ClosingClass::Bracket => "`]`",
            ClosingClass::Brace => "`}`",
        }),
        NodeLabel::Space => write!(out, "space"),
        NodeLabel::Doc => write!(out, "doc"),
    };
}

/// The name the printed tree gives an obligation of `class`.
///
/// # Specification
/// trivial.
const fn class(class: Oblig) -> ObligName
{
    ObligName(match class {
        Oblig::MissingMeld => "missing-term",
        Oblig::MissingTile => "missing-tile",
        Oblig::IncompleteTile => "incomplete-tile",
        Oblig::UnmoldedTok => "unmolded-token",
        Oblig::InconMeld => "inconsistent-term",
        Oblig::ExtraMeld => "extra-term",
        Oblig::ReservedKeyword => "reserved-keyword",
        Oblig::AmbiguousPrec => "ambiguous-precedence",
    })
}

/// The name of an obligation class, as the printed tree spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ObligName(&'static str);

impl core::fmt::Display for ObligName
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(self.0)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::SourceText;

    use super::printed;

    #[test]
    fn a_definition_prints_each_node_at_its_depth()
    {
        assert_eq!(
            printed(SourceText::from("def f = 1 ;\n")),
            "wald@0..12
  form def_value@0..11
    tile def_value@0..3 \"def\"
    tile def_value@4..5 \"f\"
    tile def_value@6..7 \"=\"
    tile number.expression@8..9 \"1\"
    tile def_value@10..11 \";\"
  space@3..4 \" \"
  space@5..6 \" \"
  space@7..8 \" \"
  space@9..10 \" \"
  space@11..12 \"\\n\"
obligations: none
"
        );
    }

    #[test]
    fn a_repaired_definition_prints_its_repairs()
    {
        assert_eq!(
            printed(SourceText::from("def f = \n")),
            "wald@0..9
  form def_value@0..7
    tile def_value@0..3 \"def\"
    tile def_value@4..5 \"f\"
    tile def_value@6..7 \"=\"
    grout item postfix@7..7
  space@3..4 \" \"
  space@5..6 \" \"
  space@7..8 \" \"
  space@8..9 \"\\n\"
obligations
  missing-tile@6..7
"
        );
    }
}
