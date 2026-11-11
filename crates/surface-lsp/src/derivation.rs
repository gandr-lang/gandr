//! The trace layer's faces in the hub: the derivation card of the declaration
//! at a cursor, which the render bus sends a client of the trace layer, and
//! the hover's derivation section.
//!
//! A card holds one row for each judgement node of the declaration's tree,
//! in the tree's order. A row holds the node's warrant, its direction, its
//! goal and its type laid out at the columns that the client stated, the
//! rule's short name, the cover, the memo's mark, the nodes that the check
//! visited, the wall, and the bytes where the goal is written, which the
//! node's place in its declaration and the declaration's first byte give. The
//! index stores no text, so the card prints each goal and type here.
//!
//! The hover's section shows the row in focus at the hover's position and
//! each of its ancestors, the root first, one line each: the warrant's glyph,
//! the direction's glyph, the goal and its type on one line, and the rule.
//!
//! # References
//!
//! - `engine-surface.md` § engine-surface-derivation (vault reference
//!   `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e`): the columns of the
//!   derivation pane, the focus at the cursor, and the hover section for the
//!   node at the cursor.

use alloc::string::String;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_pretty::PageWidth;
use gandr_surface_render_remote::AccountKey;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::DerivationCard;
use gandr_surface_render_remote::DerivationRow;
use gandr_surface_render_remote::Direction;
use gandr_surface_render_remote::Memo;
use gandr_surface_render_remote::Warrant;
use gandr_surface_session::Derivation;
use gandr_surface_session::MemoMark;
use quenchant_shape::shape::Maybe;

/// The columns that a hover's derivation section lays each goal out at: the
/// section then joins each goal's lines into one.
pub const HOVERED: Count = Count(100);

/// The derivation card of `derivation`, the declaration that its account card
/// keys `key` and that the text names `name`, whose text starts at byte
/// `start`: its goals and types laid out at `columns`.
///
/// # Specification
/// - requires: `start` is the first byte of the declaration in the text that
///   the derivation's places count from.
/// - ensures: one row for each node, in the tree's order. A row's direction is
///   checking for a node checked against a type and synthesis otherwise; its
///   memo is absent for a node that the memo cannot key; its span is the node's
///   place moved by `start`, and absent for a node with no place.
/// - provides: the card that the render bus sends a client of the trace layer.
/// - fails: never.
/// - panics: none.
/// - intension: one read of the declaration's binders, then one print of each
///   node's goal and type, so the work is linear in the declaration's nodes and
///   in the text that the prints lay out.
///
/// # Adequacy
/// - hypothesis: L3 — an attached view of the trace layer hears the card of the
///   declaration at the editor's cursor, its first row the root at depth zero,
///   and each goal written inside the declaration.
/// - witness: `hub::tests::an_attached_view_follows_the_derivation_at_the_editors_cursor`
#[spec(ensures: |ret| ret.rows.len() == derivation.nodes().len() && ret.columns == columns)]
#[must_use]
pub fn card(
    derivation: &Derivation<'_>,
    (key, declaration): (AccountKey, String),
    start: ByteOffset,
    columns: Count,
) -> DerivationCard
{
    let page = PageWidth::from(u32::try_from(columns.0).unwrap_or(u32::MAX));
    let count = |value: u32| Count(u64::from(value));
    let placed = |offset: gandr_surface_syntax::ByteOffset| {
        ByteOffset::from(usize::from(start).saturating_add(usize::from(offset)))
    };
    let goals = derivation.goals();
    let rows = derivation
        .nodes()
        .iter()
        .map(|node| DerivationRow {
            depth: count(u32::from(node.depth())),
            warrant: match derivation.warrant(node) {
                gandr_surface_session::Warrant::Checked => Warrant::Checked,
                gandr_surface_session::Warrant::Replayed => Warrant::Replayed,
                gandr_surface_session::Warrant::Refused => Warrant::Refused,
            },
            direction: match node.against() {
                Maybe::Present(_) => Direction::Checking,
                Maybe::Absent(_) => Direction::Synthesis,
            },
            goal: match goals.goal(node, page) {
                Maybe::Present(goal) => Some(alloc::format!("{goal}")),
                Maybe::Absent(_) => None,
            },
            ty: match goals.ty(node, page) {
                Maybe::Present(ty) => Some(alloc::format!("{ty}")),
                Maybe::Absent(_) => None,
            },
            rule: String::from(derivation.rule(node).as_ref()),
            cover: count(u32::from(node.cover())),
            memo: match node.memo() {
                MemoMark::Hit => Some(Memo::Hit),
                MemoMark::Miss => Some(Memo::Miss),
                MemoMark::Unkeyed | MemoMark::Closed => None,
            },
            nodes: count(u32::from(node.visited())),
            wall: Count(u64::from(node.wall())),
            span: match node.written() {
                Maybe::Present(written) => {
                    ByteRange::new(placed(written.start()), placed(written.end())).ok()
                },
                Maybe::Absent(_) => None,
            },
        })
        .collect();
    DerivationCard {
        key,
        declaration,
        columns,
        rows,
    }
}

/// The hover's derivation section of `card` at `offset`: one line for the row
/// in focus and for each of its ancestors, the root first, in a fenced block.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `None` when no row holds `offset`; otherwise a fenced block of
///   one line for each row that [`DerivationCard::ancestors`] names for the
///   focus, each set in by two spaces for each level of its depth.
/// - provides: the section that a hover adds at the trace layer.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hover inside a traced declaration's body shows the
///   root's line first and the line of the node at the position last.
/// - witness: `server::tests::a_traced_hover_shows_the_node_at_the_cursor_and_its_ancestors_6295`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|text|
    text.starts_with("```text\n") && text.ends_with("```")))]
#[must_use]
pub fn section(
    card: &DerivationCard,
    offset: ByteOffset,
) -> Option<String>
{
    let focus = card.focus(offset)?;
    let mut section = String::from("```text\n");
    for at in card.ancestors(focus) {
        let Some(row) = card.rows.get(at.0)
        else {
            continue;
        };
        for _ in 0 .. row.depth.0 {
            section.push_str("  ");
        }
        let _written = write!(
            section,
            "{} {}",
            <&str>::from(row.warrant.glyph()),
            <&str>::from(row.direction.glyph())
        );
        if let Some(ref goal) = row.goal {
            section.push(' ');
            joined(&mut section, goal.split_whitespace());
        }
        if let Some(ref ty) = row.ty {
            section.push_str(" : ");
            joined(&mut section, ty.split_whitespace());
        }
        let _written = writeln!(section, "  {}", row.rule);
    }
    section.push_str("```");
    Some(section)
}

/// Push `words` onto `line` on one line: the words of a text with each run
/// of white space, line breaks included, written as one space.
///
/// # Specification
/// trivial.
fn joined(
    line: &mut String,
    words: core::str::SplitWhitespace<'_>,
)
{
    for (at, word) in words.enumerate() {
        if at > 0 {
            line.push(' ');
        }
        line.push_str(word);
    }
}
