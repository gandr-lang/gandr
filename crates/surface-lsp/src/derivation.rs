//! The trace layer's faces in the hub: the derivation card of the declaration
//! at a cursor, which the render bus sends a client of the trace layer, the
//! whole goal of one node of it, which a client asks for, and the hover's
//! derivation section.
//!
//! A card holds one row for each judgement node of the declaration's tree,
//! in the tree's order. A row holds the node's warrant, its direction, its
//! goal and its type on one line each, cut to the room that the client's
//! columns give them, the rule's short name, the cover, the memo's mark, the
//! nodes that the check visited, the wall, and the bytes where the goal is
//! written, which the node's place in its declaration and the declaration's
//! first byte give. The index stores no text, so the card prints each goal and
//! type here: on one line through the printer's one-line faces, which build no
//! layout document (#6755). A whole goal is laid out at the client's columns
//! only when the client opens its node.
//!
//! The hover's section shows the row in focus at the hover's position and
//! each of its ancestors, the root first, one line each: the warrant's glyph,
//! the direction's glyph, the goal and its type on one line, and the rule. It
//! prints only the goals and the types of those rows.
//!
//! # References
//!
//! - `engine-surface.md` § engine-surface-derivation (vault reference
//!   `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e`): the columns of the
//!   derivation pane, the focus at the cursor, and the hover section for the
//!   node at the cursor.

use alloc::string::String;
use alloc::vec::Vec;
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
use gandr_surface_render_remote::NodeAt;
use gandr_surface_render_remote::Room;
use gandr_surface_render_remote::Warrant;
use gandr_surface_render_remote::elided;
use gandr_surface_session::Derivation;
use gandr_surface_session::DerivationNode;
use gandr_surface_session::Lay;
use gandr_surface_session::MemoMark;
use quenchant_shape::shape::Maybe;

/// The derivation card of `derivation`, the declaration that its account card
/// keys `key` and that the text names `name`, whose text starts at byte
/// `start`: its goals and types on one line each, cut to the room that a pane
/// `columns` wide gives them.
///
/// # Specification
/// - requires: `start` is the first byte of the declaration in the text that
///   the derivation's places count from.
/// - ensures: one row for each node, in the tree's order. A row's direction is
///   checking for a node checked against a type and synthesis otherwise; its
///   goal and its type are their one-line prints cut to the [`Room`] of the
///   row's depth at `columns`; its memo is absent for a node that the memo
///   cannot key; its span is the node's place moved by `start`, and absent for
///   a node with no place.
/// - provides: the card that the render bus sends a client of the trace layer.
/// - fails: never.
/// - panics: none.
/// - intension: one read of the declaration's binders, then one one-line print
///   of each node's goal and type, so no goal is laid out and the work is
///   linear in the declaration's nodes and in the text of their lines.
///
/// # Adequacy
/// - hypothesis: L3 — an attached view of the trace layer hears the card of the
///   declaration at the editor's cursor, its first row the root at depth zero,
///   each goal written inside the declaration and each goal on one line within
///   its room.
/// - witness: `hub::tests::an_attached_view_follows_the_derivation_at_the_editors_cursor_6716`
#[spec(ensures: |ret| ret.rows.len() == derivation.nodes().len() && ret.columns == columns)]
#[must_use]
pub fn card(
    derivation: &Derivation<'_>,
    (key, declaration): (AccountKey, String),
    start: ByteOffset,
    columns: Count,
) -> DerivationCard
{
    let goals = derivation.goals();
    let rows = rows(derivation, start, |node, depth| {
        let room = Room::at(columns, depth);
        (
            match goals.goal(node, Lay::Line) {
                Maybe::Present(goal) => Some(elided(goal.as_ref().split_whitespace(), room.goal)),
                Maybe::Absent(_) => None,
            },
            match goals.ty(node, Lay::Line) {
                Maybe::Present(ty) => Some(elided(ty.as_ref().split_whitespace(), room.ty)),
                Maybe::Absent(_) => None,
            },
        )
    });
    DerivationCard {
        key,
        declaration,
        columns,
        rows,
    }
}

/// The whole goal of the node at `at` of `derivation`, laid out at `columns`:
/// none for a place past the tree or a goal that the printer refused.
///
/// # Specification
/// - requires: nothing; any place is admissible input.
/// - ensures: the goal of the node at `at` as the printer lays it out at a page
///   `columns` wide, with its line breaks.
/// - provides: the whole goal that a client of the trace layer opens.
/// - fails: never.
/// - panics: none.
/// - intension: one read of the declaration's binders and one layout, of the
///   one goal.
///
/// # Adequacy
/// - hypothesis: L3 — a view that opens the node at the cursor hears its whole
///   goal, and the row's line is that goal on one line.
/// - witness: `hub::tests::an_attached_view_follows_the_derivation_at_the_editors_cursor_6716`
#[must_use]
pub fn whole(
    derivation: &Derivation<'_>,
    at: NodeAt,
    columns: Count,
) -> Option<String>
{
    let node = derivation.nodes().get(at.0)?;
    let page = PageWidth::from(u32::try_from(columns.0).unwrap_or(u32::MAX));
    match derivation.goals().goal(node, Lay::Page(page)) {
        Maybe::Present(goal) => Some(alloc::format!("{goal}")),
        Maybe::Absent(_) => None,
    }
}

/// The hover's derivation section of `derivation` at `offset`, whose text
/// starts at byte `start`: one line for the row in focus and for each of its
/// ancestors, the root first, in a fenced block.
///
/// # Specification
/// - requires: `start` is the first byte of the declaration in the text that
///   the derivation's places count from.
/// - ensures: `None` when no row holds `offset`; otherwise a fenced block of
///   one line for each row that [`DerivationCard::ancestors`] names for the
///   focus, each set in by two spaces for each level of its depth, its goal and
///   its type whole on one line.
/// - provides: the section that a hover adds at the trace layer.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over the nodes to find the focus, then one one-line
///   print of the goal and the type of each row on its path.
///
/// # Adequacy
/// - hypothesis: L3 — a hover inside a traced declaration's body shows the
///   root's line first and the line of the node at the position last.
/// - witness: `server::tests::a_traced_hover_shows_the_node_at_the_cursor_and_its_ancestors_6295`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|text|
    text.starts_with("```text\n") && text.ends_with("```")))]
#[must_use]
pub fn section(
    derivation: &Derivation<'_>,
    start: ByteOffset,
    offset: ByteOffset,
) -> Option<String>
{
    let placed = DerivationCard {
        rows: rows(derivation, start, |_, _| (None, None)),
        ..DerivationCard::default()
    };
    let focus = placed.focus(offset)?;
    let goals = derivation.goals();
    let nodes = derivation.nodes();
    let mut section = String::from("```text\n");
    for at in placed.ancestors(focus) {
        let (Some(row), Some(node)) = (placed.rows.get(at.0), nodes.get(at.0))
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
        if let Maybe::Present(goal) = goals.goal(node, Lay::Line) {
            section.push(' ');
            joined(&mut section, goal.as_ref().split_whitespace());
        }
        if let Maybe::Present(ty) = goals.ty(node, Lay::Line) {
            section.push_str(" : ");
            joined(&mut section, ty.as_ref().split_whitespace());
        }
        let _written = writeln!(section, "  {}", row.rule);
    }
    section.push_str("```");
    Some(section)
}

/// One row for each node of `derivation`, whose text starts at byte `start`,
/// in the tree's order: each its goal and its type as `printed` writes them for
/// the node at its depth.
///
/// # Specification
/// trivial.
fn rows<Printed>(
    derivation: &Derivation<'_>,
    start: ByteOffset,
    mut printed: Printed,
) -> Vec<DerivationRow>
where
    Printed: FnMut(&DerivationNode, Count) -> (Option<String>, Option<String>),
{
    let count = |value: u32| Count(u64::from(value));
    let placed = |offset: gandr_surface_syntax::ByteOffset| {
        ByteOffset::from(usize::from(start).saturating_add(usize::from(offset)))
    };
    derivation
        .nodes()
        .iter()
        .map(|node| {
            let depth = count(u32::from(node.depth()));
            let (goal, ty) = printed(node, depth);
            DerivationRow {
                depth,
                warrant: match derivation.warrant(node) {
                    gandr_surface_session::Warrant::Checked => Warrant::Checked,
                    gandr_surface_session::Warrant::Replayed => Warrant::Replayed,
                    gandr_surface_session::Warrant::Refused => Warrant::Refused,
                },
                direction: match node.against() {
                    Maybe::Present(_) => Direction::Checking,
                    Maybe::Absent(_) => Direction::Synthesis,
                },
                goal,
                ty,
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
            }
        })
        .collect()
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
