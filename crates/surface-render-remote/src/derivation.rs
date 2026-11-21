//! The derivation card: the judgement nodes of one declaration, one row for
//! each node in the order the checker met them, and the rows that the
//! derivation pane shows at a cursor.
//!
//! A [`DerivationCard`] names the declaration by its content key, as an
//! account card does, and states the columns that its rows were cut to. A
//! [`DerivationRow`] holds the node's depth, its warrant, its direction, its
//! goal and its type on one line each, cut to the [`Room`] that the pane gives
//! them at those columns, the rule's short name, the cover, the memo's mark,
//! the nodes that the check visited, the wall of the node, and the bytes of
//! the document where the goal is written. A field that the producer does not
//! know is absent and takes no bytes on the wire.
//!
//! # A row holds what the pane shows
//!
//! The pane shows each goal and each type on one line, cut to its column, so
//! the producer prints only that line and never lays a goal out. The pane
//! shows a whole goal only for the node in focus, and only when the user opens
//! it: the client then asks for that one goal with an `open` frame, and the
//! producer lays it out at the card's columns and answers with an `opened`
//! frame. So a card of many deep goals costs one line for each row, and one
//! layout for each goal that a user opens.
//!
//! # The pane follows the cursor
//!
//! The node in focus is the row with the fewest bytes that hold the cursor,
//! the deeper of two such rows ([`DerivationCard::focus`]). The search reads
//! each row once, because the form of the declaration's type can hold the
//! whole declaration and a lambda holds only its binder's bytes. The focus
//! and its ancestors are open, and every other node folds to one line
//! ([`DerivationCard::shown`]), skipped by its count of nodes. So a cursor
//! that moves inside one declaration changes the rows shown and not the card,
//! and a folded subtree costs one line.
//!
//! The hub sends the whole card when the declaration at the cursor or its
//! tree changes, and nothing when it stays the same. A cursor that moves
//! inside the declaration sends no card.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;

use crate::account::AccountKey;
use crate::present::ByteOffset;
use crate::present::ByteRange;
use crate::visual::Count;
use crate::visual::Glyph;
use crate::visual::Warrant;

/// The direction of a judgement: checking against a type the context gives,
/// or synthesis of a type. A formation synthesises its universe.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Direction
{
    /// The node is checked against a type: `⇐`.
    Checking,
    /// The node synthesises its type: `⇒`.
    Synthesis,
}

impl Direction
{
    /// The direction's glyph, one of the derivation's glyphs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn glyph(self) -> Glyph
    {
        Glyph::from(match self {
            Self::Checking => "⇐",
            Self::Synthesis => "⇒",
        })
    }
}

/// What the goal memo did for a node that it could key.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Memo
{
    /// The memo held the goal's answer: `=`.
    Hit,
    /// The memo keyed the goal and held no answer: `·`.
    Miss,
}

impl Memo
{
    /// The mark's glyph, one of the derivation's glyphs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn glyph(self) -> Glyph
    {
        Glyph::from(match self {
            Self::Hit => "=",
            Self::Miss => "·",
        })
    }
}

/// One judgement node of a derivation card.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DerivationRow
{
    /// The depth in the tree: zero at a root.
    pub depth: Count,
    /// The node's warrant: checked, replayed or refused.
    pub warrant: Warrant,
    /// Whether the node checks or synthesises.
    pub direction: Direction,
    /// The goal on one line, cut to the room of its column at its depth with
    /// an ellipsis at the end when it is longer ([`Room`]). Absent when the
    /// printer refused it.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub goal: Option<String>,
    /// The type the node is checked against or synthesised, on one line and
    /// cut the same way; absent when the node holds none or the printer
    /// refused it.
    #[cfg_attr(
        feature = "serde",
        serde(rename = "type", default, skip_serializing_if = "Option::is_none")
    )]
    pub ty: Option<String>,
    /// The short name of the rule that judged the node.
    pub rule: String,
    /// The count of binders that the node's memo key reads.
    pub cover: Count,
    /// What the memo did for the node; absent for a node that it cannot key.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub memo: Option<Memo>,
    /// The nodes that the check visited: this node and each node under it.
    pub nodes: Count,
    /// The wall of the node, in nanoseconds.
    pub wall: Count,
    /// The bytes of the document where the goal is written; absent where the
    /// lowering kept no place for the node.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<ByteRange>,
}

/// The place of a row in its card, counted from zero in pre-order.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeAt(pub usize);

/// The columns of a derivation pane that a goal and its type do not take: the
/// warrant, the direction, the rule, the cover, the memo, the nodes, the wall
/// and the spaces between the nine columns.
pub const FIXED: Count = Count(35);

/// The columns that a row of a derivation pane gives its goal and its type.
///
/// # Specification
/// - ensures: in a pane of `columns`, the type takes half of what [`FIXED`]
///   leaves, and the goal takes the same less two columns for each level of its
///   depth, which the pane sets it in by.
/// - provides: the one rule by which the producer cuts a row and the pane draws
///   it, so the two agree.
///
/// # Adequacy
/// - hypothesis: L3 — a row two levels deep in a pane of 80 columns gives its
///   type 22 columns and its goal 18.
/// - witness: `derivation::tests::a_row_is_cut_to_the_room_of_its_column`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Room
{
    /// The columns of the goal.
    pub goal: Count,
    /// The columns of the type.
    pub ty: Count,
}

impl Room
{
    /// The room of a row at `depth` in a pane `columns` wide.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(
        columns: Count,
        depth: Count,
    ) -> Self
    {
        let ty = match columns.0.saturating_sub(FIXED.0).checked_div(2) {
            Some(half) => Count(half),
            None => Count(0),
        };
        Self {
            goal: Count(ty.0.saturating_sub(depth.0.saturating_mul(2))),
            ty,
        }
    }
}

/// The text of `words` on one line, one space between two words, and cut to
/// `room` columns with an ellipsis at the end when it is longer; a room under
/// two columns counts as two.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the words joined by single spaces when they fit; otherwise the
///   first `room - 1` characters of them and an ellipsis, `room` characters in
///   all. A text that this cut leaves cuts to itself again.
/// - provides: the cut of a row's goal and type, the same in the producer and
///   in the pane.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Room`].
/// - witness: `derivation::tests::a_row_is_cut_to_the_room_of_its_column`
#[spec(ensures: |ret| ret.chars().count() <= usize::try_from(room.0).unwrap_or(usize::MAX).max(2))]
#[inline]
#[must_use]
pub fn elided(
    words: core::str::SplitWhitespace<'_>,
    room: Count,
) -> String
{
    let mut line = String::new();
    for (at, word) in words.enumerate() {
        if at > 0 {
            line.push(' ');
        }
        line.push_str(word);
    }
    let room = usize::try_from(room.0).unwrap_or(usize::MAX).max(2);
    if line.chars().count() > room {
        let cut = line
            .char_indices()
            .nth(room.saturating_sub(1))
            .map_or(line.len(), |(at, _)| at);
        line.truncate(cut);
        line.push('…');
    }
    line
}

/// The judgement nodes of one declaration, in the order the checker met them:
/// each node is followed by the nodes under it, then by its siblings.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct DerivationCard
{
    /// The declaration's key, as its account card names it.
    pub key: AccountKey,
    /// The declaration's name.
    pub declaration: String,
    /// The columns of the pane that the rows were cut for.
    pub columns: Count,
    /// The nodes, in pre-order.
    pub rows: Vec<DerivationRow>,
}

impl DerivationCard
{
    /// The place of the row just after the subtree at `at`, which the subtree's
    /// count of nodes gives, and at least the place after `at`.
    ///
    /// # Specification
    /// trivial.
    fn past(
        &self,
        at: NodeAt,
    ) -> NodeAt
    {
        let nodes = self.rows.get(at.0).map_or(1, |row| {
            usize::try_from(row.nodes.0).unwrap_or(usize::MAX).max(1)
        });
        NodeAt(at.0.saturating_add(nodes))
    }

    /// The row in focus at `offset`: of the rows whose bytes hold the offset,
    /// the one with the fewest bytes. The form of a declaration's type and the
    /// root of its body can both hold the whole declaration, and a lambda's
    /// bytes are its binder's, so no walk down from a root finds the node the
    /// cursor is in: each row is read once instead.
    ///
    /// # Specification
    /// - requires: nothing; a card whose spans do not nest is admissible input.
    /// - ensures: `None` when no row holds `offset`; otherwise a row whose
    ///   bytes hold it, from the start to the end inclusive, with no row that
    ///   holds it in fewer bytes. Of two such rows, the deeper one is the
    ///   focus, and the first on a tie.
    /// - provides: the node that the pane opens at the cursor.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the rows, which reads each row once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — in a tree of nested spans, an offset inside a leaf
    ///   focuses the leaf, an offset inside its parent and outside the leaf
    ///   focuses the parent, and an offset outside every root focuses none. Two
    ///   roots that hold the whole declaration do not take the focus from a
    ///   node of the second root's subtree.
    /// - witness: `derivation::tests::the_focus_is_the_deepest_node_at_the_cursor`
    #[spec(ensures: |ret| ret.is_none_or(|at| at.0 < self.rows.len()))]
    #[inline]
    #[must_use]
    pub fn focus(
        &self,
        offset: ByteOffset,
    ) -> Option<NodeAt>
    {
        self.rows
            .iter()
            .enumerate()
            .filter_map(|(at, row)| {
                row.span
                    .filter(|span| span.start() <= offset && offset <= span.end())
                    .map(|span| {
                        let width =
                            usize::from(span.end()).saturating_sub(usize::from(span.start()));
                        (at, width, row.depth)
                    })
            })
            .reduce(|focus, next| {
                if next.1 < focus.1 || (next.1 == focus.1 && next.2 > focus.2) {
                    next
                }
                else {
                    focus
                }
            })
            .map(|(at, ..)| NodeAt(at))
    }

    /// The row at `at` and each of its ancestors, the root first.
    ///
    /// # Specification
    /// - requires: nothing; any index is admissible input.
    /// - ensures: empty for an index past the rows; otherwise ascending indices
    ///   that end at `at`, each row one shallower than the next.
    /// - provides: the open path of the pane and the lines of the hover's
    ///   derivation section.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`DerivationCard::shown`].
    /// - witness: `derivation::tests::the_pane_opens_the_path_and_folds_each_sibling`
    #[spec(ensures: |ret| ret.last().is_none_or(|&last| last == at) && ret.is_sorted())]
    #[inline]
    #[must_use]
    pub fn ancestors(
        &self,
        at: NodeAt,
    ) -> Vec<NodeAt>
    {
        let mut path = Vec::new();
        let Some(row) = self.rows.get(at.0)
        else {
            return path;
        };
        path.push(at);
        let mut depth = row.depth;
        let mut index = at.0;
        while depth > Count(0)
            && let Some(before) = index.checked_sub(1)
        {
            index = before;
            if let Some(row) = self.rows.get(index)
                && row.depth < depth
            {
                path.push(NodeAt(index));
                depth = row.depth;
            }
        }
        path.reverse();
        path
    }

    /// The rows that the pane shows with `focus` in focus, in order: each
    /// root, and each child of a row on the path from a root to the focus.
    /// Every other row folds into the row of the subtree that holds it.
    ///
    /// # Specification
    /// - requires: nothing; any focus is admissible input.
    /// - ensures: ascending indices of rows; the first row when there is one;
    ///   with a focus, the focus and each of its ancestors and children; with
    ///   none, the roots alone.
    /// - provides: the rows of the derivation pane.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one step for each row shown, and a folded subtree is
    ///   skipped by its count of nodes, so the work is linear in the rows shown
    ///   and the path.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — in a tree of two roots, the focus at a grandchild
    ///   shows the roots, the children of the first root, and the children of
    ///   the focus's parent, and folds the rest.
    /// - witness: `derivation::tests::the_pane_opens_the_path_and_folds_each_sibling`
    #[spec(ensures: |ret| ret.is_sorted() && ret.first().is_none_or(|&first| first == NodeAt(0)))]
    #[inline]
    #[must_use]
    pub fn shown(
        &self,
        focus: Option<NodeAt>,
    ) -> Vec<NodeAt>
    {
        let path = focus.map_or_else(Vec::new, |at| self.ancestors(at));
        let mut shown = Vec::new();
        let mut at = NodeAt(0);
        while at.0 < self.rows.len() {
            shown.push(at);
            at = if path.binary_search(&at).is_ok() {
                NodeAt(at.0.saturating_add(1))
            }
            else {
                self.past(at)
            };
        }
        shown
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use super::DerivationCard;
    use super::DerivationRow;
    use super::Direction;
    use super::NodeAt;
    use super::Room;
    use super::elided;
    use crate::present::ByteOffset;
    use crate::present::ByteRange;
    use crate::visual::Count;
    use crate::visual::Warrant;

    /// A pane of 80 columns gives a type 22 columns and a root's goal 22, and
    /// a goal two levels deep 18. A goal that fits keeps its words on one line;
    /// a longer one is cut to the room with an ellipsis, and the cut text cuts
    /// to itself. A room that set the goal in by the wrong amount, or a cut
    /// one character off, changes a line here.
    #[test]
    fn a_row_is_cut_to_the_room_of_its_column()
    {
        assert_eq!(Room::at(Count(80), Count(2)), Room {
            goal: Count(18),
            ty: Count(22),
        });
        assert_eq!(Room::at(Count(30), Count(0)), Room {
            goal: Count(0),
            ty: Count(0),
        });
        assert_eq!(elided("a +\n  b".split_whitespace(), Count(18)), "a + b");
        let cut = elided("let a = { x + y } ; a".split_whitespace(), Count(10));
        assert_eq!(cut, "let a = {…");
        assert_eq!(elided(cut.split_whitespace(), Count(10)), cut);
        assert_eq!(elided("abc".split_whitespace(), Count(0)), "a…");
    }

    /// A row at `depth` over `nodes` nodes, written at `span`.
    ///
    /// # Specification
    /// trivial.
    fn node(
        depth: Count,
        nodes: Count,
        span: ByteRange,
    ) -> DerivationRow
    {
        DerivationRow {
            depth,
            warrant: Warrant::Checked,
            direction: Direction::Checking,
            goal: Some(String::from("g")),
            ty: None,
            rule: String::from("Lambda"),
            cover: Count(0),
            memo: None,
            nodes,
            wall: Count(0),
            span: Some(span),
        }
    }

    /// The card of `rows`, each a depth, a count of nodes and the start and the
    /// end of its bytes.
    ///
    /// # Specification
    /// trivial.
    fn card_of(rows: &[(Count, Count, (ByteOffset, ByteOffset))]) -> DerivationCard
    {
        DerivationCard {
            rows: rows
                .iter()
                .map(|&(depth, nodes, (start, end))| {
                    node(
                        depth,
                        nodes,
                        ByteRange::new(start, end).expect("an ordered run"),
                    )
                })
                .collect(),
            ..DerivationCard::default()
        }
    }

    /// Two roots: the first at 0..40 with children at 0..10 (two leaves) and
    /// 12..40 (one leaf at 20..30), the second at 50..60 with one leaf.
    ///
    /// # Specification
    /// trivial.
    fn card() -> DerivationCard
    {
        let row = |depth: u64, nodes: u64, (start, end): (usize, usize)| {
            (
                Count(depth),
                Count(nodes),
                (ByteOffset::from(start), ByteOffset::from(end)),
            )
        };
        card_of(&[
            row(0, 6, (0, 40)),
            row(1, 3, (0, 10)),
            row(2, 1, (0, 4)),
            row(2, 1, (5, 10)),
            row(1, 2, (12, 40)),
            row(2, 1, (20, 30)),
            row(0, 2, (50, 60)),
            row(1, 1, (52, 58)),
        ])
    }

    #[test]
    fn the_focus_is_the_deepest_node_at_the_cursor()
    {
        let card = card();
        let at = |offset: usize| card.focus(ByteOffset::from(offset));
        assert_eq!(
            at(25),
            Some(NodeAt(5)),
            "an offset in a leaf focuses the leaf"
        );
        assert_eq!(
            at(15),
            Some(NodeAt(4)),
            "an offset in a node and in none of its children focuses the node"
        );
        assert_eq!(
            at(7),
            Some(NodeAt(3)),
            "the second leaf of a pair is found past the first"
        );
        assert_eq!(
            at(54),
            Some(NodeAt(7)),
            "the search passes over the first root's subtree"
        );
        assert_eq!(at(45), None, "an offset outside every root focuses none");
        // The type's form and the body's root both hold the declaration; the
        // lambda holds only its binder, and the node under it the cursor.
        let row = |depth: u64, nodes: u64, (start, end): (usize, usize)| {
            (
                Count(depth),
                Count(nodes),
                (ByteOffset::from(start), ByteOffset::from(end)),
            )
        };
        let formed = card_of(&[
            row(0, 1, (0, 60)),
            row(0, 4, (0, 60)),
            row(1, 3, (6, 7)),
            row(2, 2, (12, 20)),
            row(3, 1, (12, 20)),
        ]);
        assert_eq!(
            formed.focus(ByteOffset::from(15_usize)),
            Some(NodeAt(4)),
            "neither the type's form nor a binder's span hides the node at the cursor, and the deeper of two equal spans is the focus"
        );
    }

    #[test]
    fn the_pane_opens_the_path_and_folds_each_sibling()
    {
        let card = card();
        let places =
            |places: &[usize]| -> Vec<NodeAt> { places.iter().copied().map(NodeAt).collect() };
        assert_eq!(
            card.ancestors(NodeAt(5)),
            places(&[0, 4, 5]),
            "a leaf's path starts at its root"
        );
        assert_eq!(
            card.ancestors(NodeAt(9)),
            places(&[]),
            "an index past the rows has none"
        );
        assert_eq!(
            card.shown(Some(NodeAt(5))),
            places(&[0, 1, 4, 5, 6]),
            "the path is open, the first child's leaves fold into it, and the second root is one line"
        );
        assert_eq!(
            card.shown(Some(NodeAt(1))),
            places(&[0, 1, 2, 3, 4, 6]),
            "a focus at a node lists its children"
        );
        assert_eq!(
            card.shown(None),
            places(&[0, 6]),
            "with no focus each root is one line"
        );
    }
}
