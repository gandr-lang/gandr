//! Where a tile the source left out is minted.
//!
//! The melder closes a form the source never finished at the last point it
//! can, past every operand the form could still take, and a form read wrongly
//! takes the forms after it down with it. A tile left out early is minted
//! late. In
//!
//! ```text
//! def once(n : Integer -> -F Integer {
//!   return n
//! }
//! ```
//!
//! the parameter list's `)` is gone, and `n : Integer -> -F Integer` is a
//! parameter, so the definition takes the block as well and is closed after
//! it. A source so repaired is read again from a repaired form: the tile that
//! form takes next is written at each place of its top-level form, nearest
//! first, and the first copy that molds with no repair is the source as its
//! author wrote it, less the tile. Its tree, the written tile read back as
//! minted, is the parse, and that one repair stands for every repair the
//! misreading made. The forms tried are the first a `)` or a `]` closes, the
//! deepest of the others and the first of the others. A `)` or a `]` is tried
//! where the melder closed the form, then at each tile end from the form's last
//! written tile on where it closes that form — every bracket of its family
//! opened since closed, save a doubled opener's second, and none between a name
//! and the bracket that opens its arguments; where two places parse, as
//! `f(x, y + 1` closed after `y` or after `1`, the nearer is taken. Any other
//! tile the form may take — a member's `;`, an arm's `=>`, a binder's `:`, an
//! `else` — is tried directly after the form's last written tile when no hole
//! comes between them and that tile opens no bracket, else at each later tile
//! end outside the brackets opened since and never inside a word, and its copy
//! must read the tiles before it as the source does, keep every top-level form
//! a declaration and nest the form no deeper. A `}` left out is not read here:
//! a block's closer is placed by the layout, which the lowering reads.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::GroutShape;
use gandr_surface_syntax::GroutSort;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_graphs::Bound;

use super::ParseResult;
use super::Repair;
use super::molded;
use super::ordered;
use super::repair;
use crate::closing::LeadingSlot;
use crate::closing::push_closing;
use crate::meld::Expected;
use crate::meld::Splice;
use crate::meld::declaration_head;
use crate::meld::primitive_copy_wrapper;
use crate::oblig::Oblig;
use crate::oblig::ObligationInstance;

/// The most places a closer is tried at, nearest the frontier first.
const PLACES: usize = 64;

/// The most copies the search molds for one repair of a tile other than a
/// closer, in the order it tries them.
const COPIES: usize = 16;

primitive_copy_wrapper!(
    /// How many forms enclose a span of a tree.
    struct Enclosure(usize);
);
primitive_copy_wrapper!(
    /// Whether a copy reads the bytes a tile is written at as that one tile.
    struct Tiled(bool);
);
primitive_copy_wrapper!(
    /// Whether every top-level form a copy reads is a declaration.
    struct Declared(bool);
);

/// A repair the search places: a form the melder closed, the tiles it may
/// take next, and where its last written tile ends.
#[derive(Clone, Debug)]
struct Target
{
    /// The repair, over the form's last written tile.
    repair: ObligationInstance,
    /// Where that tile ends.
    end: ByteOffset,
    /// Whether an operand of the form stands after that tile.
    leading: LeadingSlot,
    /// Where the melder minted the form's close.
    close: ByteOffset,
    /// The sort of the form, which its minted close carries.
    sort: GroutSort,
    /// The tiles the form may take next past an operand, tried in this order.
    closers: Vec<SourceText<'static>>,
    /// The tiles the form may take directly after that tile, tried at its end
    /// in this order before any later place.
    adjacent: Vec<SourceText<'static>>,
    /// Its family, when it closes a bracket.
    class: Option<ClosingClass>,
    /// How many forms enclose the form.
    depth: Enclosure,
}

impl Target
{
    /// The target `repair` names in `tree`, when its form may take a tile
    /// next.
    ///
    /// # Specification
    /// - requires: `repair` is an obligation of `tree`'s parse under `pbg`.
    /// - ensures: the target over the tile of a form spanning `repair`'s span,
    ///   with the sort of the close the melder minted in that form after it,
    ///   the tiles [`missing`] names for that tile and the count of forms
    ///   enclosing it; `None` when no tile spans it, no close follows it in its
    ///   form, or [`missing`] names none.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the scan.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`placed`].
    /// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
    /// - witness: `parse::place::tests::a_tile_left_out_is_minted_where_the_rest_parses_2259`
    fn of(
        pbg: &Pbg,
        tree: &SyntaxTree<'_>,
        repair: ObligationInstance,
    ) -> Option<Self>
    {
        let spans = |child: &NodeIndex| {
            tree.node(*child).is_some_and(|node| {
                node.span() == repair.span && matches!(node.label(), NodeLabel::Tile(_))
            })
        };
        let form = tree
            .positions()
            .find(|&position| tree.children(position).any(|child| spans(&child)))?;
        let children: Vec<NodeIndex> = tree.children(form).collect();
        let index = children.iter().position(spans)?;
        let NodeLabel::Tile(mold) = tree.node(*children.get(index)?)?.label()
        else {
            return None;
        };
        let after = children.get(index.saturating_add(1) ..).unwrap_or_default();
        let (ghost, sort) = after
            .iter()
            .find_map(|&child| minted(tree.node(child)?).map(|sort| (child, sort)))?;
        let leading = if after.first().is_some_and(|&next| next != ghost) {
            LeadingSlot::Occupied
        }
        else {
            LeadingSlot::Empty
        };
        let (closers, adjacent, class) = missing(pbg, mold)?;
        let depth = enclosing(tree, repair.span.start(), repair.span.end());
        Some(Self {
            repair,
            end: repair.span.end(),
            leading,
            close: tree.node(ghost)?.span().start(),
            sort,
            closers,
            adjacent,
            class,
            depth,
        })
    }
}

/// `parsed`, with the tile one of its placeable repairs stands for minted where
/// the rest of its top-level form parses.
///
/// # Specification
/// - requires: `parsed` is a parse under `pbg`.
/// - ensures: of the [`Oblig::MissingTile`] repairs that are [`Target`]s, the
///   first in source order whose tile is a `)` or a `]`, then of the others the
///   one whose form is deepest, the first in source order among equals, then
///   the first other in source order: the first of these whose tile written at
///   one of its places — the first [`PLACES`] and the melder's close for a `)`
///   or a `]`, the first [`COPIES`] copies for another tile — leaves its
///   top-level form with no repair. A `)` or a `]` is written where the melder
///   closed the form, or else at the end of the form's last written tile or of
///   a later tile of its top-level form — every bracket of the closer's family
///   opened since closed, or the tile the second of two such openers, no closer
///   of that family before it closing a bracket opened earlier, and no `(` or
///   `[` next. Any other tile no hole faces on the left is written at the end
///   of the form's last written tile, with no word character next and unless
///   that tile opens a bracket; then one a hole faces on the left at the end of
///   a later tile outside every bracket opened since, with no word character,
///   `(` or `[` next; either copy reads the tiles before it with the source's
///   molds, each of its top-level forms a declaration, the repair's form under
///   no more forms than in the source. The tree is the source's with the tile
///   minted, empty, at the first such place in that order — past a run of the
///   same tile written there — a minted close for a bracket and an empty
///   postfix grout otherwise, and the obligations are that repair and the
///   copy's others, shifted back over the tile; otherwise `parsed`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter list's `)` left out is minted after the
///   parameter's type; one left out of a rule's application is minted after its
///   nested application, never inside it, its misreading's other repairs gone;
///   one left out after a nested `)` is minted after it; a block's `}` left out
///   at the end, which this does not read, stays where the melder minted it; a
///   member's `;` left out is minted at the end of its line, an arm's `=>`
///   after its pattern and never inside it, a binder's `:` after its name and
///   never after its type, an `else` after the first block; and a definition's
///   last `;` left out at the end of the source is never minted inside its
///   body.
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
/// - witness: `parse::place::tests::a_tile_left_out_is_minted_where_the_rest_parses_2259`
pub(super) fn placed<'source>(
    pbg: &Pbg,
    parsed: ParseResult<'source>,
) -> ParseResult<'source>
{
    earlier(pbg, &parsed).unwrap_or(parsed)
}

/// `parsed` with a placeable repair placed, if a place parses.
///
/// # Specification
/// - requires: as [`placed`].
/// - ensures: as [`placed`], `None` where it returns `parsed`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
/// - witness: `parse::place::tests::a_tile_left_out_is_minted_where_the_rest_parses_2259`
fn earlier<'source>(
    pbg: &Pbg,
    parsed: &ParseResult<'source>,
) -> Option<ParseResult<'source>>
{
    let tree = &parsed.tree;
    let mut repairs: Vec<ObligationInstance> = parsed
        .obligations
        .iter()
        .copied()
        .filter(|obligation| obligation.class == Oblig::MissingTile)
        .collect();
    repairs.sort_unstable_by_key(|obligation| (obligation.span.start(), obligation.span.end()));
    let targets: Vec<Target> = repairs
        .into_iter()
        .filter_map(|repair| Target::of(pbg, tree, repair))
        .collect();
    let bracket = targets.iter().find(|target| target.class.is_some());
    let others: Vec<&Target> = targets
        .iter()
        .filter(|target| target.class.is_none())
        .collect();
    let deepest = others
        .iter()
        .enumerate()
        .min_by_key(|&(_, target)| core::cmp::Reverse(target.depth))
        .map(|(at, _)| at);
    let first = deepest.filter(|&at| at != 0).and_then(|_| others.first());
    bracket
        .into_iter()
        .chain(deepest.and_then(|at| others.get(at)).copied())
        .chain(first.copied())
        .find_map(|target| settled(pbg, tree, target))
}

/// The parse with `target`'s tile minted where the rest of its top-level form
/// parses, if a place tried does: for a closer, the melder's close and the
/// first [`PLACES`] tile ends; for another tile, the first [`COPIES`] copies.
///
/// # Specification
/// - requires: `target` is a [`Target`] of `tree`'s parse under `pbg`.
/// - ensures: as [`placed`] for that target; `None` where no copy tried parses.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn settled<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    target: &Target,
) -> Option<ParseResult<'source>>
{
    let top = tree
        .children(tree.root())
        .filter_map(|position| tree.node(position))
        .map(Node::span)
        .find(|span| span.start() < target.end && target.end <= span.end())?;
    let lead = usize::from(top.start());
    let shifted = |offset: ByteOffset| usize::from(offset).checked_sub(lead).map(ByteOffset::from);
    let (repair_start, repair_end) = (
        shifted(target.repair.span.start())?,
        shifted(target.repair.span.end())?,
    );
    let source = tree.source();
    let text = <&str>::from(source);
    let mut tiles: Vec<ByteSpan> = tree
        .positions()
        .filter_map(|position| tree.node(position))
        .filter(|node| matches!(node.label(), NodeLabel::Tile(_)))
        .map(Node::span)
        .filter(|span| target.end < span.end() && span.end() <= top.end())
        .collect();
    tiles.sort_unstable_by_key(|span| (span.start(), span.end()));
    let word_next = |offset: ByteOffset| {
        text.as_bytes()
            .get(usize::from(offset))
            .is_some_and(|&next| next.is_ascii_alphanumeric() || next == b'_')
    };
    let mut places = Vec::new();
    if target.leading == LeadingSlot::Empty && target.class.is_some() {
        places.push(target.end);
    }
    let (mut depth, mut doubled) = (0_usize, false);
    let mut previous: Option<ClosingClass> = None;
    for span in tiles {
        let spelling =
            DelimSpelling::from(text.get(usize::from(span.start()) .. usize::from(span.end()))?);
        let opening = ClosingClass::opening(spelling);
        let closing = ClosingClass::closing(spelling);
        let counted = |class: Option<ClosingClass>| {
            class.is_some() && (target.class.is_none() || class == target.class)
        };
        if counted(opening) {
            depth = depth.saturating_add(1);
            doubled = target.class.is_some() && previous == target.class;
        }
        else if counted(closing) {
            let Some(shallower) = depth.checked_sub(1)
            else {
                break;
            };
            depth = shallower;
        }
        let glued = matches!(
            text.as_bytes().get(usize::from(span.end())).copied(),
            Some(b'(' | b'[')
        );
        let at_doubled = doubled && opening == target.class;
        let split = target.class.is_none() && word_next(span.end());
        if !glued && !split && (depth == 0 || at_doubled) {
            places.push(span.end());
        }
        previous = opening;
    }
    places.truncate(PLACES);
    if target.class.is_some() {
        places.insert(0, target.close);
    }
    let adjacent = if word_next(target.end) {
        &[][..]
    }
    else {
        target.adjacent.as_slice()
    };
    let (place, closer) = adjacent
        .iter()
        .map(|&closer| (target.end, closer))
        .chain(
            places
                .iter()
                .flat_map(|&place| target.closers.iter().map(move |&closer| (place, closer))),
        )
        .take(target.class.map_or(COPIES, |_| PLACES.saturating_add(1)))
        .find(|&(place, closer)| {
            let tile = shifted(place).and_then(|at| {
                Some((
                    at,
                    ByteOffset::from(usize::from(at).checked_add(<&str>::from(closer).len())?),
                ))
            });
            written(source, top, place, closer).is_some_and(|copy| {
                let copy = SourceText::from(copy.as_str());
                repair(pbg, copy) == Repair::Unneeded
                    && molded(pbg, copy).commit_with_obligations(copy).is_ok_and(
                        |(copied, _repairs)| {
                            tile.is_some_and(|(at, end)| bool::from(tiled(&copied, at, end)))
                                && (target.class.is_some()
                                    || (bool::from(declared(pbg, &copied))
                                        && enclosing(&copied, repair_start, repair_end)
                                            <= target.depth
                                        && tile.is_some_and(|(at, _end)| {
                                            kept(tree, top.start(), place)
                                                == kept(&copied, ByteOffset::from(0_usize), at)
                                        })))
                        },
                    )
            })
        })?;
    let place = past(source, place, closer);
    let whole = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(text.len())).ok()?;
    let copy = written(source, whole, place, closer)?;
    let leaf = target.class.map_or(
        NodeLabel::Grout {
            sort: target.sort,
            shape: GroutShape::Postfix,
        },
        |class| NodeLabel::GhostClose {
            sort: target.sort,
            class,
        },
    );
    let splice = Splice::new(place, closer, leaf)?;
    let (tree, copied) = molded(pbg, SourceText::from(copy.as_str()))
        .commit_spliced(source, splice)
        .ok()?;
    let mut obligations: Vec<ObligationInstance> = copied
        .into_iter()
        .map(|obligation| splice.obligation(obligation))
        .collect();
    obligations.push(target.repair);
    ordered(&mut obligations);
    Some(ParseResult { tree, obligations })
}

/// The tiles of `tree` from `from` up to `upto`, each with its span measured
/// from `from`, in source order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every [`NodeLabel::Tile`] starting at or after `from` and ending
///   at or before `upto`, its span less `from`, sorted by span.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn kept(
    tree: &SyntaxTree<'_>,
    from: ByteOffset,
    upto: ByteOffset,
) -> Vec<(ByteSpan, NodeLabel)>
{
    let (from, upto) = (usize::from(from), usize::from(upto));
    let mut tiles: Vec<(ByteSpan, NodeLabel)> = tree
        .positions()
        .filter_map(|position| tree.node(position))
        .filter(|node| matches!(node.label(), NodeLabel::Tile(_)))
        .filter_map(|node| {
            let (start, end) = (
                usize::from(node.span().start()),
                usize::from(node.span().end()),
            );
            (from <= start && end <= upto)
                .then(|| {
                    let span = ByteSpan::new(
                        ByteOffset::from(start.checked_sub(from)?),
                        ByteOffset::from(end.checked_sub(from)?),
                    )
                    .ok()?;
                    Some((span, node.label()))
                })
                .flatten()
        })
        .collect();
    tiles.sort_unstable_by_key(|&(span, _)| (span.start(), span.end()));
    tiles
}

/// Whether `copied` reads its bytes `at .. end` as one tile.
///
/// # Specification
/// - requires: nothing.
/// - ensures: true exactly when some [`NodeLabel::Tile`] of `copied` spans `at
///   .. end`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn tiled(
    copied: &SyntaxTree<'_>,
    at: ByteOffset,
    end: ByteOffset,
) -> Tiled
{
    Tiled::from(
        copied
            .positions()
            .filter_map(|position| copied.node(position))
            .any(|node| {
                matches!(node.label(), NodeLabel::Tile(_))
                    && node.span().start() == at
                    && node.span().end() == end
            }),
    )
}

/// Whether every top-level form `copied` reads is a declaration, its layout
/// and documentation aside.
///
/// # Specification
/// - requires: nothing.
/// - ensures: true exactly when every child of the root that is neither
///   [`NodeLabel::Space`] nor [`NodeLabel::Doc`] is a [`NodeLabel::Meld`] whose
///   mold [`declaration_head`] accepts.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn declared(
    pbg: &Pbg,
    copied: &SyntaxTree<'_>,
) -> Declared
{
    Declared::from(
        copied
            .children(copied.root())
            .filter_map(|position| copied.node(position))
            .all(|node| match node.label() {
                NodeLabel::Space | NodeLabel::Doc => true,
                NodeLabel::Meld(mold) => bool::from(declaration_head(pbg, mold)),
                NodeLabel::Wald
                | NodeLabel::Tile(_)
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. } => false,
            }),
    )
}

/// How many forms of `tree` enclose `start .. end`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the count of [`NodeLabel::Meld`] nodes whose span holds `start ..
///   end`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the count.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn enclosing(
    tree: &SyntaxTree<'_>,
    start: ByteOffset,
    end: ByteOffset,
) -> Enclosure
{
    Enclosure::from(
        tree.positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| {
                matches!(node.label(), NodeLabel::Meld(_))
                    && node.span().start() <= start
                    && end <= node.span().end()
            })
            .count(),
    )
}

/// The sort a close the melder minted carries, when `node` is one: a minted
/// close or an empty postfix grout.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the sort of a [`NodeLabel::GhostClose`], or of an empty
///   [`GroutShape::Postfix`] grout; `None` for any other node.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the match.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn minted(node: &Node) -> Option<GroutSort>
{
    let empty = node.span().start() == node.span().end();
    match node.label() {
        NodeLabel::GhostClose { sort, .. } => Some(sort),
        NodeLabel::Grout {
            sort,
            shape: GroutShape::Postfix,
        } if empty => Some(sort),
        NodeLabel::Wald
        | NodeLabel::Meld(_)
        | NodeLabel::Tile(_)
        | NodeLabel::Grout { .. }
        | NodeLabel::Space
        | NodeLabel::Doc => None,
    }
}

/// The tiles the form whose last written tile is of `mold` may take next —
/// past an operand, then directly after that tile — and their family when they
/// close a bracket.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first tile of the form's cheapest closing with its operand
///   slot occupied and its family, when that tile is a `)` or a `]`, and none
///   directly after; else every distinct tile that may follow `mold` in its
///   form and neither opens nor closes a bracket, in successor order, with no
///   family: first those a hole faces on the left, then, unless `mold` opens a
///   bracket, those none does; `None` when there is none.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the reading.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
/// - witness: `parse::place::tests::a_tile_left_out_is_minted_where_the_rest_parses_2259`
fn missing(
    pbg: &Pbg,
    mold: MoldId,
) -> Option<(
    Vec<SourceText<'static>>,
    Vec<SourceText<'static>>,
    Option<ClosingClass>,
)>
{
    let mut material = Vec::new();
    let _reach = push_closing(pbg, mold, LeadingSlot::Occupied, &mut material);
    if let Some(&Expected::Tile(label)) = material.first()
        && let Some(class @ (ClosingClass::Paren | ClosingClass::Bracket)) =
            ClosingClass::closing(DelimSpelling::from(label))
    {
        return Some((
            Vec::from([SourceText::from(label)]),
            Vec::new(),
            Some(class),
        ));
    }
    let (mut past, mut adjacent): (Vec<SourceText<'static>>, Vec<SourceText<'static>>) =
        (Vec::new(), Vec::new());
    let (mut seen_past, mut seen_adjacent) = (BTreeSet::new(), BTreeSet::new());
    let opens = pbg
        .mold(mold)
        .is_ok_and(|def| ClosingClass::opening(DelimSpelling::from(def.label)).is_some());
    for &(_, next) in pbg.mold_successors(mold) {
        let Ok(def) = pbg.mold(next)
        else {
            continue;
        };
        let spelling = DelimSpelling::from(def.label);
        if ClosingClass::opening(spelling).is_some() || ClosingClass::closing(spelling).is_some() {
            continue;
        }
        let label = SourceText::from(def.label);
        if matches!(pbg.bounds(next), Ok((Bound::Value(_), _))) {
            if seen_past.insert(def.label) {
                past.push(label);
            }
        }
        else if !opens && seen_adjacent.insert(def.label) {
            adjacent.push(label);
        }
    }
    (!past.is_empty() || !adjacent.is_empty()).then_some((past, adjacent, None))
}

/// `place`, past every `tile` the source writes there: the same copy, read
/// with the written tiles before the one left out.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first offset at or after `place` the source does not write
///   `tile` at, counting in whole tiles.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the walk.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn past(
    source: SourceText<'_>,
    place: ByteOffset,
    tile: SourceText<'_>,
) -> ByteOffset
{
    let (text, tile) = (<&str>::from(source), <&str>::from(tile));
    let mut at = usize::from(place);
    while !tile.is_empty() && text.get(at ..).is_some_and(|rest| rest.starts_with(tile)) {
        at = at.saturating_add(tile.len());
    }
    ByteOffset::from(at)
}

/// The bytes of `source` within `within`, with `tile` written at `place`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `source`'s bytes from `within`'s start to `place`, `tile`, then
///   its bytes from `place` to `within`'s end; `None` when `place` lies outside
///   `within` or off a character boundary.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the concatenation.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn written(
    source: SourceText<'_>,
    within: ByteSpan,
    place: ByteOffset,
    tile: SourceText<'_>,
) -> Option<String>
{
    let text = <&str>::from(source);
    let tile = <&str>::from(tile);
    let before = text.get(usize::from(within.start()) .. usize::from(place))?;
    let after = text.get(usize::from(place) .. usize::from(within.end()))?;
    let mut copy = String::with_capacity(
        before
            .len()
            .saturating_add(tile.len())
            .saturating_add(after.len()),
    );
    copy.push_str(before);
    copy.push_str(tile);
    copy.push_str(after);
    Some(copy)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceText;

    use crate::oblig::Oblig;
    use crate::parse;
    use crate::testing::reconstruct;

    /// #2242: a closer the source left out is minted where the rest of its
    /// form parses, not after everything the form could still take.
    #[test]
    fn a_closer_left_out_is_minted_where_the_rest_parses_2242()
    {
        let pbg = built_in().unwrap();
        let after = |source: &str, written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        let once = "def once(n : Integer -> -F Integer {\n  return n\n}\n";
        let glued = "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n  P : (x : Int) --> \
                     Int;\n  rule S(P(x) <=> x;\n}\n";
        let head = "def head(xs : List(Integer) -> -F Integer {\n  return 0\n}\n";
        let open = "def once(n : Integer) -> -F Integer {\n  return n\n";
        for (source, at, class, why) in [
            (
                once,
                after(once, "n : Integer"),
                ClosingClass::Paren,
                "the parameter list's `)` is minted after the parameter's type, where the \
                 definition's return type and block then parse",
            ),
            (
                glued,
                after(glued, "S(P(x)"),
                ClosingClass::Paren,
                "a rule's `)` left out is minted after its nested application, not between \
                 the nested operation's name and its arguments, and its misreading's other \
                 repairs are gone",
            ),
            (
                head,
                after(head, "List(Integer)"),
                ClosingClass::Paren,
                "a `)` left out after a nested `)` is minted after the written one: the copy \
                 is the same text either way",
            ),
            (
                open,
                after(open, "return n"),
                ClosingClass::Brace,
                "a block's `}` left out at the end, which the layout places, stays where the \
                 melder minted it",
            ),
        ] {
            let parsed = parse(&pbg, SourceText::from(source)).unwrap();
            let tree = parsed.tree();
            let minted: Vec<_> = tree
                .positions()
                .filter_map(|position| tree.node(position))
                .filter_map(|node| match node.label() {
                    NodeLabel::GhostClose { class, .. } => Some((class, node.span())),
                    NodeLabel::Wald
                    | NodeLabel::Meld(_)
                    | NodeLabel::Tile(_)
                    | NodeLabel::Grout { .. }
                    | NodeLabel::Space
                    | NodeLabel::Doc => None,
                })
                .collect();
            assert_eq!(minted.len(), 1, "{why}: {minted:?}");
            let (minted_class, span) = minted.first().copied().unwrap();
            assert_eq!(
                (minted_class, span.start(), span.end()),
                (class, ByteOffset::from(at), ByteOffset::from(at)),
                "{why}"
            );
            assert_eq!(
                reconstruct(tree),
                source,
                "{why}: the tree reconstructs the source"
            );
            assert!(
                matches!(parsed.obligations(), [repair] if repair.class == Oblig::MissingTile),
                "{why}: one repair stands: {:?}",
                parsed.obligations()
            );
        }
    }

    /// #2259: a tile other than a bracket the source left out is minted where
    /// the rest of its form parses, and never where a copy parses only by
    /// reading the source around it differently.
    #[test]
    fn a_tile_left_out_is_minted_where_the_rest_parses_2259()
    {
        let pbg = built_in().unwrap();
        let after = |source: &str, written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        let member = "data Circle : Type {\n  Base : Circle\n  loop : Base <-> Base;\n}\n";
        let arm = "def classify(n : Integer) -> -F Integer {\n  case n {\n    ?branch  return \
                   1\n  }\n}\n";
        let branch = "def pick(b : Bool) -> -F Integer {\n  if b { return 1 }  { return 2 }\n}\n";
        let last = "def twice : Integer ;\ndef twice = loop then loop \n";
        let binder = "data Stack : Type {\n  Empty : Stack;\n  Push : (x  Integer, rest : Stack) --> \
             Stack;\n}\n";
        for (source, at, why) in [
            (
                member,
                after(member, "Base : Circle"),
                "a member's `;` left out is minted at the end of its line, and the member after \
                 it reads as written",
            ),
            (
                arm,
                after(arm, "?branch"),
                "an arm's `=>` left out is minted after its pattern, never between the pattern's \
                 `?` and its name",
            ),
            (
                binder,
                after(binder, "(x"),
                "a binder's `:` left out is minted after its name, which it follows with no \
                 operand between, never after the type",
            ),
        ] {
            let parsed = parse(&pbg, SourceText::from(source)).unwrap();
            let tree = parsed.tree();
            assert_eq!(
                minted(tree),
                [ByteOffset::from(at)],
                "{why}: {:?}",
                parsed.obligations()
            );
            assert_eq!(
                reconstruct(tree),
                source,
                "{why}: the tree reconstructs the source"
            );
            assert!(
                matches!(parsed.obligations(), [repair] if repair.class == Oblig::MissingTile),
                "{why}: one repair stands: {:?}",
                parsed.obligations()
            );
        }
        let parsed = parse(&pbg, SourceText::from(branch)).unwrap();
        let tree = parsed.tree();
        let written = branch.find("if").map(ByteOffset::from);
        assert!(
            tree.positions()
                .filter_map(|position| tree.node(position))
                .any(|node| matches!(node.label(), NodeLabel::Meld(_))
                    && Some(node.span().start()) == written),
            "a tile never fuses with the word before it: `else` written after `if` would read \
             `ifelse` as a name, and the `if` keeps its form"
        );
        let parsed = parse(&pbg, SourceText::from(last)).unwrap();
        assert!(
            !minted(parsed.tree()).contains(&ByteOffset::from(after(last, "= loop"))),
            "a definition's last `;` left out is never minted inside its body, where \
             `(def twice = loop;) then loop` would read"
        );
    }

    /// A try that stops molding at its first repair answers as the whole
    /// molding and commit do, over every prefix of sources whole, missing a
    /// closer and carrying one too many: each prefix leaves its forms open
    /// at another point, so repairs stream early, late and only at the
    /// close.
    #[test]
    fn a_try_stopped_at_its_first_repair_answers_as_a_whole_parse()
    {
        let pbg = built_in().unwrap();
        let mut repaired = 0_usize;
        let mut clean = 0_usize;
        for source in [
            "def once(n : Integer) -> -F Integer {\n  return n\n}\n",
            "def once(n : Integer -> -F Integer {\n  return n\n}\n",
            "def once(n : Integer)) -> -F Integer {\n  return n\n}\n",
            "def head(xs : List(Integer) -> -F Integer {\n  return 0\n}\n",
            "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n  rule S(P(x) <=> x;\n}\n",
            "def pair = f(x, [y, z], (w)) ;\n",
        ] {
            for end in (0 ..= source.len()).filter(|&end| source.is_char_boundary(end)) {
                let prefix = SourceText::from(source.get(.. end).unwrap());
                let whole = super::molded(&pbg, prefix)
                    .commit_with_obligations(prefix)
                    .is_ok_and(|(_tree, obligations)| obligations.is_empty());
                assert_eq!(
                    super::repair(&pbg, prefix) == super::Repair::Unneeded,
                    whole,
                    "{:?}: the stopped molding and the whole one disagree",
                    <&str>::from(prefix)
                );
                if whole {
                    clean = clean.saturating_add(1);
                }
                else {
                    repaired = repaired.saturating_add(1);
                }
            }
        }
        assert!(
            clean > 0 && repaired > 0,
            "both answers are exercised: {clean} clean, {repaired} repaired"
        );
    }

    /// Where `tree` mints a tile that is no bracket: its empty postfix grouts.
    ///
    /// # Specification
    /// trivial.
    fn minted(tree: &gandr_surface_syntax::SyntaxTree<'_>) -> Vec<ByteOffset>
    {
        tree.positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| {
                matches!(node.label(), NodeLabel::Grout {
                    shape: GroutShape::Postfix,
                    ..
                }) && node.span().start() == node.span().end()
            })
            .map(|node| node.span().start())
            .collect()
    }
}
