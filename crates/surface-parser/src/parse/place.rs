//! Where a closer the source left out is minted.
//!
//! The melder closes a form the source never finished at the last point it
//! can, past every operand the form could still take, and a form read wrongly
//! takes the forms after it down with it. A closer left out early is minted
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
//! it. A source so repaired is read again from its first repair whose form
//! expects a `)` or a `]` next: the closer is written where the melder closed
//! the form, then at each tile end from the form's last written tile on,
//! nearest first, where it closes that form — every bracket of its family
//! opened since closed, save a doubled opener's second, and none between a name
//! and the bracket that opens its arguments — and the first copy whose
//! top-level form molds with no repair is the source as its author wrote it,
//! less the closer. Its tree, the written closer read back as a minted close,
//! is the parse, and that one repair stands for every repair the misreading
//! made. Where two places parse, as `f(x, y + 1` closed after `y` or after
//! `1`, the nearer is taken. A `}` left out is not read here: a block's closer
//! is placed by the layout, which the lowering reads.

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

use super::ParseResult;
use super::Repair;
use super::molded;
use super::ordered;
use super::repair;
use crate::closing::LeadingSlot;
use crate::closing::push_closing;
use crate::meld::Expected;
use crate::meld::Splice;
use crate::oblig::Oblig;
use crate::oblig::ObligationInstance;

/// The most places a closer is tried at, nearest the frontier first.
const PLACES: usize = 64;

/// A repair the search places: a form the melder closed, the closer it
/// expects next, and where its last written tile ends.
#[derive(Clone, Copy, Debug)]
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
    /// The closer the form expects next.
    closer: SourceText<'static>,
    /// Its family.
    class: ClosingClass,
}

impl Target
{
    /// The target `repair` names in `tree`, when its form expects a `)` or a
    /// `]` next.
    ///
    /// # Specification
    /// - requires: `repair` is an obligation of `tree`'s parse under `pbg`.
    /// - ensures: the target over the tile of a form spanning `repair`'s span,
    ///   with the sort of the close the melder minted in that form after it;
    ///   `None` when no tile spans it, no close follows it in its form, or the
    ///   form's cheapest closing, past any operand, does not begin with a `)`
    ///   or a `]`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the scan.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`placed`].
    /// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
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
        let (closer, class) = missing(pbg, mold)?;
        Some(Self {
            repair,
            end: repair.span.end(),
            leading,
            close: tree.node(ghost)?.span().start(),
            sort,
            closer,
            class,
        })
    }
}

/// `parsed`, with the closer its first placeable repair stands for minted
/// where the rest of its top-level form parses.
///
/// # Specification
/// - requires: `parsed` is a parse under `pbg`.
/// - ensures: for the first [`Oblig::MissingTile`] in source order that is a
///   [`Target`], when the target's closer written where the melder closed the
///   form, or else at the end of the form's last written tile or of a later
///   tile of its top-level form — every bracket of the closer's family opened
///   since closed, or the tile the second of two such openers, no closer of
///   that family before it closing a bracket opened earlier, and no `(` or `[`
///   next — leaves that form with no repair, the tree is the source's with the
///   closer minted, empty, at the first such place in that order — past a run
///   of the same closer written there — and the obligations are that repair and
///   the copy's others, shifted back over the closer; otherwise `parsed`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter list's `)` left out is minted after the
///   parameter's type; one left out of a rule's application is minted after its
///   nested application, never inside it, its misreading's other repairs gone;
///   one left out after a nested `)` is minted after it; and a block's `}` left
///   out at the end, which this does not read, stays where the melder minted
///   it.
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
pub(super) fn placed<'source>(
    pbg: &Pbg,
    parsed: ParseResult<'source>,
) -> ParseResult<'source>
{
    earlier(pbg, &parsed).unwrap_or(parsed)
}

/// `parsed` with its first placeable repair placed, if a place parses.
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
    let target = repairs
        .into_iter()
        .find_map(|repair| Target::of(pbg, tree, repair))?;
    let top = tree
        .children(tree.root())
        .filter_map(|position| tree.node(position))
        .map(Node::span)
        .find(|span| span.start() < target.end && target.end <= span.end())?;
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
    let mut places = Vec::new();
    if target.leading == LeadingSlot::Empty {
        places.push(target.end);
    }
    let (mut depth, mut doubled) = (0_usize, false);
    let mut previous: Option<ClosingClass> = None;
    for span in tiles {
        let spelling =
            DelimSpelling::from(text.get(usize::from(span.start()) .. usize::from(span.end()))?);
        let opening = ClosingClass::opening(spelling);
        if opening == Some(target.class) {
            depth = depth.saturating_add(1);
            doubled = previous == Some(target.class);
        }
        else if ClosingClass::closing(spelling) == Some(target.class) {
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
        let at_doubled = doubled && opening == Some(target.class);
        if !glued && (depth == 0 || at_doubled) {
            places.push(span.end());
        }
        previous = opening;
    }
    places.truncate(PLACES);
    places.insert(0, target.close);
    let place = places.into_iter().find(|&place| {
        written(source, top, place, target.closer)
            .is_some_and(|copy| repair(pbg, SourceText::from(copy.as_str())) == Repair::Unneeded)
    })?;
    let place = past(source, place, target.closer);
    let whole = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(text.len())).ok()?;
    let copy = written(source, whole, place, target.closer)?;
    let splice = Splice::new(place, target.closer, NodeLabel::GhostClose {
        sort: target.sort,
        class: target.class,
    })?;
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

/// The closer the form whose last written tile is of `mold` expects next,
/// past any operand, and its family, when that is a `)` or a `]`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the text and family of the first tile of the form's cheapest
///   closing with its operand slot occupied, when that tile is a `)` or a `]`;
///   `None` otherwise.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the reading.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
fn missing(
    pbg: &Pbg,
    mold: MoldId,
) -> Option<(SourceText<'static>, ClosingClass)>
{
    let mut material = Vec::new();
    let _reach = push_closing(pbg, mold, LeadingSlot::Occupied, &mut material);
    let Some(&Expected::Tile(label)) = material.first()
    else {
        return None;
    };
    let class = ClosingClass::closing(DelimSpelling::from(label))?;
    match class {
        ClosingClass::Paren | ClosingClass::Bracket => Some((SourceText::from(label), class)),
        ClosingClass::Brace => None,
    }
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
}
