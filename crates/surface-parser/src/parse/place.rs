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
//! deepest of the others and the first of the others. A declaration the melder
//! cannot close can leave its keyword and the tiles after it as top-level
//! forms of their own: in `def quiet : Prog (Either StateOp Void Integer = Op;`
//! the group reads `= Op` as an equality, and `def quiet :` stands apart. When
//! no copy of a form alone parses and the gap before each line places no tile,
//! the search runs again over the first four forms a `)` or a `]` closes and
//! the same two others. Then each copy starts at such a keyword, so that it
//! holds the whole declaration, and a later bracket's form without one is
//! copied alone. The gap goes first: a field whose `(` its line leaves open
//! owes the `)` on that line, though a copy from the keyword can parse with
//! the `)` on a later line. A `)` or a `]` is tried where the melder closed
//! the form, then at each tile end from
//! the form's last written tile on where it closes that form — every bracket
//! of its family opened since closed, save a doubled opener's second, and none
//! between a name and the bracket that opens its arguments; where two places
//! parse, as `f(x, y + 1` closed after `y` or after `1`, the nearer is taken. A
//! place that parts an operand from the argument the melder applies it to is
//! tried after the next place, so the `)` of `S (P x <=> x;` comes after `P x`.
//! The melder can close the form at the end of its last written tile, before an
//! operand that follows the tile. A closer there expels that operand, so that
//! place is not tried. Any other tile the form may take — a member's `;`, an
//! arm's `=>`, a binder's `:`, an `else` — is tried directly after the form's
//! last written tile when no hole comes between them and that tile opens no
//! bracket, else at each later tile end outside the brackets opened since and
//! never inside a word, and its copy must read the tiles before it as the
//! source does, keep every top-level form a declaration and nest the form no
//! deeper. A form that the layout ends before a later top-level form takes its
//! end from a separator of no bytes, as `def f(n : N) -> N n` without its `=`
//! does, and a copy of that form alone has no such separator. When no copy
//! molds with no repair, each copy is tried again with the separator written
//! after it, and the tile is minted only where one copy alone parses. A `}`
//! left out is not read here: a block's closer is placed by the layout, which
//! the lowering reads.
//!
//! A top-level form whose declaration keyword is left out or misspelled,
//! `def1 f(x : T) -> …`, reads as an expression. The root holds declarations
//! alone, so the melder reads its words as strays and its brackets as
//! expressions of their own, with no repair. Each run of top-level forms that
//! read as no declaration is read again with a keyword written before a form
//! of the run, each keyword that form's first tile can follow. The first copy
//! that makes the rest of the run declarations with no repair is the parse.
//! The keyword is minted at the head of that form as an empty prefix grout and
//! owed alone. The search above then runs over that parse.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::cell::Cell;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::CloseReach;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::GroutShape;
use gandr_surface_syntax::GroutSort;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Dir;

use super::ParseResult;
use super::molded;
use super::spliced;
use super::unrepaired;
use crate::MeldState;
use crate::Molder;
use crate::TokenIndex;
use crate::TokenRun;
use crate::closing::LeadingSlot;
use crate::closing::push_closing;
use crate::label::Token;
use crate::label::cut_in;
use crate::label::label;
use crate::meld::BOUNDARY_SORT;
use crate::meld::Expected;
use crate::meld::Splice;
use crate::meld::declaration_head;
use crate::meld::primitive_copy_wrapper;
use crate::mold::KEYWORDS;
use crate::mold::Molding;
use crate::mold::lookahead_reach;
use crate::oblig::Oblig;
use crate::oblig::ObligationInstance;

/// The most places a closer is tried at, nearest the frontier first.
const PLACES: usize = 64;

/// The most copies the search molds for one repair of a tile other than a
/// closer, in the order it tries them.
const COPIES: usize = 16;

/// The most brackets left open whose closer the last search places, in source
/// order.
const BRACKETS: usize = 4;

/// Which search over a parse's targets runs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Pass
{
    /// The first bracket left open, the deepest other target and the first
    /// other, each copied from its top-level form alone.
    First,
    /// After the gap places no tile: the first [`BRACKETS`] brackets left open
    /// and the same two others, each copied from its declaration's keyword.
    Last,
}

/// How far back a copy of a target's top-level form reaches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The copy holds the top-level form alone.
    Form,
    /// The copy starts at the keyword of the form's declaration, which the
    /// melder leaves as a top-level tile before the form ([`keyword`]). A form
    /// with no such keyword is not copied.
    Declaration,
    /// The copy starts at that keyword when there is one, and holds the form
    /// alone otherwise.
    Widest,
}

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
        // A node's span covers its children's, so the tile's parent is a root,
        // or a top-level form covering the repair or one of its descendants,
        // which the layout keeps as one range.
        let covers = |position: NodeIndex| {
            tree.node(position).is_some_and(|node| {
                node.span().start() <= repair.span.start() && repair.span.end() <= node.span().end()
            })
        };
        let forms = tree.forms();
        let first = forms.partition_point(|&form| {
            tree.node(form)
                .is_some_and(|node| node.span().end() < repair.span.start())
        });
        let holders = forms
            .get(first ..)
            .unwrap_or_default()
            .iter()
            .copied()
            .take_while(|&form| {
                tree.node(form)
                    .is_some_and(|node| node.span().start() <= repair.span.end())
            })
            .filter(|&form| covers(form))
            .flat_map(|form| {
                core::iter::once(form).chain(tree.descendants(form).into_iter().flatten())
            });
        let form = tree
            .roots()
            .iter()
            .copied()
            .chain(holders)
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
///   closed the form, unless that is the end of the form's last written tile
///   and the tile after it closes no bracket and opens no declaration. Else it
///   is written at the end of the form's last written tile or of a later tile
///   of its top-level form — every bracket of the closer's family opened since
///   closed, or the tile the second of two such openers, no closer of that
///   family before it closing a bracket opened earlier, and no `(` or `[` next.
///   A place with an application tile next is tried after the next place. Any
///   other tile no hole faces on the left is written at the end of the form's
///   last written tile, with no word character next and unless that tile opens
///   a bracket; then one a hole faces on the left at the end of a later tile
///   outside every bracket opened since, with no word character, `(` or `[`
///   next; either copy reads the tiles before it with the source's molds, each
///   of its top-level forms a declaration, the repair's form under no more
///   forms than in the source. When no copy of such a tile molds with no repair
///   and a separator of no bytes ends its top-level form before a later one
///   ([`lost_separator`]), each copy is tried again with that separator written
///   after it, and the tile is placed only where one copy alone leaves no
///   repair. The tree is the source's with the tile minted, empty — past a run
///   of the same tile written there — a minted close for a bracket at the last
///   such place in the source, reaching back to the first such place, and an
///   empty postfix grout otherwise at the first such place in that order, and
///   the obligations are that repair and the copy's others, shifted back over
///   the tile. A declaration's keyword left out at the head of a top-level form
///   is placed first ([`headed`]), and the search above runs over that parse.
///   Where the search places no tile, the gap before each line places the
///   separators and closers it shows ([`super::gap::gapped`]). Where the gap
///   places none either, the search runs again over the first [`BRACKETS`]
///   targets whose tile is a `)` or a `]` and the same two others. Each copy
///   then starts at the keyword of the target's declaration that the melder
///   leaves as a top-level tile before its top-level form ([`keyword`]). A
///   target the first search tried is not copied again without that keyword,
///   and a later bracket's form without one is copied alone. This search keeps
///   a copy only where its parse owes fewer obligations than `parsed`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter list's `)` left out before a return type is
///   minted after the type it makes, reaching back to the parameter's type; one
///   left out of a rule's application is minted after its nested application,
///   never inside it, its misreading's other repairs gone; one left out after a
///   nested `)` is minted after it; a block's `}` left out at the end, which
///   this does not read, stays where the melder minted it; a member's `;` left
///   out is minted at the end of its line, an arm's `=>` after its pattern and
///   never inside it, a binder's `:` after its name and never after its type,
///   an `else` after the first block; a definition's `=` left out, whose form
///   the layout's separator before the next declaration ends, after its result
///   type; a type's `)` left out of a declaration that the melder breaks apart,
///   before its `=`, and the inner `)` of a result type that the outer bracket
///   takes at no place; and a definition's last `;` left out at the end of the
///   source is never minted inside its body.
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
/// - witness: `parse::place::tests::a_closer_left_out_of_a_broken_declaration_is_minted_where_it_parses_5837`
/// - witness: `parse::place::tests::a_tile_left_out_is_minted_where_the_rest_parses_2259`
/// - witness: `parse::place::tests::a_tile_a_form_the_layout_ends_lacks_is_minted_where_one_copy_parses_5938`
/// - witness: `parse::place::tests::a_declaration_keyword_left_out_is_minted_at_its_head_2440`
/// - witness: `parse::gap::tests::a_separator_left_out_before_a_line_at_its_items_column_is_minted_5433`
pub(super) fn placed<'source>(
    pbg: &Pbg,
    parsed: ParseResult<'source>,
) -> ParseResult<'source>
{
    let parsed = headed(pbg, &parsed).unwrap_or(parsed);
    earlier(pbg, &parsed, Pass::First)
        .or_else(|| super::gap::gapped(pbg, &parsed))
        .or_else(|| earlier(pbg, &parsed, Pass::Last))
        .unwrap_or(parsed)
}

/// `parsed` with a placeable repair placed, if a place parses, over the targets
/// and with the copies `pass` names.
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
/// - witness: `parse::place::tests::a_closer_left_out_of_a_broken_declaration_is_minted_where_it_parses_5837`
/// - witness: `parse::place::tests::a_tile_left_out_is_minted_where_the_rest_parses_2259`
fn earlier<'source>(
    pbg: &Pbg,
    parsed: &ParseResult<'source>,
    pass: Pass,
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
    // The reach of a target the first search tried, then of one it did not.
    let (count, tried, fresh) = match pass {
        Pass::First => (1, Reach::Form, Reach::Form),
        Pass::Last => (BRACKETS, Reach::Declaration, Reach::Widest),
    };
    let brackets = targets
        .iter()
        .filter(|target| target.class.is_some())
        .take(count)
        .enumerate()
        .map(|(at, target)| (target, if at == 0 { tried } else { fresh }));
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
    brackets
        .chain(
            deepest
                .and_then(|at| others.get(at))
                .map(|&target| (target, tried)),
        )
        .chain(first.map(|&target| (target, tried)))
        .find_map(|(target, reach)| {
            settled(pbg, tree, target, reach).filter(|placed| match pass {
                Pass::First => true,
                Pass::Last => placed.obligations.len() < parsed.obligations.len(),
            })
        })
}

/// `parsed` with a declaration's keyword minted at the head of a run of
/// top-level forms that read as no declaration, when written there it parses.
///
/// A form whose keyword is left out or misspelled, as `def1 f(x : T) -> …`,
/// reads as an expression. The root holds declarations alone, so the melder
/// reads its words as strays side by side and its brackets as expressions of
/// their own, with no repair. Of the runs of top-level forms that read as no
/// declaration, each form whose first tile a declaration keyword takes next is
/// tried run by run in source order, and within a run from its last form back,
/// with each such keyword written before that tile, a space after it, in mold
/// order, the first [`COPIES`] copies in all. Each copy spans the form and the
/// rest of its run. A run that holds no repair takes `def` alone.
///
/// # Specification
/// - requires: `parsed` is a parse under `pbg`.
/// - ensures: the first such copy that molds with no repair as declarations
///   alone is the parse: the source's tree read from the whole copy, the
///   keyword an empty prefix grout at its first tile and its space empty there,
///   with one [`Oblig::MissingTile`] over that tile beside the copy's other
///   obligations, shifted back over the keyword; `None` where no copy tried
///   parses.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — a definition whose `def` is misspelled, or left out at
///   the start of the source, reads as one declaration owing its keyword alone,
///   minted at its name and never at the misspelled word; a call at the top
///   level with a repair of its own that no keyword makes a declaration keeps
///   its reading.
/// - witness: `parse::place::tests::a_declaration_keyword_left_out_is_minted_at_its_head_2440`
fn headed<'source>(
    pbg: &Pbg,
    parsed: &ParseResult<'source>,
) -> Option<ParseResult<'source>>
{
    let tree = &parsed.tree;
    let source = tree.source();
    let whole = ByteSpan::new(
        ByteOffset::from(0_usize),
        ByteOffset::from(<&str>::from(source).len()),
    )
    .ok()?;
    // A top-level form, with whether it reads as a declaration. A grout or a
    // minted close there ends a run as a declaration does.
    let read = |position: NodeIndex| {
        let node = tree.node(position)?;
        let declaration = match node.label() {
            NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
                bool::from(declaration_head(pbg, mold))
            },
            NodeLabel::Space | NodeLabel::Doc => return None,
            NodeLabel::Wald | NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } => true,
        };
        Some((position, node.span(), declaration))
    };
    // A source of declarations alone, as every clean one is, allocates
    // nothing here.
    if tree
        .children(tree.root())
        .filter_map(read)
        .all(|(_, _, declaration)| declaration)
    {
        return None;
    }
    let forms: Vec<(NodeIndex, ByteSpan, bool)> =
        tree.children(tree.root()).filter_map(read).collect();
    // Each form that reads as no declaration, beside the first form of its
    // run: the runs in source order and, within a run, its last form first,
    // so the keyword stands at the name a misspelled keyword stands before.
    let mut starts: Vec<(usize, usize)> = Vec::new();
    let mut head = 0_usize;
    for (at, &(_, _, declaration)) in forms.iter().enumerate() {
        if declaration {
            head = at.saturating_add(1);
        }
        else {
            starts.push((head, at));
        }
    }
    starts.sort_unstable_by_key(|&(head, at)| (head, core::cmp::Reverse(at)));
    let mut written_keyword = String::new();
    starts
        .iter()
        .filter_map(|&(_, at)| {
            let &(position, span, _) = forms.get(at)?;
            let end = forms
                .get(at ..)
                .unwrap_or_default()
                .iter()
                .take_while(|&&(_, _, declaration)| !declaration)
                .last()
                .map_or_else(|| span.end(), |&(_, last, _)| last.end());
            let run = ByteSpan::new(span.start(), end).ok()?;
            // A run with no repair reads as expressions the lowering refuses.
            // It owes `def` alone, where a definition's shape follows its
            // first word: another keyword reads `same Integer answer ;` as
            // its own declaration, though the run is an expression.
            let repaired = parsed.obligations.iter().any(|obligation| {
                run.start() <= obligation.span.start() && obligation.span.end() <= run.end()
            });
            let (lead, lead_span) = first_tile(tree, position)?;
            Some(
                heads(pbg, lead)
                    .into_iter()
                    .filter(move |&keyword| repaired || <&str>::from(keyword) == "def")
                    .map(move |keyword| (run, lead_span, keyword)),
            )
        })
        .flatten()
        .take(COPIES)
        .find_map(|(run, lead, keyword)| {
            let place = lead.start();
            written_keyword.clear();
            written_keyword.push_str(<&str>::from(keyword));
            written_keyword.push(' ');
            let tile = SourceText::from(written_keyword.as_str());
            let copied = written(source, run, place, tile, SourceText::from(""))?;
            let copied = SourceText::from(copied.as_str());
            let declaration = unrepaired(pbg, copied)?;
            if !bool::from(declared(pbg, &declaration)) {
                return None;
            }
            let copy = written(source, whole, place, tile, SourceText::from(""))?;
            let splice = Splice::new(place, tile, NodeLabel::Grout {
                sort: BOUNDARY_SORT.grout_sort(),
                shape: GroutShape::Prefix,
            })?;
            spliced(
                molded(pbg, SourceText::from(copy.as_str())),
                source,
                &[splice],
                [ObligationInstance::new(Oblig::MissingTile, lead)],
            )
        })
}

/// The first tile of the form at `position`, read down its first children.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the mold and span of the tile reached from `position` through
///   each node's first significant child; `None` where that walk meets anything
///   but a form or a tile.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the walk.
///
/// # Adequacy
/// - hypothesis: L3 — as [`headed`].
/// - witness: `parse::place::tests::a_declaration_keyword_left_out_is_minted_at_its_head_2440`
fn first_tile(
    tree: &SyntaxTree<'_>,
    position: NodeIndex,
) -> Option<(MoldId, ByteSpan)>
{
    let mut at = position;
    loop {
        let node = tree.node(at)?;
        match node.label() {
            NodeLabel::Tile(mold) => return Some((mold, node.span())),
            NodeLabel::Meld(_) => {
                at = tree.children(at).find(|&child| {
                    tree.node(child)
                        .is_some_and(|child| bool::from(child.label().significance()))
                })?;
            },
            NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => return None,
        }
    }
}

/// The declaration keywords whose next tile `lead`'s label spells, in mold
/// order, each once.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the reserved spellings of the molds [`declaration_head`] accepts
///   that a `≐`-successor with `lead`'s label follows, first occurrence kept.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — as [`headed`].
/// - witness: `parse::place::tests::a_declaration_keyword_left_out_is_minted_at_its_head_2440`
fn heads(
    pbg: &Pbg,
    lead: MoldId,
) -> Vec<SourceText<'static>>
{
    let Ok(lead) = pbg.mold(lead).map(|def| def.label)
    else {
        return Vec::new();
    };
    let adjacencies = pbg.adjacencies();
    let named = |mold: MoldId| {
        let from = adjacencies.partition_point(|&(left, _right)| left < mold);
        adjacencies
            .get(from ..)
            .unwrap_or_default()
            .iter()
            .take_while(|&&(left, _right)| left == mold)
            .any(|&(_left, right)| pbg.mold(right).is_ok_and(|next| next.label == lead))
    };
    let mut keywords: Vec<(MoldId, SourceText<'static>)> = KEYWORDS
        .iter()
        .filter_map(|&keyword| {
            pbg.candidates(TileLabel(keyword))
                .iter()
                .copied()
                .find(|&mold| bool::from(declaration_head(pbg, mold)) && named(mold))
                .map(|mold| (mold, SourceText::from(keyword)))
        })
        .collect();
    keywords.sort_unstable_by_key(|&(mold, _keyword)| mold);
    keywords
        .into_iter()
        .map(|(_mold, keyword)| keyword)
        .collect()
}

/// A top-level form's own molding, which every copy of it the search tries
/// shares up to where the copy's tokens part from the form's.
///
/// A molding of a run reads the stream only up to its
/// [`lookahead_reach`], so a copy's tokens before the latest position whose
/// reach stops short of the first token the copy changes mold as the form's
/// own. The form is molded once, as far as the copies need it, and a copy
/// molds only from there: a copy that halts at a repair has its pushes rolled
/// back, and one that molds whole is committed from the molding, which then
/// starts over.
///
/// # Specification
/// - requires: `state` holds `tokens` up to `molded`, molded from a fresh state
///   over `text`, which `tokens` labels.
/// - ensures: as [`Shared::copy`].
/// - fails: never.
/// - panics: none.
/// - executable: none — this carrier has no call boundary; [`Shared::copy`]
///   carries the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Shared::copy`].
/// - witness: `parse::place::tests::a_resumed_copy_answers_as_a_fresh_one`
struct Shared<'pbg, 'text>
{
    /// The molder every molding here runs.
    molder: Molder<'pbg>,
    /// The form's own molding, `molded` tokens in.
    state: MeldState<'pbg>,
    /// The form's text.
    text: SourceText<'text>,
    /// The form's tokens.
    tokens: Vec<Token>,
    /// How many of `tokens` `state` holds.
    molded: TokenIndex,
    /// Whether the last token molded left a repair.
    halted: Molding,
}

impl<'pbg, 'text> Shared<'pbg, 'text>
{
    /// The form `text`, none of it molded yet.
    ///
    /// # Specification
    /// trivial.
    fn new(
        pbg: &'pbg Pbg,
        text: SourceText<'text>,
    ) -> Self
    {
        Self {
            molder: Molder::new(pbg),
            state: MeldState::new(pbg),
            text,
            tokens: label(SourceFragment::from(<&str>::from(text))),
            molded: TokenIndex::from(0_usize),
            halted: Molding::Whole,
        }
    }

    /// The tree `copy`, the form with one tile written in, parses to when it
    /// parses with no repair, read from the form's own molding as far as the
    /// copy shares it and committed from it when the copy molds whole.
    ///
    /// # Specification
    /// - requires: `copy` is the form's text with a tile written in, and with a
    ///   separator written after it or none.
    /// - ensures: what [`unrepaired`] answers of `copy`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates a fresh molding of `copy`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every copy the search tries over the sources the
    ///   placement's witnesses read, and over every one-token drop of a corpus
    ///   source, answers as its fresh molding.
    /// - witness: `parse::place::tests::a_resumed_copy_answers_as_a_fresh_one`
    fn copy<'copy>(
        &mut self,
        copy: SourceText<'copy>,
    ) -> Option<SyntaxTree<'copy>>
    {
        let copied = label(SourceFragment::from(<&str>::from(copy)));
        let form = <&str>::from(self.text).as_bytes();
        let same = form
            .iter()
            .zip(<&str>::from(copy).as_bytes())
            .take_while(|&(left, right)| left == right)
            .count();
        // The first token the copy changes: one the form's differs from, or
        // one that reaches past the bytes the two share.
        let parted = copied
            .iter()
            .zip(&self.tokens)
            .position(|(left, right)| {
                left != right || usize::try_from(left.end).map_or(true, |end| end > same)
            })
            .unwrap_or_else(|| copied.len().min(self.tokens.len()));
        let mut resume = parted;
        while resume > 0 && usize::from(lookahead_reach(&copied, TokenIndex::from(resume))) > parted
        {
            resume = resume.saturating_sub(1);
        }
        if resume < usize::from(self.molded) {
            self.state = MeldState::new(self.molder.pbg());
            self.molded = TokenIndex::from(0_usize);
            self.halted = Molding::Whole;
        }
        while self.halted == Molding::Whole && usize::from(self.molded) < resume {
            let next = TokenIndex::from(usize::from(self.molded).saturating_add(1));
            self.halted = self.molder.mold_run_until_repair(
                &mut self.state,
                &self.tokens,
                TokenRun::new(self.molded, next),
                self.text,
            );
            self.molded = next;
        }
        if self.halted == Molding::Halted {
            return None;
        }
        let mark = self.state.mark();
        let molding = self.molder.mold_run_until_repair(
            &mut self.state,
            &copied,
            TokenRun::new(self.molded, TokenIndex::from(copied.len())),
            copy,
        );
        if molding == Molding::Halted {
            self.state.rollback_to(&mark);
            return None;
        }
        // The molding holds the whole copy: commit it, and mold the form
        // afresh for the next copy.
        let whole = core::mem::replace(&mut self.state, MeldState::new(self.molder.pbg()));
        self.molded = TokenIndex::from(0_usize);
        self.halted = Molding::Whole;
        let (tree, obligations) = whole.commit_with_obligations(copy).ok()?;
        obligations.is_empty().then_some(tree)
    }
}

/// Where the declaration that holds the top-level form `form` starts, when the
/// melder leaves the declaration's keyword as a top-level tile before `form`.
///
/// A declaration the melder cannot close can leave its keyword as a bare tile
/// at the root, before the form. The walk back stops at the first top-level
/// form whose first tile opens a declaration: a bare tile there is the
/// keyword, and a meld there is the declaration before, which the copy leaves
/// out.
///
/// # Specification
/// - requires: `form` is a child of `tree`'s root, and `tree` molds under
///   `pbg`.
/// - ensures: the start of the last top-level form before `form` whose first
///   tile opens a declaration, when that form is a bare tile; `None` otherwise.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the walk.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_of_a_broken_declaration_is_minted_where_it_parses_5837`
fn keyword(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    form: NodeIndex,
) -> Option<ByteOffset>
{
    let before: Vec<NodeIndex> = tree
        .children(tree.root())
        .take_while(|&position| position != form)
        .collect();
    let (position, span) = before.iter().rev().find_map(|&position| {
        let (mold, span) = first_tile(tree, position)?;
        bool::from(declaration_head(pbg, mold)).then_some((position, span))
    })?;
    tree.node(position)
        .is_some_and(|node| matches!(node.label(), NodeLabel::Tile(_)))
        .then_some(span.start())
}

/// The parse with `target`'s tile minted where the rest of its top-level form
/// parses, the copy reaching as far back as `reach` says, if a place tried
/// does: for a closer, the melder's close and the first [`PLACES`] tile ends;
/// for another tile, the first [`COPIES`] copies, then, when none molds with no
/// repair, those copies with the separator the form lost written after them
/// ([`lost_separator`]).
///
/// # Specification
/// - requires: `target` is a [`Target`] of `tree`'s parse under `pbg`.
/// - ensures: as [`placed`] for that target; `None` where no copy tried parses,
///   or `reach` is [`Reach::Declaration`] and [`keyword`] finds no keyword.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
/// - witness: `parse::place::tests::a_closer_left_out_of_a_broken_declaration_is_minted_where_it_parses_5837`
/// - witness: `parse::place::tests::a_tile_a_form_the_layout_ends_lacks_is_minted_where_one_copy_parses_5938`
fn settled<'source>(
    pbg: &Pbg,
    tree: &SyntaxTree<'source>,
    target: &Target,
    reach: Reach,
) -> Option<ParseResult<'source>>
{
    let (form, held) = tree
        .children(tree.root())
        .filter_map(|position| tree.node(position).map(|node| (position, node.span())))
        .find(|&(_, span)| span.start() < target.end && target.end <= span.end())?;
    let top = match reach {
        Reach::Form => held,
        Reach::Declaration => ByteSpan::new(keyword(pbg, tree, form)?, held.end()).ok()?,
        Reach::Widest => keyword(pbg, tree, form)
            .map_or(Some(held), |start| ByteSpan::new(start, held.end()).ok())?,
    };
    let lead = usize::from(top.start());
    let shifted = |offset: ByteOffset| usize::from(offset).checked_sub(lead).map(ByteOffset::from);
    let (repair_start, repair_end) = (
        shifted(target.repair.span.start())?,
        shifted(target.repair.span.end())?,
    );
    let source = tree.source();
    let text = <&str>::from(source);
    // Each tile with its mold. The empty application tile the melder pushes
    // between an operand and its juxtaposed argument is one of them.
    let application = pbg.application();
    let mut tiles: Vec<(ByteSpan, MoldId)> = tree
        .positions()
        .filter_map(|position| tree.node(position))
        .filter_map(|node| match node.label() {
            NodeLabel::Tile(mold) => Some((node.span(), mold)),
            NodeLabel::Wald
            | NodeLabel::Meld(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => None,
        })
        .filter(|&(span, _)| target.end < span.end() && span.end() <= top.end())
        .collect();
    tiles.sort_unstable_by_key(|&(span, _)| (span.start(), span.end()));
    // Whether an operand follows the form's last written tile: the first tile
    // after it, past an application tile, faces no hole on its left and opens
    // no declaration, as `Integer` in `def once(n : Integer -> …` does.
    let operand_follows = tiles
        .iter()
        .find(|&&(_, mold)| Some(mold) != application)
        .is_some_and(|&(_, mold)| {
            let faces_hole = pbg.mold(mold).is_ok_and(|def| {
                pbg.step(def.rctx, Dir::Left).is_ok_and(|steps| {
                    steps
                        .iter()
                        .any(|step| matches!(step.crossed, StepSym::Sort(_)))
                })
            });
            !faces_hole && !bool::from(declaration_head(pbg, mold))
        });
    let word_next = |offset: ByteOffset| {
        text.as_bytes()
            .get(usize::from(offset))
            .is_some_and(|&next| next.is_ascii_alphanumeric() || next == b'_')
    };
    let mut places = Vec::new();
    // Where the places that part an operand from its argument start: the next
    // other place is tried before them.
    let mut parting: Option<usize> = None;
    if target.leading == LeadingSlot::Empty && target.class.is_some() {
        places.push(target.end);
    }
    let (mut depth, mut doubled) = (0_usize, false);
    let mut previous: Option<ClosingClass> = None;
    let mut tiles = tiles.into_iter().peekable();
    while let Some((span, mold)) = tiles.next() {
        if Some(mold) == application {
            continue;
        }
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
        // A place that parts an operand from the argument the melder applies
        // it to is tried after the next place: `S (P x <=> x;` takes its `)`
        // after `P x`, and `f(e, x { … }` still takes its `)` after `x`.
        let juxtaposed = tiles
            .peek()
            .is_some_and(|&(_, next)| Some(next) == application);
        let at_doubled = doubled && opening == target.class;
        let split = target.class.is_none() && word_next(span.end());
        if !glued && !split && (depth == 0 || at_doubled) {
            if juxtaposed {
                let _first = parting.get_or_insert(places.len());
                places.push(span.end());
            }
            else if let Some(first) = parting.take() {
                places.insert(first, span.end());
            }
            else {
                places.push(span.end());
            }
        }
        previous = opening;
    }
    places.truncate(PLACES);
    // The melder's close goes first, unless it stands at the end of the form's
    // last written tile and a written operand follows, which a closer there
    // expels.
    if target.class.is_some()
        && (target.leading == LeadingSlot::Empty || target.end < target.close || !operand_follows)
    {
        places.insert(0, target.close);
    }
    let adjacent = if word_next(target.end) {
        &[][..]
    }
    else {
        target.adjacent.as_slice()
    };
    let mut shared = Shared::new(
        pbg,
        SourceText::from(text.get(usize::from(top.start()) .. usize::from(top.end()))?),
    );
    let tried = adjacent
        .iter()
        .map(|&closer| (target.end, closer))
        .chain(
            places
                .iter()
                .flat_map(|&place| target.closers.iter().map(move |&closer| (place, closer))),
        )
        .take(target.class.map_or(COPIES, |_| PLACES.saturating_add(1)));
    // Whether a copy molded with no repair, whatever the checks after it say.
    let clean = Cell::new(false);
    let mut accepts = |&(place, closer): &(ByteOffset, SourceText<'static>),
                       tail: SourceText<'static>| {
        let spelled = cut_in(source, place, closer);
        let pad = spelled.find(<&str>::from(closer)).unwrap_or(0_usize);
        let tile = shifted(place).and_then(|at| {
            let at = usize::from(at).checked_add(pad)?;
            Some((
                ByteOffset::from(at),
                ByteOffset::from(at.checked_add(<&str>::from(closer).len())?),
            ))
        });
        written(source, top, place, SourceText::from(spelled.as_str()), tail).is_some_and(|copy| {
            let copy = SourceText::from(copy.as_str());
            shared.copy(copy).is_some_and(|copied| {
                clean.set(true);
                tile.is_some_and(|(at, end)| bool::from(tiled(&copied, at, end)))
                    && (target.class.is_some()
                        || (bool::from(declared(pbg, &copied))
                            && enclosing(&copied, repair_start, repair_end) <= target.depth
                            && tile.is_some_and(|(at, _end)| {
                                kept(tree, top.start(), place)
                                    == kept(&copied, ByteOffset::from(0_usize), at)
                            })))
            })
        })
    };
    // A bracket's closer is owed at every place that parses. It is minted at
    // the last of them in the source, and it reaches back to the first.
    let (place, closer, first) = if target.class.is_some() {
        let mut first: Option<ByteOffset> = None;
        let mut last: Option<(ByteOffset, SourceText<'static>)> = None;
        for candidate in tried {
            if accepts(&candidate, SourceText::from("")) {
                first = Some(first.map_or(candidate.0, |at| at.min(candidate.0)));
                if last.is_none_or(|(at, _)| at < candidate.0) {
                    last = Some(candidate);
                }
            }
        }
        let (place, closer) = last?;
        (place, closer, first)
    }
    else {
        let plain = tried
            .clone()
            .find(|candidate| accepts(candidate, SourceText::from("")));
        let (place, closer) = match plain {
            Some(found) => found,
            // A copy that molds whole as written has its end: the separator is
            // not what the form lacks.
            None if clean.get() => return None,
            // Written back, the separator the form lost must make one place
            // alone parse, as the source holds the tile at one place.
            None => {
                let separator = lost_separator(pbg, tree, form)?;
                let mut parsing = tried.filter(|candidate| accepts(candidate, separator));
                let found = parsing.next()?;
                if parsing.any(|other| other != found) {
                    return None;
                }
                found
            },
        };
        (place, closer, None)
    };
    let place = past(source, place, closer);
    let spelled = cut_in(source, place, closer);
    let spelled = SourceText::from(spelled.as_str());
    let whole = ByteSpan::new(ByteOffset::from(0_usize), ByteOffset::from(text.len())).ok()?;
    let copy = written(source, whole, place, spelled, SourceText::from(""))?;
    let leaf = target.class.map_or(
        NodeLabel::Grout {
            sort: target.sort,
            shape: GroutShape::Postfix,
        },
        |class| NodeLabel::GhostClose {
            sort: target.sort,
            class,
            reach: CloseReach::from(first.map_or(0_u32, |first| {
                u32::try_from(usize::from(place).saturating_sub(usize::from(first)))
                    .unwrap_or(u32::MAX)
            })),
        },
    );
    let splice = Splice::new(place, spelled, leaf)?;
    spliced(
        molded(pbg, SourceText::from(copy.as_str())),
        source,
        &[splice],
        [target.repair],
    )
}

/// The separator of no bytes that ends `form`, a top-level form of `tree`, as
/// its label spells it: the separator the layout gives from the line of a
/// later top-level form. A copy of `form` alone has no such line, so it lacks
/// the separator, and the end that the form takes from it.
///
/// # Specification
/// - requires: `form` is a child of `tree`'s root.
/// - ensures: the label of a [`NodeLabel::Tile`] child of `form` with no bytes
///   at `form`'s end, when that label closes no bracket and a child of the root
///   that starts at or after that end is a form with bytes; `None` otherwise.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — a definition's `=` left out, whose form the layout's
///   separator before the next declaration ends, is minted after its result
///   type. A block's `}` of no bytes at the form's end, or a separator with no
///   later form, written after the copies, moves recovery rows.
/// - witness: `parse::place::tests::a_tile_a_form_the_layout_ends_lacks_is_minted_where_one_copy_parses_5938`
/// - witness: `tests::sweeps::dropped_tokens_recover_no_worse_than_the_record`
fn lost_separator(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    form: NodeIndex,
) -> Option<SourceText<'static>>
{
    let end = tree.node(form)?.span().end();
    let later = tree
        .children(tree.root())
        .filter_map(|position| tree.node(position))
        .any(|node| {
            end <= node.span().start()
                && node.span().start() < node.span().end()
                && matches!(node.label(), NodeLabel::Meld(_) | NodeLabel::Tile(_))
        });
    if !later {
        return None;
    }
    tree.children(form)
        .filter_map(|child| tree.node(child))
        .find_map(|node| match node.label() {
            NodeLabel::Tile(mold) if node.span().start() == end && node.span().end() == end => pbg
                .mold(mold)
                .ok()
                .map(|def| def.label)
                .filter(|&label| ClosingClass::closing(DelimSpelling::from(label)).is_none())
                .map(SourceText::from),
            NodeLabel::Tile(_)
            | NodeLabel::Wald
            | NodeLabel::Meld(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => None,
        })
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

/// The bytes of `source` within `within`, with `tile` written at `place` and
/// `tail` written after them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `source`'s bytes from `within`'s start to `place`, `tile`, its
///   bytes from `place` to `within`'s end, then `tail`; `None` when `place`
///   lies outside `within` or off a character boundary.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the concatenation.
///
/// # Adequacy
/// - hypothesis: L3 — as [`placed`].
/// - witness: `parse::place::tests::a_closer_left_out_is_minted_where_the_rest_parses_2242`
/// - witness: `parse::place::tests::a_tile_a_form_the_layout_ends_lacks_is_minted_where_one_copy_parses_5938`
fn written(
    source: SourceText<'_>,
    within: ByteSpan,
    place: ByteOffset,
    tile: SourceText<'_>,
    tail: SourceText<'_>,
) -> Option<String>
{
    let text = <&str>::from(source);
    let tile = <&str>::from(tile);
    let tail = <&str>::from(tail);
    let before = text.get(usize::from(within.start()) .. usize::from(place))?;
    let after = text.get(usize::from(place) .. usize::from(within.end()))?;
    let mut copy = String::with_capacity(
        before
            .len()
            .saturating_add(tile.len())
            .saturating_add(after.len())
            .saturating_add(tail.len()),
    );
    copy.push_str(before);
    copy.push_str(tile);
    copy.push_str(after);
    copy.push_str(tail);
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
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;

    use crate::label::label;
    use crate::oblig::Oblig;
    use crate::parse;
    use crate::testing::reconstruct;

    /// #2242, #5199, #3812: a closer the source left out is minted where the
    /// rest of its form parses, not after everything the form could still
    /// take. Where more than one place parses, it is minted at the last of
    /// them and reaches back to the first.
    #[test]
    fn a_closer_left_out_is_minted_where_the_rest_parses_2242()
    {
        let pbg = built_in().unwrap();
        let after = |source: &str, written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        let once = include_str!(
            "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-once.gandr"
        );
        let glued = include_str!(
            "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-glued.gandr"
        );
        let head = include_str!(
            "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-head.gandr"
        );
        let open = include_str!(
            "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-open.gandr"
        );
        for (source, at, first, class, why) in [
            (
                once,
                after(once, "-> -F Integer"),
                Some(after(once, "n : Integer")),
                ClosingClass::Paren,
                "the parameter list's `)` parses after the parameter's type and after the \
                 function type the return type makes of it: it is minted at the last and \
                 reaches back to the first",
            ),
            (
                glued,
                after(glued, "S (P x"),
                None,
                ClosingClass::Paren,
                "a rule's `)` left out is minted after its juxtaposed application, not between \
                 the nested operation's name and its argument, and its misreading's other \
                 repairs are gone",
            ),
            (
                head,
                after(head, "-> -F Integer"),
                Some(after(head, "List(Integer)")),
                ClosingClass::Paren,
                "a `)` left out after a nested `)` parses after the written one and after the \
                 function type the return type makes: it is minted at the last and reaches back \
                 to the first",
            ),
            (
                open,
                after(open, "return n"),
                None,
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
                    NodeLabel::GhostClose { class, reach, .. } => {
                        Some((class, node.span(), u32::from(reach)))
                    },
                    NodeLabel::Wald
                    | NodeLabel::Meld(_)
                    | NodeLabel::Tile(_)
                    | NodeLabel::Grout { .. }
                    | NodeLabel::Space
                    | NodeLabel::Doc => None,
                })
                .collect();
            assert_eq!(minted.len(), 1, "{why}: {minted:?}");
            let (minted_class, span, reach) = minted.first().copied().unwrap();
            assert_eq!(
                (minted_class, span.start(), span.end()),
                (class, ByteOffset::from(at), ByteOffset::from(at)),
                "{why}"
            );
            if let Some(first) = first {
                assert_eq!(
                    usize::try_from(reach).ok(),
                    at.checked_sub(first),
                    "{why}: the close reaches back to the first place"
                );
            }
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

    /// #5837: a closer left out of a declaration that the melder breaks into
    /// pieces is minted where the declaration parses from its keyword. Where
    /// the first bracket left open takes it at no place, a later one does.
    #[test]
    fn a_closer_left_out_of_a_broken_declaration_is_minted_where_it_parses_5837()
    {
        let pbg = built_in().unwrap();
        let after = |source: &str, written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        let typed = include_str!(
            "place/unformatted/a-closer-left-out-of-a-broken-declaration-is-minted-where-it-parses-5837-typed.gandr"
        );
        let inner = include_str!(
            "place/unformatted/a-closer-left-out-of-a-broken-declaration-is-minted-where-it-parses-5837-inner.gandr"
        );
        for (source, at, why) in [
            (
                typed,
                after(typed, "Void Integer"),
                "a `def`'s type that reads its `=` as an equality takes its `)` before the `=`, \
                 though the melder leaves `def quiet :` apart from the type",
            ),
            (
                inner,
                after(inner, "-> Run (?(Seat.Dispatch"),
                "the inner `(` of a result type takes the `)`, though the outer `(` is the first \
                 bracket left open",
            ),
        ] {
            let parsed = parse(&pbg, SourceText::from(source)).unwrap();
            let tree = parsed.tree();
            let minted: Vec<_> = tree
                .positions()
                .filter_map(|position| tree.node(position))
                .filter(|node| matches!(node.label(), NodeLabel::GhostClose { .. }))
                .map(|node| (node.span().start(), node.span().end()))
                .collect();
            assert_eq!(
                minted,
                [(ByteOffset::from(at), ByteOffset::from(at))],
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
        let member = include_str!(
            "place/unformatted/a-tile-left-out-is-minted-where-the-rest-parses-2259-member.gandr"
        );
        let arm = include_str!(
            "place/unformatted/a-tile-left-out-is-minted-where-the-rest-parses-2259-arm.gandr"
        );
        let branch = include_str!(
            "place/unformatted/a-tile-left-out-is-minted-where-the-rest-parses-2259-branch.gandr"
        );
        let last = include_str!(
            "place/unformatted/a-tile-left-out-is-minted-where-the-rest-parses-2259-last.gandr"
        );
        let binder = include_str!(
            "place/unformatted/a-tile-left-out-is-minted-where-the-rest-parses-2259-binder.gandr"
        );
        for (source, at, why) in [
            (
                member,
                after(member, "| loop"),
                "a cell's `:` left out is minted after its name, and the cell reads as written",
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
             `(def twice = loop;) ∷ loop` would read"
        );
    }

    /// #5938: a tile other than a bracket that a form lacks, where the layout's
    /// separator before the next declaration ends that form, is minted where
    /// one copy alone parses with that separator written after it, and at no
    /// place where two copies parse so.
    #[test]
    fn a_tile_a_form_the_layout_ends_lacks_is_minted_where_one_copy_parses_5938()
    {
        let pbg = built_in().unwrap();
        let after = |source: &str, written: &str| {
            source
                .find(written)
                .map_or(0_usize, |start| start.saturating_add(written.len()))
        };
        let separated = include_str!(
            "place/unformatted/a-tile-a-form-the-layout-ends-lacks-is-minted-where-one-copy-parses-5938-separated.gandr"
        );
        let ambiguous = include_str!(
            "place/unformatted/a-tile-a-form-the-layout-ends-lacks-is-minted-where-one-copy-parses-5938-ambiguous.gandr"
        );
        let parsed = parse(&pbg, SourceText::from(separated)).unwrap();
        let tree = parsed.tree();
        assert_eq!(
            minted(tree),
            [ByteOffset::from(after(separated, "-> Spool"))],
            "a definition's `=` left out, whose form the layout's separator before the next \
             declaration ends, is minted after its result type, not left after its `->`: {:?}",
            parsed.obligations()
        );
        assert_eq!(
            reconstruct(tree),
            separated,
            "the tree reconstructs the source"
        );
        assert!(
            matches!(parsed.obligations(), [repair] if repair.class == Oblig::MissingTile),
            "one repair stands: {:?}",
            parsed.obligations()
        );
        let parsed = parse(&pbg, SourceText::from(ambiguous)).unwrap();
        let held = minted(parsed.tree());
        assert!(
            [after(ambiguous, "-> Pair"), after(ambiguous, "-> Pair Nat")]
                .iter()
                .all(|&at| !held.contains(&ByteOffset::from(at))),
            "a definition's `=` left out, where its copy parses at two places with the separator \
             its form lost, is minted at neither: the source does not say which it holds: \
             {held:?}"
        );
    }

    /// #2440, #5199: a definition whose `def` is misspelled, or left out at
    /// the start of the source, reads as one declaration owing its keyword
    /// alone, the keyword minted at its head; a call at the top level with a
    /// repair of its own that no keyword makes a declaration keeps its reading.
    #[test]
    fn a_declaration_keyword_left_out_is_minted_at_its_head_2440()
    {
        let pbg = built_in().unwrap();
        let body = include_str!(
            "place/unformatted/a-declaration-keyword-left-out-is-minted-at-its-head-2440-body.gandr"
        );
        let misspelled = include_str!(
            "place/unformatted/a-declaration-keyword-left-out-is-minted-at-its-head-2440-misspelled.gandr"
        );
        for (source, why) in [
            (
                misspelled,
                "a misspelled `def` is a word of its own, and the definition after it owes \
                 its keyword",
            ),
            (
                body,
                "a definition with its `def` left out owes its keyword",
            ),
        ] {
            let head = source.find("f(").unwrap();
            let parsed = parse(&pbg, SourceText::from(source)).unwrap();
            let tree = parsed.tree();
            assert_eq!(
                reconstruct(tree),
                source,
                "{why}: the tree reconstructs the source"
            );
            assert!(
                matches!(
                    parsed.obligations(),
                    [repair] if repair.class == Oblig::MissingTile
                        && usize::from(repair.span.start()) == head
                        && usize::from(repair.span.end()) == head.saturating_add(1)
                ),
                "{why}: one repair stands, over the name: {:?}",
                parsed.obligations()
            );
            let ghosts: Vec<ByteOffset> = tree
                .positions()
                .filter_map(|position| tree.node(position))
                .filter(|node| {
                    matches!(node.label(), NodeLabel::Grout {
                        shape: GroutShape::Prefix,
                        ..
                    }) && node.span().start() == node.span().end()
                })
                .map(|node| node.span().start())
                .collect();
            assert_eq!(
                ghosts,
                [ByteOffset::from(head)],
                "{why}: the keyword is minted, empty, at the name"
            );
        }
        let call = "f(x\n";
        let parsed = parse(&pbg, SourceText::from(call)).unwrap();
        assert!(
            !parsed
                .tree()
                .positions()
                .any(
                    |position| parsed.tree().node(position).is_some_and(|node| matches!(
                        node.label(),
                        NodeLabel::Grout {
                            shape: GroutShape::Prefix,
                            ..
                        }
                    ))
                ),
            "a call left open at the top level, which no keyword makes a declaration, keeps its \
             reading: {:?}",
            parsed.obligations()
        );
    }

    /// #5199: a misspelled keyword before a definition is a stray word, and
    /// the definition after it owes its `def` at its name. The keyword search
    /// tries the later form first, so the keyword is never minted at the
    /// misspelled word.
    #[test]
    fn a_misspelled_keyword_owes_its_def_at_the_name_after_it_5199()
    {
        let pbg = built_in().unwrap();
        let source = "de pair = 1 ;\n";
        let head = source.find("pair").unwrap();
        let parsed = parse(&pbg, SourceText::from(source)).unwrap();
        let tree = parsed.tree();
        assert_eq!(
            reconstruct(tree),
            source,
            "the tree reconstructs the source"
        );
        assert!(
            matches!(
                parsed.obligations(),
                [repair] if repair.class == Oblig::MissingTile
                    && usize::from(repair.span.start()) == head
            ),
            "one repair stands, at the name: {:?}",
            parsed.obligations()
        );
        let ghosts: Vec<ByteOffset> = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| {
                matches!(node.label(), NodeLabel::Grout {
                    shape: GroutShape::Prefix,
                    ..
                }) && node.span().start() == node.span().end()
            })
            .map(|node| node.span().start())
            .collect();
        assert_eq!(
            ghosts,
            [ByteOffset::from(head)],
            "the keyword is minted, empty, at the name, never at the misspelled word"
        );
    }

    /// A try that stops molding at its first repair answers as the whole
    /// molding and commit do, the same tree when it needs none, over every
    /// prefix of sources whole, missing a closer and carrying one too many:
    /// each prefix leaves its forms open at another point, so repairs stream
    /// early, late and only at the close.
    #[test]
    fn a_try_stopped_at_its_first_repair_answers_as_a_whole_parse()
    {
        let pbg = built_in().unwrap();
        let mut repaired = 0_usize;
        let mut clean = 0_usize;
        for source in [
            include_str!(
                "place/unformatted/a-try-stopped-at-its-first-repair-answers-as-a-whole-parse-1.gandr"
            ),
            include_str!(
                "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-once.gandr"
            ),
            include_str!(
                "place/unformatted/a-try-stopped-at-its-first-repair-answers-as-a-whole-parse-2.gandr"
            ),
            include_str!(
                "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-head.gandr"
            ),
            include_str!(
                "place/unformatted/a-try-stopped-at-its-first-repair-answers-as-a-whole-parse-3.gandr"
            ),
            "def pair = f (x (#[y, z])) w ;\n",
        ] {
            for end in (0 ..= source.len()).filter(|&end| source.is_char_boundary(end)) {
                let prefix = SourceText::from(source.get(.. end).unwrap());
                let whole = super::molded(&pbg, prefix)
                    .commit_with_obligations(prefix)
                    .ok()
                    .and_then(|(tree, obligations)| obligations.is_empty().then_some(tree));
                assert_eq!(
                    super::unrepaired(&pbg, prefix),
                    whole,
                    "{:?}: the stopped molding and the whole one disagree",
                    <&str>::from(prefix)
                );
                if whole.is_some() {
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

    /// A copy read from its form's shared molding answers as a fresh molding
    /// of it does, the same tree when it needs no repair: a closer, a member's
    /// `;`, an arm's `=>` and an `else` written at every token end of sources
    /// whole and missing a tile, each copy with a separator written after it
    /// and with none, tried in source order and then backwards, so the shared
    /// molding resumes, starts again, and starts over after a copy it
    /// committed.
    #[test]
    fn a_resumed_copy_answers_as_a_fresh_one()
    {
        let pbg = built_in().unwrap();
        let mut answers = [0_usize; 2];
        for source in [
            include_str!(
                "place/unformatted/a-try-stopped-at-its-first-repair-answers-as-a-whole-parse-1.gandr"
            ),
            include_str!(
                "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-once.gandr"
            ),
            include_str!(
                "place/unformatted/a-closer-left-out-is-minted-where-the-rest-parses-2242-head.gandr"
            ),
            include_str!(
                "place/unformatted/a-declaration-keyword-left-out-is-minted-at-its-head-2440-misspelled.gandr"
            ),
            include_str!(
                "place/unformatted/a-try-stopped-at-its-first-repair-answers-as-a-whole-parse-3.gandr"
            ),
            include_str!("place/unformatted/a-resumed-copy-answers-as-a-fresh-one-1.gandr"),
            include_str!("place/unformatted/a-resumed-copy-answers-as-a-fresh-one-2.gandr"),
            include_str!(
                "place/unformatted/a-tile-left-out-is-minted-where-the-rest-parses-2259-branch.gandr"
            ),
            include_str!(
                "place/unformatted/a-tile-a-form-the-layout-ends-lacks-is-minted-where-one-copy-parses-5938-separated.gandr"
            ),
        ] {
            let text = SourceText::from(source);
            let mut shared = super::Shared::new(&pbg, text);
            let ends: Vec<usize> = label(SourceFragment::from(source))
                .iter()
                .filter_map(|token| usize::try_from(token.end).ok())
                .collect();
            for &end in ends.iter().chain(ends.iter().rev()) {
                for (tile, tail) in [")", ";", "=>", "else"]
                    .into_iter()
                    .flat_map(|tile| ["", ";"].map(|tail| (tile, tail)))
                {
                    let copy = [
                        source.get(.. end).unwrap(),
                        tile,
                        source.get(end ..).unwrap(),
                        tail,
                    ]
                    .concat();
                    let copy = SourceText::from(copy.as_str());
                    let fresh = super::unrepaired(&pbg, copy);
                    let resumed = shared.copy(copy);
                    assert_eq!(
                        resumed,
                        fresh,
                        "{:?}: the resumed molding and the fresh one disagree",
                        <&str>::from(copy)
                    );
                    if let Some(count) = answers.get_mut(usize::from(fresh.is_some())) {
                        *count = count.saturating_add(1);
                    }
                }
            }
        }
        assert!(
            answers.iter().all(|&count| count > 0),
            "both answers are exercised: {answers:?}"
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
