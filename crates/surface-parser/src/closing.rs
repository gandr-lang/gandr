//! The shortest material that closes an open form, the menu of the cheapest
//! ways to close it, and how each tile of either is written.
//!
//! An open form frontier is a tile occurrence of its rule's form. The
//! grammar's same-form adjacency names every tile that can follow it, holes
//! skipped; [`push_closing`] walks that adjacency to the nearest tile that
//! can end the form, charging one for each tile and one for each hole the
//! grammar requires before a tile, and [`closings`] keeps walking to the
//! next cheapest ends. [`tile_spelling`] says how a label in that material
//! is written: most labels are their tile's text, a few name a lexical class
//! that any token of the class fills.
//!
//! # The completion query is a bound
//!
//! `finalize` (and its interaction-surface name `expected`) reports the
//! material and the obligations closing the input here would introduce, without
//! mutating the state. It reads the slope as it stands rather than replaying
//! the commit, so it is a bound: every obligation a commit inserts is among
//! those it names, and its only excess is a `MissingMeld` for an operator whose
//! operand is a form still open, which the commit's force-close then turns into
//! that operand. The molder uses this cost as one of its ranking keys, so the
//! bound is part of the molding the corpus sources check.
//!
//! The alternative was an exact query: replay the commit on a copy of the
//! slope. It costs a slope clone and a collapse per query, which the molder
//! pays once per surviving candidate per token. Reversal: if a consumer needs
//! the exact obligations at a prefix, it commits a checkpointed copy; if the
//! molder's ranking ever needs exactness, the query replays, and the corpus
//! sources say whether any molding moved.
//!
//! ### An open form expects its cheapest closing
//!
//! For each open form frontier the material is the cheapest way to close the
//! form: the grammar's same-form adjacency names every tile that can follow the
//! frontier, holes skipped, and a uniform-cost walk over it reaches the nearest
//! tile that can end the form, one per tile and one per hole, ties to the lower
//! mold id. A hole is charged before a tile when the predecessor's right
//! context does not admit the tile directly, and after the last tile when it
//! ends the form only once a required tail is filled; the first hole is dropped
//! when anything already stands above the frontier. So `( x` expects `)`, `def
//! x = [1, 2` expects `]` and `;`, and `run y <-` inside a block expects an
//! expression, `;` and `}`. An operator's missing operand adds no hole when a
//! form is open where the operand goes, since closing that form supplies it;
//! its obligation still stands, keeping the bound above.
//! `Completion::innermost` ends after the first frontier's closing, so an
//! editor can show what closes the form the cursor is in.
//!
//! `tile_spelling` writes each tile: a label naming a lexical class
//! (`identifier`, `constructor`, `number`, string content, a shell word, …) is
//! filled by any token of the class, the shell subshell brackets and the
//! command-substitution opener are written as the text the labeler reads them
//! from, and every other label is its own text.
//!
//! - Alternatives: the first `≐`-successor in mold order, which names an
//!   optional tile as often as the closer (`@[` after `def x`, `,` in a
//!   parameter list, `;` after `run y <-` with no expression before it); a walk
//!   that commits a copy and reads its ghost closes, which names closers but
//!   not the keywords and holes between them.
//! - Reversal: the bound keeps one closing because the molder ranks by its
//!   cost; a consumer that needs more reads the menu below, and a ranking that
//!   needs more reads the menu's first entries the same way.
//!
//! ### The menu is every cheap closing
//!
//! An inline completion offers more than one closing: the parameter list's
//! `)`, its return type, another parameter; a block's expression and each
//! statement that may open it. [`closings`] runs the same uniform-cost walk
//! over simple paths — a path never visits a mold twice — and keeps each end
//! it reaches, cheapest first, until it holds the asked number; a path that
//! writes the same text as one kept earlier is dropped, and each mold is
//! grown at most that many times, so the walk is bounded by the limit times
//! the form's adjacency.
//!
//! The walk starts from every reading of the frontier's tile, not only the
//! one the molder kept: the molder reads `case x {` as the empty match, whose
//! `}` follows its `{` directly, and the arm block's `{` of the same text is
//! what offers an arm. The readings are the molds of the frontier's label
//! that a predecessor of the frontier is followed by, and, for a tile that
//! opens a form, the form-first molds of its label and sort that agree with
//! it on whether an operand stands before it.
//!
//! A bracket pair the path leaves empty holds the hole its grammar admits —
//! an opener immediately followed by its family's closer, where the closer's
//! left context faces the sort the opener's right context faces — uncharged,
//! so `def x = (` offers `)` and the parenthesized `<expression> )`, while the
//! unit's `)`, whose left context faces only its opener, stays bare. After an
//! occupied slot the first tile is one whose left context faces a sort: the
//! occupied slot stands before it, so `thunk { 1` offers `}` and `; }` but no
//! statement. [`MeldState::continuations`](crate::MeldState::continuations)
//! pairs the menu with the hole the operator nearest the cursor still owes.
//!
//! - Alternatives: one closing per frontier, the bound's material, which leaves
//!   an editor a single answer; every path up to a cost, which floods a menu
//!   with repetitions of one list separator.
//! - Reversal: a consumer that needs paths through a repetition more than once
//!   lifts the simple-path rule for that consumer's walk.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::MoldDef;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Dir;

use crate::meld::Expected;
use crate::mold::CandidateLabel;

/// The labels that name a lexical class rather than spell a tile, with the
/// name a placeholder for one shows: every label [`candidate_labels`] offers
/// that is not the token's own text.
///
/// [`candidate_labels`]: crate::candidate_labels
const CLASS_LABELS: &[&str] = &[
    "character",
    "constructor",
    "double_string_fragment",
    "environment_assignment",
    "escape_sequence",
    "file_descriptor",
    "hole_name",
    "identifier",
    "number",
    "shell_word",
    "single_quoted_content",
    "string_fragment",
    "type_identifier",
    "type_variable",
    "typed_number",
    "variable_name",
];

/// The labels whose tile the labeler emits under another text, with that
/// text.
const WRITTEN_AS: &[(&str, &str)] = &[
    ("command_substitution_start", "$!{"),
    ("subshell_close", "]"),
    ("subshell_open", "["),
];

/// How a tile label is written in source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TileSpelling<'label>
{
    /// The tile is written as this exact text.
    Literal(&'label str),
    /// The label names a lexical class: any token of the class is the tile.
    Class(&'label str),
}

/// How the tile labeled `label` is written.
///
/// # Specification
/// - requires: nothing; any label is admissible.
/// - ensures: a label naming a lexical class (an identifier, a constructor, a
///   number, string content, a shell word, …) is [`TileSpelling::Class`] of
///   itself; the shell subshell brackets and the command-substitution opener
///   are [`TileSpelling::Literal`] of the text the labeler reads them from;
///   every other label is [`TileSpelling::Literal`] of itself, the text it is
///   the label of.
/// - provides: the spelling a completion shows for an expected tile.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each class label [`candidate_labels`] offers for a sample
///   token of every lexeme is a class, each renamed bracket reads back as its
///   token's text, and keyword and punctuation labels are their own text.
///   Treating a class as literal, or a literal as a class, changes a spelling.
/// - witness: `closing::tests::every_label_a_token_offers_is_spelled_as_it_reads`
///
/// [`candidate_labels`]: crate::candidate_labels
#[spec(ensures: |ret| {
    let label = <&str>::from(label);
    match ret {
        TileSpelling::Class(class) => class == label && CLASS_LABELS.contains(&label),
        TileSpelling::Literal(text) => !CLASS_LABELS.contains(&label)
            && (text == label || WRITTEN_AS.contains(&(label, text))),
    }
})]
#[inline]
#[must_use]
pub fn tile_spelling(label: CandidateLabel<'_>) -> TileSpelling<'_>
{
    let label = <&str>::from(label);
    if CLASS_LABELS.contains(&label) {
        return TileSpelling::Class(label);
    }
    for &(renamed, text) in WRITTEN_AS {
        if renamed == label {
            return TileSpelling::Literal(text);
        }
    }
    TileSpelling::Literal(label)
}

/// Whether anything already stands in the slot right after an open frontier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LeadingSlot
{
    /// Nothing follows the frontier yet.
    Empty,
    /// An operand, an operator or an inner form follows it: whatever hole
    /// comes first is being filled.
    Occupied,
}

/// Whether [`push_closing`] found a way to close the form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClosingReach
{
    /// The material closing the form was pushed.
    Closed,
    /// No end is reachable from the frontier: its mold is not the grammar's.
    Unreachable,
}

/// What a step to a tile crosses before it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Crossed
{
    /// The tile follows directly.
    Nothing,
    /// A hole of this sort comes first.
    Hole(Sort),
}

/// The cost of closing material: one per tile, one per hole.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Cost(usize);

impl Cost
{
    /// The cost of no material.
    const ZERO: Self = Self(0);

    /// The cost after one more tile, with `crossed` before it.
    ///
    /// # Specification
    /// trivial.
    const fn then(
        self,
        crossed: Crossed,
    ) -> Self
    {
        Self(self.0.saturating_add(match crossed {
            Crossed::Nothing => 1,
            Crossed::Hole(_) => 2,
        }))
    }

    /// The cost after one more hole.
    ///
    /// # Specification
    /// trivial.
    const fn hole(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// How the walk reached a tile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Via
{
    /// The tile is the frontier the walk started from.
    Start,
    /// The tile follows `previous` across `crossed`.
    Step
    {
        /// The tile before it.
        previous: MoldId,
        /// What comes between the two.
        crossed: Crossed,
    },
}

/// The cheapest way the walk has found to a tile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Reached
{
    /// Its cost: one per tile, one per hole.
    cost: Cost,
    /// How it was reached.
    via: Via,
}

/// The cheapest end the walk has found: the tile ending the form, the
/// trailing hole it owes, and the whole cost.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct End
{
    /// The last tile.
    mold: MoldId,
    /// The hole a required tail owes after it.
    tail: Crossed,
    /// The cost of the material up to and including that hole.
    cost: Cost,
}

/// How a tile can end its form, if it can.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Ending
{
    /// The form can end at the tile.
    Here,
    /// The form can end once a hole of this sort follows the tile.
    AfterHole(Sort),
    /// The form cannot end at the tile.
    Not,
}

/// Push onto `material` the cheapest material that closes the form whose
/// open frontier is `frontier`, with `leading` saying whether the slot after
/// the frontier is already being filled.
///
/// # Specification
/// - requires: nothing; an unknown mold is admitted.
/// - ensures: on [`ClosingReach::Closed`], `material` gains, in source order,
///   the tiles from the frontier to a tile that can end its form, each preceded
///   by the hole its predecessor's right context requires when that context
///   does not admit the tile directly, and a trailing hole when the last tile
///   ends the form only after one. The first hole is omitted when `leading` is
///   [`LeadingSlot::Occupied`]. The material is the cheapest so charged, one
///   per tile and one per hole, ties broken toward the lower mold id. A
///   frontier already ending its form, or a required tail whose hole is
///   occupied, pushes nothing. On [`ClosingReach::Unreachable`], `material` is
///   unchanged.
/// - provides: the closing material [`MeldState::finalize`] reports for each
///   open frontier.
/// - fails: [`ClosingReach::Unreachable`] when no end is reachable, which
///   happens only for a mold the grammar does not hold.
/// - panics: none.
/// - intension: a uniform-cost walk over the frontier's same-form adjacency,
///   visiting each mold of the form at most once at its cheapest cost.
///
/// # Adequacy
/// - hypothesis: L3 — brackets, a parameter list, a binding statement, a
///   required-tail quantifier, a string and a list each close at their exact
///   material, with and without the leading slot occupied. Taking the first
///   successor rather than the cheapest, dropping a required hole, keeping a
///   filled one or stopping short of an end changes the material.
/// - witness: `closing::tests::each_form_closes_at_its_cheapest_material`
/// - witness: `closing::tests::an_unknown_mold_is_unreachable`
///
/// [`MeldState::finalize`]: crate::MeldState::finalize
#[spec(captures: before = material.len(),
    ensures: |ret| match ret {
        ClosingReach::Closed => material.len() >= before,
        ClosingReach::Unreachable => material.len() == before,
    })]
pub fn push_closing(
    pbg: &Pbg,
    frontier: MoldId,
    leading: LeadingSlot,
    material: &mut Vec<Expected>,
) -> ClosingReach
{
    if pbg.mold(frontier).is_err() {
        return ClosingReach::Unreachable;
    }
    let mut reached: BTreeMap<MoldId, Reached> = BTreeMap::new();
    let mut queue: BTreeSet<(Cost, MoldId)> = BTreeSet::new();
    let _fresh = reached.insert(frontier, Reached {
        cost: Cost::ZERO,
        via: Via::Start,
    });
    let _queued = queue.insert((Cost::ZERO, frontier));
    let mut best: Vec<End> = Vec::with_capacity(1);
    while let Some((cost, mold)) = queue.pop_first() {
        if best.first().is_some_and(|end| end.cost <= cost) {
            break;
        }
        if reached.get(&mold).is_some_and(|known| known.cost < cost) {
            continue;
        }
        let start = mold == frontier;
        let end = match ending(pbg, mold) {
            Ending::Here if start => Some(End {
                mold,
                tail: Crossed::Nothing,
                cost,
            }),
            Ending::Here => {
                offer(&mut best, End {
                    mold,
                    tail: Crossed::Nothing,
                    cost,
                });
                continue;
            },
            Ending::AfterHole(_) if start && leading == LeadingSlot::Occupied => Some(End {
                mold,
                tail: Crossed::Nothing,
                cost,
            }),
            Ending::AfterHole(sort) => Some(End {
                mold,
                tail: Crossed::Hole(sort),
                cost: cost.hole(),
            }),
            Ending::Not => None,
        };
        if let Some(end) = end {
            offer(&mut best, end);
        }
        for &(_, next) in pbg.mold_successors(mold) {
            let crossed = if start && leading == LeadingSlot::Occupied {
                Crossed::Nothing
            }
            else {
                between(pbg, mold, next)
            };
            let cost = cost.then(crossed);
            if reached.get(&next).is_some_and(|known| known.cost <= cost) {
                continue;
            }
            let _prior = reached.insert(next, Reached {
                cost,
                via: Via::Step {
                    previous: mold,
                    crossed,
                },
            });
            let _queued = queue.insert((cost, next));
        }
    }
    let Some(&end) = best.first()
    else {
        return ClosingReach::Unreachable;
    };
    let mut reversed: Vec<Expected> = Vec::new();
    if let Crossed::Hole(sort) = end.tail {
        reversed.push(Expected::Hole(sort));
    }
    let mut at = end.mold;
    while let Some(&Reached {
        via: Via::Step { previous, crossed },
        ..
    }) = reached.get(&at)
    {
        if let Ok(def) = pbg.mold(at) {
            reversed.push(Expected::Tile(def.label));
        }
        if let Crossed::Hole(sort) = crossed {
            reversed.push(Expected::Hole(sort));
        }
        at = previous;
    }
    material.extend(reversed.into_iter().rev());
    ClosingReach::Closed
}

/// Keep `end` in `best` when it is cheaper than the end held there.
///
/// # Specification
/// - ensures: `best` holds one end, the cheaper of `end` and the one it held,
///   the held one on a tie.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the closing witness's cases tie between ends of equal
///   cost only where the lower mold id is the material asserted; keeping the
///   later end, or a dearer one, changes it.
/// - witness: `closing::tests::each_form_closes_at_its_cheapest_material`
#[spec(ensures: |_| best.len() == 1)]
fn offer(
    best: &mut Vec<End>,
    end: End,
)
{
    match best.first_mut() {
        Some(held) if held.cost <= end.cost => {},
        Some(held) => *held = end,
        None => best.push(end),
    }
}

/// How `mold` can end its form.
///
/// # Specification
/// - ensures: [`Ending::Here`] for a mold the grammar lets end its form with
///   nothing after it; [`Ending::AfterHole`] of the first sort its right
///   context faces for a mold that ends it once a hole follows; [`Ending::Not`]
///   otherwise, an unknown mold included.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a bracket's closer ends at once, a quantifier's dot ends
///   once its body follows, and a parameter's colon ends nothing; the closing
///   witness asserts each at its exact material. Treating a required tail as an
///   end, or an end as a required tail, changes that material.
/// - witness: `closing::tests::each_form_closes_at_its_cheapest_material`
#[spec(ensures: |ret| !matches!(ret, Ending::Here) || bool::from(pbg.mold_is_form_last(mold)))]
fn ending(
    pbg: &Pbg,
    mold: MoldId,
) -> Ending
{
    if bool::from(pbg.mold_is_form_last(mold)) {
        return Ending::Here;
    }
    if bool::from(pbg.mold_has_required_tail(mold)) {
        return match right_sort(pbg, mold) {
            Crossed::Hole(sort) => Ending::AfterHole(sort),
            Crossed::Nothing => Ending::Not,
        };
    }
    Ending::Not
}

/// What comes between `left` and its same-form successor `right`.
///
/// # Specification
/// - ensures: nothing when `left`'s right context faces `right`'s label
///   directly, `right`'s left context faces `left`'s label directly, or either
///   mold is unknown; otherwise the first sort `left`'s right context faces,
///   the hole the grammar puts between them.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `def x =` needs an expression before its `;` and a
///   parenthesis closes directly; the closing witness asserts both. Charging a
///   hole the context admits a tile across, or dropping one it requires,
///   changes that material.
/// - witness: `closing::tests::each_form_closes_at_its_cheapest_material`
#[spec(ensures: |ret| matches!(ret, Crossed::Nothing) || pbg.mold(left).is_ok())]
fn between(
    pbg: &Pbg,
    left: MoldId,
    right: MoldId,
) -> Crossed
{
    let (Ok(def), Ok(next)) = (pbg.mold(left), pbg.mold(right))
    else {
        return Crossed::Nothing;
    };
    let faces = |rctx, dir, label| {
        pbg.step(rctx, dir).is_ok_and(|steps| {
            steps
                .iter()
                .any(|step| step.crossed == StepSym::Tile(label))
        })
    };
    if faces(def.rctx, Dir::Right, next.label) || faces(next.rctx, Dir::Left, def.label) {
        return Crossed::Nothing;
    }
    right_sort(pbg, left)
}

/// The first sort `mold`'s right context faces, as a hole to cross.
///
/// # Specification
/// - ensures: a hole of the first sort among the right context's steps; nothing
///   when it faces no sort or the mold is unknown.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — expression and type holes are asserted at their sorts by
///   the closing witness; reading a sort from the wrong side or a tile step as
///   a sort changes them.
/// - witness: `closing::tests::each_form_closes_at_its_cheapest_material`
#[spec(ensures: |ret| matches!(ret, Crossed::Nothing) || pbg.mold(mold).is_ok())]
fn right_sort(
    pbg: &Pbg,
    mold: MoldId,
) -> Crossed
{
    let Ok(def) = pbg.mold(mold)
    else {
        return Crossed::Nothing;
    };
    let Ok(steps) = pbg.step(def.rctx, Dir::Right)
    else {
        return Crossed::Nothing;
    };
    steps
        .iter()
        .find_map(|step| match step.crossed {
            StepSym::Sort(sort) => Some(Crossed::Hole(sort)),
            StepSym::Tile(_) => None,
        })
        .unwrap_or(Crossed::Nothing)
}

/// One step of a continuation: a tile to write, or a hole to fill.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step
{
    /// The tile of this mold.
    Tile(MoldId),
    /// A hole of `sort`, faced by the right context of the mold `after`.
    Hole
    {
        /// The sort that fills the hole.
        sort: Sort,
        /// The tile or operator whose right context faces the hole.
        after: MoldId,
    },
}

/// How many closings [`closings`] keeps.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClosingLimit(usize);

impl From<usize> for ClosingLimit
{
    /// The limit of `count` closings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<ClosingLimit> for usize
{
    /// The number of closings the limit admits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(limit: ClosingLimit) -> Self
    {
        limit.0
    }
}

/// One way to close an open form: the steps from its frontier to a tile that
/// ends the form, in source order.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Closing(Vec<Step>);

impl Closing
{
    /// The closing's steps, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[Step]
    {
        &self.0
    }
}

/// A position in the walk's trail arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TrailIndex(usize);

/// How the walk reached one trail's tile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Link
{
    /// The tile is the frontier the walk started from.
    Root,
    /// The tile follows the trail at `previous` across `crossed`.
    After
    {
        /// The trail ending at the tile before.
        previous: TrailIndex,
        /// What comes between the two tiles.
        crossed: Crossed,
    },
}

/// One path the walk has grown: its last tile and how the walk reached it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Trail
{
    /// The path's last tile.
    mold: MoldId,
    /// The path before it.
    link: Link,
}

/// What the walk does with a queued trail.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Next
{
    /// Report the trail as a closing, with the hole a required tail owes
    /// after its last tile.
    End(Crossed),
    /// Extend the trail by each successor of its last tile.
    Grow,
}

/// The `limit` cheapest ways to close the form whose open frontier is
/// `frontier`, cheapest first, with `leading` saying whether the slot after
/// the frontier is already being filled.
///
/// The walk starts from every reading of the frontier's tile — the frontier's
/// mold and each mold of the same label the same predecessor admits, or for a
/// form's first tile each form-first mold of the same label and sort — since
/// the molder kept one reading for the text so far and the next tile may yet
/// choose another: `case x {` molds its `{` as the empty match's, and an arm
/// is a closing of the arm block's `{`.
///
/// # Specification
/// - requires: nothing; an unknown mold and a zero limit are admitted.
/// - ensures: at most `limit` closings, each a path through the same-form
///   adjacency from a reading of the frontier's tile that visits no mold twice
///   and ends at a tile that can end the form, charged as [`push_closing`]
///   charges and ordered by that charge, ties toward the lower mold and then
///   the path found first; a path that writes the same text as one kept earlier
///   is dropped. A closing's steps are its tiles in source order, each preceded
///   by the hole its predecessor's right context requires when that context
///   does not admit it directly, and followed by the hole a required tail owes.
///   A bracket pair the path would leave empty — an opener immediately followed
///   by the closer of its family, whose left context faces the sort the
///   opener's right context faces — holds an uncharged hole of that sort, the
///   frontier included when `leading` is [`LeadingSlot::Empty`]. Each hole
///   names the mold before it. No hole follows the frontier when `leading` is
///   [`LeadingSlot::Occupied`], and the first tile after it is one whose left
///   context faces a sort: the occupied slot stands before it. An unknown
///   frontier or a zero limit has no closing.
/// - provides: the menu of closings an inline completion offers.
/// - fails: never.
/// - panics: none.
/// - intension: a uniform-cost walk that extends each mold at most `limit`
///   times and stops at the `limit`-th closing, so its work is bounded by
///   `limit` times the form's adjacency, plus one scan of the adjacency for the
///   frontier's readings.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter list, a definition's value, an empty bracket
///   pair, an empty match, a required tail and an occupied slot each yield
///   their exact closings in order, with the mold each hole names. Keeping only
///   the cheapest, revisiting a mold, walking the frontier's own reading alone,
///   dropping the pair's hole, naming the wrong mold before a hole or
///   reordering equal charges changes them.
/// - witness: `closing::tests::closings_offer_each_path_cheapest_first`
/// - witness: `closing::tests::an_unknown_mold_is_unreachable`
#[spec(ensures: |ret| ret.len() <= usize::from(limit))]
#[inline]
#[must_use]
pub fn closings(
    pbg: &Pbg,
    frontier: MoldId,
    leading: LeadingSlot,
    limit: ClosingLimit,
) -> Vec<Closing>
{
    let limit = usize::from(limit);
    let mut found: Vec<Closing> = Vec::new();
    if limit == 0 || pbg.mold(frontier).is_err() {
        return found;
    }
    let mut trails: Vec<Trail> = Vec::new();
    let mut queue: BTreeSet<(Cost, Next, MoldId, TrailIndex)> = BTreeSet::new();
    for reading in readings(pbg, frontier) {
        let _queued = queue.insert((Cost::ZERO, Next::Grow, reading, TrailIndex(trails.len())));
        trails.push(Trail {
            mold: reading,
            link: Link::Root,
        });
    }
    let mut grown: BTreeMap<MoldId, usize> = BTreeMap::new();
    while found.len() < limit
        && let Some((cost, next, mold, at)) = queue.pop_first()
    {
        if let Next::End(tail) = next {
            let closing = trace(pbg, &trails, at, tail, leading);
            if !found
                .iter()
                .any(|held| reads_alike(pbg, held, &closing) == Reading::Alike)
            {
                found.push(closing);
            }
            continue;
        }
        let times = grown.entry(mold).or_default();
        if *times >= limit {
            continue;
        }
        *times = times.saturating_add(1);
        let start = trails
            .get(at.0)
            .is_some_and(|trail| trail.link == Link::Root);
        let end = match ending(pbg, mold) {
            Ending::Here => Some((cost, Crossed::Nothing)),
            Ending::AfterHole(_) if start && leading == LeadingSlot::Occupied => {
                Some((cost, Crossed::Nothing))
            },
            Ending::AfterHole(sort) => Some((cost.hole(), Crossed::Hole(sort))),
            Ending::Not => None,
        };
        if let Some((charged, tail)) = end {
            let _queued = queue.insert((charged, Next::End(tail), mold, at));
        }
        for &(_, successor) in pbg.mold_successors(mold) {
            if on_trail(&trails, at, successor) == Visited::Already {
                continue;
            }
            // An occupied slot stands before the first tile grown from the
            // frontier, so only a tile a hole may stand before follows it.
            let crossed = if start && leading == LeadingSlot::Occupied {
                let after_hole = pbg.mold(successor).is_ok_and(|def| {
                    pbg.step(def.rctx, Dir::Left).is_ok_and(|steps| {
                        steps
                            .iter()
                            .any(|step| matches!(step.crossed, StepSym::Sort(_)))
                    })
                });
                if !after_hole {
                    continue;
                }
                Crossed::Nothing
            }
            else {
                between(pbg, mold, successor)
            };
            let grown_at = TrailIndex(trails.len());
            trails.push(Trail {
                mold: successor,
                link: Link::After {
                    previous: at,
                    crossed,
                },
            });
            let _queued = queue.insert((cost.then(crossed), Next::Grow, successor, grown_at));
        }
    }
    found
}

/// Every mold the frontier's tile could be read as where it stands: the
/// frontier, each mold of its label that a predecessor of the frontier is
/// followed by, and, when the frontier can open a form, each form-first mold
/// of its label and sort that agrees with it on whether an operand stands
/// before it.
///
/// # Specification
/// - ensures: ascending and unique; holds `frontier` itself when the grammar
///   holds it; empty for an unknown mold.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the empty match's `{` reads as the arm block's too, and
///   the closings witness asserts the arm that only the second reading reaches;
///   a parenthesis at an operand slot never reads as a call's, whose argument
///   list the same witness never offers there. Reading the frontier alone loses
///   the arm; ignoring the left operand offers the call's.
/// - witness: `closing::tests::closings_offer_each_path_cheapest_first`
#[spec(ensures: |ret| ret.contains(&frontier) == pbg.mold(frontier).is_ok() && (pbg.mold(frontier).is_ok() || ret.is_empty()))]
fn readings(
    pbg: &Pbg,
    frontier: MoldId,
) -> BTreeSet<MoldId>
{
    let mut found: BTreeSet<MoldId> = BTreeSet::new();
    let Ok(def) = pbg.mold(frontier)
    else {
        return found;
    };
    let _held = found.insert(frontier);
    let alike = |other: MoldId| pbg.mold(other).is_ok_and(|other| other.label == def.label);
    if bool::from(pbg.mold_has_predecessor(frontier)) {
        for &(before, _) in pbg
            .adjacencies()
            .iter()
            .filter(|&&(_, after)| after == frontier)
        {
            for &(_, sibling) in pbg.mold_successors(before) {
                if alike(sibling) {
                    let _held = found.insert(sibling);
                }
            }
        }
    }
    if bool::from(pbg.mold_is_form_first(frontier)) {
        let operand_before = |mold: &MoldDef| {
            pbg.step(mold.rctx, Dir::Left).is_ok_and(|steps| {
                steps
                    .iter()
                    .any(|step| matches!(step.crossed, StepSym::Sort(_)))
            })
        };
        let before = operand_before(def);
        for &other in pbg.form_first() {
            let agrees = pbg.mold(other).is_ok_and(|other| {
                other.label == def.label
                    && other.sort == def.sort
                    && operand_before(other) == before
            });
            if agrees {
                let _held = found.insert(other);
            }
        }
    }
    found
}

/// Whether a path already holds a mold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visited
{
    /// The path holds the mold.
    Already,
    /// The path does not hold it.
    Not,
}

/// Whether `mold` is a tile of the trail ending at `at`, the frontier
/// included.
///
/// # Specification
/// - ensures: [`Visited::Already`] exactly when some trail on the chain from
///   `at` back to the root holds `mold`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter list's repeat would revisit its `,`; the
///   closings witness asserts paths that never do. Ignoring the root, or
///   stopping before it, lets a closing revisit a mold.
/// - witness: `closing::tests::closings_offer_each_path_cheapest_first`
#[spec(ensures: |ret| matches!(ret, Visited::Not) || trails.iter().any(|trail| trail.mold == mold))]
fn on_trail(
    trails: &[Trail],
    at: TrailIndex,
    mold: MoldId,
) -> Visited
{
    let mut index = at;
    while let Some(trail) = trails.get(index.0) {
        if trail.mold == mold {
            return Visited::Already;
        }
        match trail.link {
            Link::Root => return Visited::Not,
            Link::After { previous, .. } => index = previous,
        }
    }
    Visited::Not
}

/// The closing the trail ending at `at` spells, with `tail` after its last
/// tile.
///
/// # Specification
/// - ensures: the trail's tiles after the frontier in source order, each
///   preceded by the hole it crosses, an empty bracket pair holding the hole
///   its opener's right context faces — the frontier counts as an opener only
///   when `leading` is [`LeadingSlot::Empty`] — and `tail` last; each hole
///   names the mold before it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the closings witness asserts a crossed hole, a filled
///   pair and a required tail at their exact steps and molds.
/// - witness: `closing::tests::closings_offer_each_path_cheapest_first`
#[spec(ensures: |ret| ret.0.iter().filter(|step| matches!(step, Step::Tile(_))).count() <= trails.len()
    && (!matches!(tail, Crossed::Hole(_)) || trails.get(at.0).is_none()
        || matches!(ret.0.last(), Some(&Step::Hole { sort, .. }) if tail == Crossed::Hole(sort))))]
fn trace(
    pbg: &Pbg,
    trails: &[Trail],
    at: TrailIndex,
    tail: Crossed,
    leading: LeadingSlot,
) -> Closing
{
    let mut reversed: Vec<Step> = Vec::new();
    if let (Crossed::Hole(sort), Some(last)) = (tail, trails.get(at.0)) {
        reversed.push(Step::Hole {
            sort,
            after: last.mold,
        });
    }
    let mut index = at;
    while let Some(&Trail {
        mold,
        link: Link::After { previous, crossed },
    }) = trails.get(index.0)
    {
        reversed.push(Step::Tile(mold));
        if let Some(before) = trails.get(previous.0) {
            let filled = before.link == Link::Root && leading == LeadingSlot::Occupied;
            let hole = match crossed {
                Crossed::Hole(sort) => Crossed::Hole(sort),
                Crossed::Nothing if filled => Crossed::Nothing,
                Crossed::Nothing => empty_pair(pbg, before.mold, mold),
            };
            if let Crossed::Hole(sort) = hole {
                reversed.push(Step::Hole {
                    sort,
                    after: before.mold,
                });
            }
        }
        index = previous;
    }
    reversed.reverse();
    Closing(reversed)
}

/// The hole an empty bracket pair holds: `opener` then `closer` of the same
/// family, with the sort `opener`'s right context faces between them.
///
/// # Specification
/// - ensures: a hole of the first sort `opener`'s right context faces when
///   `opener`'s label opens the family `closer`'s label closes and `closer`'s
///   left context faces that sort too, so the grammar admits the hole between
///   them; nothing otherwise, an unknown mold included.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a block brace holds an expression; a parenthesis whose
///   unit closer faces only its opener holds nothing, while the parenthesized
///   closer holds the expression; a definition's parameter parenthesis, whose
///   context faces only tiles, holds nothing. The closings witness asserts
///   each. Skipping the closer's side admits an empty pair the grammar refuses
///   to fill.
/// - witness: `closing::tests::closings_offer_each_path_cheapest_first`
#[spec(ensures: |ret| matches!(ret, Crossed::Nothing) || (pbg.mold(opener).is_ok() && pbg.mold(closer).is_ok()))]
fn empty_pair(
    pbg: &Pbg,
    opener: MoldId,
    closer: MoldId,
) -> Crossed
{
    let (Ok(open), Ok(close)) = (pbg.mold(opener), pbg.mold(closer))
    else {
        return Crossed::Nothing;
    };
    let opens = ClosingClass::opening(DelimSpelling::from(open.label));
    let closes = ClosingClass::closing(DelimSpelling::from(close.label));
    if !matches!((opens, closes), (Some(family), Some(closed)) if family == closed) {
        return Crossed::Nothing;
    }
    let Crossed::Hole(sort) = right_sort(pbg, opener)
    else {
        return Crossed::Nothing;
    };
    let admits = pbg
        .step(close.rctx, Dir::Left)
        .is_ok_and(|steps| steps.iter().any(|step| step.crossed == StepSym::Sort(sort)));
    if admits {
        Crossed::Hole(sort)
    }
    else {
        Crossed::Nothing
    }
}

/// Whether two closings write the same text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// Their steps agree label for label and hole for hole.
    Alike,
    /// Some step differs.
    Distinct,
}

/// Whether `held` and `closing` write the same text: the same tile labels and
/// the same holes, each after a tile of the same label, in the same order.
///
/// # Specification
/// - ensures: [`Reading::Alike`] exactly when the two have equally many steps
///   and each pair is two tiles of one label, or two holes of one sort after
///   tiles of one label.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a unit `( )` and a parenthesized `( E )` are distinct
///   molds that read alike once the unit's pair is filled; the closings witness
///   asserts the menu keeps one. Comparing molds rather than labels keeps both.
/// - witness: `closing::tests::closings_offer_each_path_cheapest_first`
#[spec(ensures: |ret| matches!(ret, Reading::Distinct) || held.0.len() == closing.0.len())]
fn reads_alike(
    pbg: &Pbg,
    held: &Closing,
    closing: &Closing,
) -> Reading
{
    let label = |mold: MoldId| pbg.mold(mold).map(|def| def.label).ok();
    let alike = held.0.len() == closing.0.len()
        && held
            .0
            .iter()
            .zip(&closing.0)
            .all(|(&left_step, &right_step)| match (left_step, right_step) {
                (Step::Tile(left), Step::Tile(right)) => label(left) == label(right),
                (
                    Step::Hole {
                        sort: left,
                        after: left_after,
                    },
                    Step::Hole {
                        sort: right,
                        after: right_after,
                    },
                ) => left == right && label(left_after) == label(right_after),
                (Step::Tile(_), Step::Hole { .. }) | (Step::Hole { .. }, Step::Tile(_)) => false,
            });
    if alike {
        Reading::Alike
    }
    else {
        Reading::Distinct
    }
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::boxed::Box;
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::error::Error;

    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::Sort;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;

    use super::Closing;
    use super::ClosingLimit;
    use super::ClosingReach;
    use super::LeadingSlot;
    use super::Step;
    use super::TileSpelling;
    use super::closings;
    use super::push_closing;
    use super::tile_spelling;
    use crate::Expected;
    use crate::Lexeme;
    use crate::MeldState;
    use crate::Molder;
    use crate::TokenText;
    use crate::candidate_labels;
    use crate::label;

    /// The open frontier molding `source` leaves nearest the slope head.
    ///
    /// # Specification
    /// trivial.
    fn frontier(
        pbg: &Pbg,
        source: SourceText<'_>,
    ) -> MoldId
    {
        let mut molder = Molder::new(pbg);
        let mut state = MeldState::new(pbg);
        let tokens = label(SourceFragment::from(<&str>::from(source)));
        molder.mold_stream(&mut state, &tokens, source);
        state
            .open_form_mold()
            .expect("the source leaves a form open")
    }

    /// The material closing `frontier` with `leading`, and whether it closed.
    ///
    /// # Specification
    /// trivial.
    fn closing(
        pbg: &Pbg,
        frontier: MoldId,
        leading: LeadingSlot,
    ) -> (ClosingReach, Vec<Expected>)
    {
        let mut material = vec![Expected::Grout(gandr_surface_syntax::GroutShape::Convex)];
        let reach = push_closing(pbg, frontier, leading, &mut material);
        (reach, material.split_off(1))
    }

    #[test]
    fn each_form_closes_at_its_cheapest_material() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        let hole = Expected::Hole;
        let tile = Expected::Tile;
        for (source, leading, want) in [
            ("( x", LeadingSlot::Occupied, vec![tile(")")]),
            ("(", LeadingSlot::Empty, vec![tile(")")]),
            ("def x =", LeadingSlot::Empty, vec![
                hole(Sort::Expression),
                tile(";"),
            ]),
            ("def f = [1, 2", LeadingSlot::Occupied, vec![tile("]")]),
            (
                "def f(x: Nat) -> -F Nat { run y <-",
                LeadingSlot::Empty,
                vec![hole(Sort::Expression), tile(";"), tile("}")],
            ),
            ("def f = \"abc", LeadingSlot::Occupied, vec![tile("\"")]),
            ("def g : forall a .", LeadingSlot::Empty, vec![hole(
                Sort::Type,
            )]),
            ("def g : forall a .", LeadingSlot::Occupied, vec![]),
        ] {
            let at = frontier(&pbg, SourceText::from(source));
            assert_eq!(
                (ClosingReach::Closed, want),
                closing(&pbg, at, leading),
                "`{source}` with {leading:?}"
            );
        }
        Ok(())
    }

    #[test]
    fn an_unknown_mold_is_unreachable() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        assert_eq!(
            (ClosingReach::Unreachable, vec![]),
            closing(&pbg, MoldId::from(u32::MAX), LeadingSlot::Empty),
            "a mold past the table reaches no end and pushes nothing"
        );
        assert_eq!(
            Vec::<Closing>::new(),
            closings(
                &pbg,
                MoldId::from(u32::MAX),
                LeadingSlot::Empty,
                ClosingLimit::from(4_usize)
            ),
            "a mold past the table has no closing"
        );
        Ok(())
    }

    /// `closing` written out: each tile as its label, each hole as its sort
    /// and the label of the mold before it.
    ///
    /// # Specification
    /// trivial.
    fn written(
        pbg: &Pbg,
        closing: &Closing,
    ) -> String
    {
        let label = |mold: MoldId| pbg.mold(mold).map_or("?", |def| def.label);
        closing
            .steps()
            .iter()
            .map(|&step| match step {
                Step::Tile(mold) => label(mold).to_owned(),
                Step::Hole { sort, after } => alloc::format!("<{sort:?}@{}>", label(after)),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn closings_offer_each_path_cheapest_first() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        for (source, leading, limit, want) in [
            ("def x =", LeadingSlot::Empty, 1_usize, vec![
                "<Expression@=> ;",
            ]),
            // The unit's closer faces only its opener, so its pair stays empty;
            // the parenthesized closer is the one that holds an expression.
            ("def x = (", LeadingSlot::Empty, 3, vec![
                ")",
                "<Expression@(> )",
                "<Expression@(> , )",
            ]),
            // With the slot filled, the unit's `)` and the parenthesized `)`
            // read alike, and the menu keeps one of them.
            ("def x = ( 1", LeadingSlot::Occupied, 3, vec![
                ")",
                ", )",
                ": <Type@:> )",
            ]),
            // A parameter list's parenthesis faces only tiles, so its pair is
            // never filled; the `,` repeat is never walked twice.
            ("def f(x: Integer", LeadingSlot::Occupied, 4, vec![
                ") { <Expression@{> }",
                ", ) { <Expression@{> }",
                ") -> <Type@->> { <Expression@{> }",
                ", identifier ) { <Expression@{> }",
            ]),
            (
                "def f(x: Integer) -> -F Integer {",
                LeadingSlot::Empty,
                3,
                vec![
                    "<Expression@{> }",
                    "<Expression@{> ; }",
                    "val <Pattern@val> = <Expression@=> ; }",
                ],
            ),
            // The molder reads `case x {` as the empty match, whose closer
            // faces only its opener, so that pair stays empty; the arm is a
            // closing of the arm block's reading of the same `{`.
            (
                "def f(x: Nat) -> -F Nat { case x {",
                LeadingSlot::Empty,
                2,
                vec!["}", "<Pattern@{> => <Expression@=>> }"],
            ),
            ("def g : forall a .", LeadingSlot::Empty, 1, vec![
                "<Type@.>",
            ]),
            ("def g : forall a .", LeadingSlot::Occupied, 1, vec![""]),
            // An expression already stands in the body, so no statement
            // follows the `{` before a separator does.
            ("def x = thunk { 1", LeadingSlot::Occupied, 2, vec![
                "}", "; }",
            ]),
            ("def x =", LeadingSlot::Empty, 0, vec![]),
        ] {
            let at = frontier(&pbg, SourceText::from(source));
            let found: Vec<String> = closings(&pbg, at, leading, ClosingLimit::from(limit))
                .iter()
                .map(|closing| written(&pbg, closing))
                .collect();
            assert_eq!(want, found, "`{source}` with {leading:?}, {limit} kept");
        }
        Ok(())
    }

    #[test]
    fn every_label_a_token_offers_is_spelled_as_it_reads()
    {
        let source = "def f = X(x, 1, 1u32, 'c', \"s\\n\"); #!sh{ A=b echo 'q' $v [ ls ] 2>x }";
        let mut lexemes = BTreeSet::new();
        for token in label(SourceFragment::from(source)) {
            let start = usize::try_from(token.start).unwrap_or(usize::MAX);
            let end = usize::try_from(token.end).unwrap_or(usize::MAX);
            let text = source.get(start .. end).unwrap_or_default();
            lexemes.insert(alloc::format!("{:?}", token.lexeme));
            for offered in candidate_labels(token.lexeme, TokenText::from(text)) {
                match tile_spelling(offered) {
                    TileSpelling::Literal(spelled) => assert!(
                        spelled == text || (text.starts_with("#!") && spelled == "#!{"),
                        "`{text}` offers `{offered:?}`, spelled `{spelled}`"
                    ),
                    TileSpelling::Class(class) => {
                        assert_eq!(class, <&str>::from(offered), "a class names itself");
                        assert_ne!(class, text, "`{text}` is not its own class");
                    },
                }
            }
        }
        let every: BTreeSet<_> = [
            Lexeme::LowerWord,
            Lexeme::UpperWord,
            Lexeme::Number,
            Lexeme::TypedNumber,
            Lexeme::Character,
            Lexeme::Quote,
            Lexeme::StringFragment,
            Lexeme::EscapeSequence,
            Lexeme::Punct,
            Lexeme::ShellWord,
            Lexeme::EnvAssign,
            Lexeme::SingleQuotedContent,
            Lexeme::VariableName,
            Lexeme::SubshellOpen,
            Lexeme::SubshellClose,
            Lexeme::FileDescriptor,
            Lexeme::Space,
        ]
        .iter()
        .map(|lexeme| alloc::format!("{lexeme:?}"))
        .collect();
        assert_eq!(
            every, lexemes,
            "the sample reads every lexeme but `Unknown`"
        );
    }
}
