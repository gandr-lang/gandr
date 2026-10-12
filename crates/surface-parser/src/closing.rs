//! The shortest material that closes an open form, and how each tile of it
//! is written.
//!
//! An open form frontier is a tile occurrence of its rule's form. The
//! grammar's same-form adjacency names every tile that can follow it, holes
//! skipped; [`push_closing`] walks that adjacency to the nearest tile that
//! can end the form, charging one for each tile and one for each hole the
//! grammar requires before a tile. [`tile_spelling`] says how a label in that
//! material is written: most labels are their tile's text, a few name a
//! lexical class that any token of the class fills.
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
//! - Reversal: if one closing per frontier is not enough for a consumer — a
//!   menu of alternatives, say — the walk keeps every end at the least cost
//!   instead of the first.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
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
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
            | Crossed::Nothing => 1,
            | Crossed::Hole(_) => 2,
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
            | Ending::Here if start => Some(End {
                mold,
                tail: Crossed::Nothing,
                cost,
            }),
            | Ending::Here => {
                offer(&mut best, End {
                    mold,
                    tail: Crossed::Nothing,
                    cost,
                });
                continue;
            },
            | Ending::AfterHole(_) if start && leading == LeadingSlot::Occupied => Some(End {
                mold,
                tail: Crossed::Nothing,
                cost,
            }),
            | Ending::AfterHole(sort) => Some(End {
                mold,
                tail: Crossed::Hole(sort),
                cost: cost.hole(),
            }),
            | Ending::Not => None,
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
        | Some(held) if held.cost <= end.cost => {},
        | Some(held) => *held = end,
        | None => best.push(end),
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
            | Crossed::Hole(sort) => Ending::AfterHole(sort),
            | Crossed::Nothing => Ending::Not,
        };
    }
    Ending::Not
}

/// What comes between `left` and its same-form successor `right`.
///
/// # Specification
/// - ensures: nothing when `left`'s right context faces `right`'s label
///   directly or either mold is unknown; otherwise the first sort that context
///   faces, the hole the grammar puts between them.
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
    let Ok(steps) = pbg.step(def.rctx, Dir::Right)
    else {
        return Crossed::Nothing;
    };
    if steps
        .iter()
        .any(|step| step.crossed == StepSym::Tile(next.label))
    {
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
            | StepSym::Sort(sort) => Some(Crossed::Hole(sort)),
            | StepSym::Tile(_) => None,
        })
        .unwrap_or(Crossed::Nothing)
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;
    use alloc::collections::BTreeSet;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::error::Error;

    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::Sort;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;

    use super::ClosingReach;
    use super::LeadingSlot;
    use super::TileSpelling;
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
                    | TileSpelling::Literal(spelled) => assert!(
                        spelled == text || (text.starts_with("#!") && spelled == "#!{"),
                        "`{text}` offers `{offered:?}`, spelled `{spelled}`"
                    ),
                    | TileSpelling::Class(class) => {
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
