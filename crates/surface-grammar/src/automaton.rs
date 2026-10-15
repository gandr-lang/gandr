//! The tile automaton: what a parser reads of a pushed tile, as tables.
//!
//! A parser over a precedence-bounded grammar reads a handful of facts of
//! every tile it weighs: which side of it faces a hole, whether it continues
//! or opens a form, the form's sort and precedence, whether the form can end
//! there and what sort its next hole holds. Read as an automaton, the molds
//! are its states and the same-form successor runs of the mold table its
//! transitions, each labelled by the successor's tile label; a token stream
//! drives a form through it one successor at a time. The tables here add,
//! per state, its kind and its observation class, and per kind and sort the
//! set of states a parser admits, as bitsets over mold ids. They are derived
//! once per grammar, by every build and every thaw, in time linear in the
//! table and a sort of its readings. A table of `n` molds takes `5n` bytes —
//! a byte of kind and four of class per mold — and sixteen sets of
//! `⌈n / 64⌉` eight-byte words; for the built-in surface's some 2,600 molds
//! that is about 18 KB. The derivation adds about 0.1 ms to the 0.65 ms a
//! size-optimized `built_in` takes, about 2 ms to the 5 ms of an unoptimized
//! one; [`Pbg::tile_table_bytes`](crate::Pbg::tile_table_bytes) reports the
//! size of a given grammar's tables.
//!
//! # Tile kinds
//!
//! A tile's kind is fixed by its same-form neighbours and its bounds. A mold
//! with a successor and no predecessor starts a form, absorbing the operand
//! before it when a hole faces it on the left; one with a predecessor is a
//! mid when it has a successor or a required tail and an end otherwise; one
//! with neither neighbour is an operand or an operator by the holes facing
//! it. [`TileKind`] names the eight.
//!
//! # Observation classes
//!
//! Two molds share an [`Observation`] when everything a parser reads of a
//! pushed tile agrees, its identity, label and same-form neighbours aside:
//! the kind, the form's sort and precedence, both neighbour flags, the form
//! membership (first, complete last, required tail), the sort of the next
//! hole to its right and the shape of both bounds. Pushing either onto one
//! slope flags the same obligations, provided the two are adjacent to the
//! same open frontiers; a parser that weighs many molds over one slope pushes
//! one per class and adjacency, and one that weighs what follows them
//! compares their successors, whose classes the same table names. Classes are
//! numbered by their least mold, so the numbering is a function of the
//! grammar.
//!
//! - Alternatives: the interchangeable-mold column, which also fixes the rule,
//!   the context and the neighbours themselves and so merges only label twins;
//!   a class per mold, which leaves every candidate its own dry run.
//! - Reversal: a parser that reads another fact of a pushed tile makes that
//!   fact a component, and the classes split.
//!
//! # Tile sets
//!
//! A parser admits a candidate by its kind, its sort and the frontier it
//! meets. [`TileSet`] names the sets those tests select — what fills a hole
//! of a sort, what absorbs an operand of a sort, the prefix operators, the
//! operators that extend an operand, the mids that can open their form and
//! everything that continues a form — and each is a bitset of the table's
//! width. The sets lie end to end in one vector, the word `w` of the set at
//! [`TileSet`] position `s` at `s × width + w`; a [`MoldSet`] views one set,
//! read a [`MoldWord`] at a time, so a candidate menu is admitted by one
//! union of words and a bit test per candidate rather than by a
//! classification per candidate.
//!
//! - Alternatives: a mask per admission context, which multiplies the tables by
//!   the contexts for a union the parser computes in a few word operations; a
//!   sorted list per set, which costs a search per candidate.
//! - Reversal: a grammar whose table outgrows a cache-resident bitset per set.
//!
//! # Derivation
//!
//! The derivation reads each mold's columns off the mold table in one record
//! rather than through the per-mold queries a parser calls. A size-optimized
//! build shares a generic instantiation across crates, and each query's
//! specification wrapper is generic: instantiated here, the parser's hot
//! paths link this crate's out-of-line copy instead of inlining their own,
//! which costs a clean corpus mold about ten percent. Reading the columns
//! directly leaves the parser's instantiations as they were.
//!
//! - Alternatives: the per-mold queries, cheaper to write and the regression
//!   above; disabling shared generics, a workspace-wide build change for one
//!   crate's call shape.
//! - Reversal: a toolchain that inlines a shared instantiation at its callers,
//!   or a build that stops sharing generics.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::ops::BitOr;

use anodized::spec;
use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Prec;

use crate::model::PbgError;
use crate::model::Sort;
use crate::mold::MoldColumns;
use crate::mold::MoldDef;
use crate::mold::MoldInSet;
use crate::mold::MoldTable;
use crate::mold::StepSym;

/// How many sorts a hole can hold: the [`Sort`] tags run below it.
const SORTS: usize = 6;

/// How many tile sets the table holds: a fill and an absorb set per sort,
/// and four more.
const SET_COUNT: usize = 2 * SORTS + 4;

/// The tile sets in position order: the set at position `s` is `SETS[s]`.
const SETS: [TileSet; SET_COUNT] = [
    TileSet::Fills(Sort::Item),
    TileSet::Fills(Sort::Pattern),
    TileSet::Fills(Sort::Expression),
    TileSet::Fills(Sort::Type),
    TileSet::Fills(Sort::Instantiation),
    TileSet::Fills(Sort::ModuleMember),
    TileSet::Absorbs(Sort::Item),
    TileSet::Absorbs(Sort::Pattern),
    TileSet::Absorbs(Sort::Expression),
    TileSet::Absorbs(Sort::Type),
    TileSet::Absorbs(Sort::Instantiation),
    TileSet::Absorbs(Sort::ModuleMember),
    TileSet::Prefixes,
    TileSet::LeftOperators,
    TileSet::FirstMids,
    TileSet::Continuations,
];

/// How many molds one [`MoldWord`] covers.
const WORD_BITS: usize = 64;

/// What a pushed tile is to the slope, read off its same-form neighbours,
/// its required tail and its bounds.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TileKind
{
    /// No same-form neighbour and no hole on either side: a whole operand.
    Operand,
    /// No same-form neighbour; a hole faces it on the right only.
    Prefix,
    /// No same-form neighbour; a hole faces it on the left only.
    Postfix,
    /// No same-form neighbour; holes face it on both sides.
    Infix,
    /// A successor and no predecessor, no hole on the left: opens a form at
    /// a fresh slot.
    Start,
    /// A successor and no predecessor, a hole on the left: opens a form over
    /// the operand before it.
    AbsorbingStart,
    /// A predecessor and either a successor or a required tail.
    Mid,
    /// A predecessor, no successor and no required tail.
    End,
}

/// The class of molds a parser reads alike once pushed, their identities,
/// labels and same-form neighbours aside.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Observation(u32);

impl From<Observation> for u32
{
    /// Reads the class number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(class: Observation) -> Self
    {
        class.0
    }
}

/// A set of molds a parser admits by kind and sort.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TileSet
{
    /// The operands and fresh starts of a sort: what fills a hole of it.
    Fills(Sort),
    /// The absorbing starts of a sort: what extends an operand of it.
    Absorbs(Sort),
    /// The prefix operators.
    Prefixes,
    /// The infix and postfix operators: what extends an operand on its right.
    LeftOperators,
    /// The mids that can open their form.
    FirstMids,
    /// The mids and ends: what continues an open form.
    Continuations,
}

/// A tile set's position among the table's sets.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SetPosition(usize);

impl TileSet
{
    /// The set's position among the table's sets: its index in [`SETS`],
    /// which the derivation places the set's bits by. Fills take the sort
    /// tags, absorbs the tags past them, and the four kind sets the four
    /// positions after those. The automaton's witness reads every set of
    /// every word against the kinds and sorts it is defined by, so a
    /// position that disagrees with [`SETS`] shows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn position(self) -> SetPosition
    {
        SetPosition(match self {
            Self::Fills(Sort::Item) => 0,
            Self::Fills(Sort::Pattern) => 1,
            Self::Fills(Sort::Expression) => 2,
            Self::Fills(Sort::Type) => 3,
            Self::Fills(Sort::Instantiation) => 4,
            Self::Fills(Sort::ModuleMember) => 5,
            Self::Absorbs(Sort::Item) => 6,
            Self::Absorbs(Sort::Pattern) => 7,
            Self::Absorbs(Sort::Expression) => 8,
            Self::Absorbs(Sort::Type) => 9,
            Self::Absorbs(Sort::Instantiation) => 10,
            Self::Absorbs(Sort::ModuleMember) => 11,
            Self::Prefixes => 12,
            Self::LeftOperators => 13,
            Self::FirstMids => 14,
            Self::Continuations => 15,
        })
    }
}

/// How many bytes a grammar's tile tables hold.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TileTableBytes(pub usize);

/// Which [`MoldWord`] of a set covers a mold: mold `id` is bit `id % 64` of
/// word `id / 64`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MoldWordIndex(usize);

impl MoldWordIndex
{
    /// The word covering `mold`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the mold's id divided by the word's width; an id past the
    ///   platform's word size reads the last index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness tests every mold through the
    ///   word this names; an off-by-one width puts molds in their neighbours'
    ///   words.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| usize::try_from(u32::from(mold)).map_or(ret.0 == usize::MAX, |id| Some(ret.0) == id.checked_div(WORD_BITS)))]
    #[inline]
    #[must_use]
    pub fn of(mold: MoldId) -> Self
    {
        Self(usize::try_from(u32::from(mold)).map_or(usize::MAX, |id| {
            id.checked_div(WORD_BITS).unwrap_or(usize::MAX)
        }))
    }
}

/// Sixty-four consecutive molds' membership in a set: bit `i` of the word
/// at [`MoldWordIndex`] `w` is mold `64 w + i`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct MoldWord(u64);

impl MoldWord
{
    /// Whether `mold` is in the word, read at the bit its id names; the
    /// caller pairs the word with the mold's [`MoldWordIndex`].
    ///
    /// # Specification
    /// - requires: the word is the one [`MoldWordIndex::of`] names for `mold`.
    /// - ensures: the bit at the mold's id modulo the word's width.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness reads every mold's bit in
    ///   every set; a shifted or inverted bit misreads the membership.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| bool::from(ret) == u32::from(mold).checked_rem(64).and_then(|bit| self.0.checked_shr(bit)).is_some_and(|shifted| shifted & 1 == 1))]
    #[inline]
    #[must_use]
    pub fn contains(
        self,
        mold: MoldId,
    ) -> MoldInSet
    {
        let bit = u32::from(mold).checked_rem(64).unwrap_or(0);
        MoldInSet::from(
            self.0
                .checked_shr(bit)
                .is_some_and(|shifted| shifted & 1 == 1),
        )
    }

    /// The word with `other`'s molds removed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn without(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 & !other.0)
    }
}

impl BitOr for MoldWord
{
    type Output = Self;

    /// The union of two words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn bitor(
        self,
        rhs: Self,
    ) -> Self
    {
        Self(self.0 | rhs.0)
    }
}

/// A tile set's molds: a view of its words, one per [`MoldWordIndex`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MoldSet<'table>(&'table [MoldWord]);

impl MoldSet<'_>
{
    /// The word at `at`: empty past the table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the stored word at the index, the empty word past the set.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness reads every mold's bit
    ///   through the word its index names and the first word past the table; a
    ///   shifted read misreads the membership.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret == self.0.get(at.0).copied().unwrap_or_default())]
    #[inline]
    #[must_use]
    pub fn word(
        self,
        at: MoldWordIndex,
    ) -> MoldWord
    {
        self.0.get(at.0).copied().unwrap_or_default()
    }

    /// Whether `mold` is in the set; false past the table.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the mold's bit in the word its index names.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`word`](Self::word).
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret == self.word(MoldWordIndex::of(mold)).contains(mold))]
    #[inline]
    #[must_use]
    pub fn contains(
        self,
        mold: MoldId,
    ) -> MoldInSet
    {
        self.word(MoldWordIndex::of(mold)).contains(mold)
    }
}

/// The shape of one precedence bound, for comparing readings.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum BoundShape
{
    /// The bottom bound.
    Bottom,
    /// The form's own group: a hole can face the tile on that side.
    Value,
    /// The root bound: no hole faces the tile on that side.
    Root,
}

impl BoundShape
{
    /// The shape of `bound`.
    ///
    /// # Specification
    /// trivial.
    const fn of(bound: Bound<Prec>) -> Self
    {
        match bound {
            Bound::Bottom => Self::Bottom,
            Bound::Value(_) => Self::Value,
            Bound::Root => Self::Root,
        }
    }
}

/// Everything a parser reads of a pushed tile, its identity, label and
/// same-form neighbours aside: what an [`Observation`] classes.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Reading
{
    /// The tile's kind.
    kind: TileKind,
    /// The form's sort.
    sort: Sort,
    /// The form's precedence group.
    prec: Prec,
    /// Whether the mold has a same-form predecessor and successor.
    neighbours: (bool, bool),
    /// Whether the mold can open its form, end it with no hole required,
    /// and end it only once a trailing hole is filled.
    membership: (bool, bool, bool),
    /// The sort of the first hole to the mold's right in its form.
    hole: Option<Sort>,
    /// The shapes of the mold's left and right bounds.
    bounds: (BoundShape, BoundShape),
}

impl Reading
{
    /// The reading of a mold defined by `def`, whose table columns are
    /// `columns`; a mold past the table reads as no neighbour, no
    /// membership, root bounds and no hole.
    ///
    /// # Specification
    /// - requires: `def` is the table's mold the columns were read for.
    /// - ensures: the kind is a start, absorbing when a hole faces it on the
    ///   left, for a successor and no predecessor; a mid for a predecessor and
    ///   a successor or a required tail; an end for a predecessor alone;
    ///   otherwise an operand, prefix, postfix or infix by the holes facing it.
    ///   The other components are the columns' answers.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness rereads every built-in mold's
    ///   kind from the public flags and bounds; a swapped flag or side
    ///   misclassifies starts, ends or operators.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret.sort == def.sort && ret.prec == def.prec && ret.neighbours == (columns.is_some_and(|held| bool::from(held.predecessor)), columns.is_some_and(|held| bool::from(held.successor))) && (ret.kind == TileKind::Mid) == (ret.neighbours.0 && (ret.neighbours.1 || ret.membership.2)))]
    fn of(
        columns: Option<MoldColumns<'_>>,
        def: &MoldDef,
    ) -> Self
    {
        let (left, right) = columns.map_or((Bound::Root, Bound::Root), |held| held.bounds);
        let (left, right) = (BoundShape::of(left), BoundShape::of(right));
        let flag = |read: fn(MoldColumns<'_>) -> bool| columns.is_some_and(read);
        let has_pred = flag(|held| bool::from(held.predecessor));
        let has_succ = flag(|held| bool::from(held.successor));
        let required_tail = flag(|held| bool::from(held.required_tail));
        let kind = match (has_pred, has_succ) {
            (false, true) if left == BoundShape::Value => TileKind::AbsorbingStart,
            (false, true) => TileKind::Start,
            (true, true) => TileKind::Mid,
            (true, false) if required_tail => TileKind::Mid,
            (true, false) => TileKind::End,
            (false, false) => match (left == BoundShape::Value, right == BoundShape::Value) {
                (false, false) => TileKind::Operand,
                (false, true) => TileKind::Prefix,
                (true, false) => TileKind::Postfix,
                (true, true) => TileKind::Infix,
            },
        };
        let hole = columns.and_then(|held| {
            held.right_steps.iter().find_map(|step| match step.crossed {
                StepSym::Sort(sort) => Some(sort),
                StepSym::Tile(_) => None,
            })
        });
        Self {
            kind,
            sort: def.sort,
            prec: def.prec,
            neighbours: (has_pred, has_succ),
            membership: (
                flag(|held| bool::from(held.first)),
                flag(|held| bool::from(held.complete_last)),
                required_tail,
            ),
            hole,
            bounds: (left, right),
        }
    }

    /// The sets a mold of this reading belongs to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an operand or start fills its sort; an absorbing start
    ///   absorbs its sort; a prefix is a prefix; an infix or postfix extends an
    ///   operand; a mid or end continues a form, and a mid that can open its
    ///   form is also a first mid.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness reads every built-in mold's
    ///   membership in every set against its kind and sort; a kind in the wrong
    ///   set or a lost first mid shows.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| matches!(ret, [Some(_), _]) && ret.iter().flatten().any(|&held| held == TileSet::FirstMids) == (self.kind == TileKind::Mid && self.membership.0))]
    fn sets(self) -> [Option<TileSet>; 2]
    {
        match self.kind {
            TileKind::Operand | TileKind::Start => [Some(TileSet::Fills(self.sort)), None],
            TileKind::AbsorbingStart => [Some(TileSet::Absorbs(self.sort)), None],
            TileKind::Prefix => [Some(TileSet::Prefixes), None],
            TileKind::Infix | TileKind::Postfix => [Some(TileSet::LeftOperators), None],
            TileKind::Mid => [
                Some(TileSet::Continuations),
                self.membership.0.then_some(TileSet::FirstMids),
            ],
            TileKind::End => [Some(TileSet::Continuations), None],
        }
    }
}

/// The tile automaton's per-grammar tables: each mold's kind and
/// observation class, and the tile sets as bitsets.
#[derive(Clone, Debug)]
pub struct TileAutomaton
{
    /// Each mold's kind, by id.
    kinds: Vec<TileKind>,
    /// Each mold's observation class, by id.
    observations: Vec<Observation>,
    /// How many words each set spans.
    width: usize,
    /// The sets' words, set after set in [`TileSet::position`] order.
    sets: Vec<MoldWord>,
}

impl TileAutomaton
{
    /// Derives the tables of `table`.
    ///
    /// # Specification
    /// - requires: `table` is assembled.
    /// - ensures: one kind and one class per mold; two molds share a class
    ///   exactly when their readings agree, and classes are numbered in order
    ///   of their least mold; each set holds exactly the molds whose reading
    ///   puts them in it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over the built-in grammar every mold's kind, class
    ///   and set memberships are compared, through the public queries, with the
    ///   reading's components; a dropped component merges molds a parser tells
    ///   apart, and a misplaced bit admits a mold no frontier takes.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret.kinds.len() == table.len().0 && ret.observations.len() == ret.kinds.len() && ret.sets.len() == SET_COUNT.saturating_mul(ret.width) && ret.width.saturating_mul(WORD_BITS) >= ret.kinds.len())]
    pub(crate) fn derive(table: &MoldTable) -> Self
    {
        let count = table.len().0;
        let width = count.div_ceil(WORD_BITS);
        let mut kinds = Vec::with_capacity(count);
        let mut observations = Vec::with_capacity(count);
        let mut sets = vec![MoldWord(0); SET_COUNT.saturating_mul(width)];
        let mut classes: BTreeMap<Reading, Observation> = BTreeMap::new();
        for (id, def) in table.iter() {
            let reading = Reading::of(table.columns(id), def);
            let next = Observation(u32::try_from(classes.len()).unwrap_or(u32::MAX));
            let class = *classes.entry(reading).or_insert(next);
            kinds.push(reading.kind);
            observations.push(class);
            let Ok(raw) = usize::try_from(u32::from(id))
            else {
                continue;
            };
            let word = raw.checked_div(WORD_BITS).unwrap_or(0);
            let bit = 1_u64
                .checked_shl(u32::try_from(raw.checked_rem(WORD_BITS).unwrap_or(0)).unwrap_or(0))
                .unwrap_or(0);
            // Each set's bits are placed by its index in `SETS`, which is its
            // position: the derivation calls none of the queries a parser's
            // hot paths inline, so this crate instantiates none of them.
            for set in reading.sets().into_iter().flatten() {
                if let Some(slot) = SETS
                    .iter()
                    .position(|&held| held == set)
                    .and_then(|position| position.checked_mul(width))
                    .and_then(|start| start.checked_add(word))
                    .and_then(|at| sets.get_mut(at))
                {
                    slot.0 |= bit;
                }
            }
        }
        Self {
            kinds,
            observations,
            width,
            sets,
        }
    }

    /// The kind of mold `id`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the derived kind for a mold in the table.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness reads every built-in mold and
    ///   the first id past the table through this query.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::UnknownMold { id: missing } if *missing == id), |kind| usize::try_from(u32::from(id)).ok().and_then(|at| self.kinds.get(at)) == Some(kind)))]
    #[inline]
    pub(crate) fn kind(
        &self,
        id: MoldId,
    ) -> Result<TileKind, PbgError>
    {
        match usize::try_from(u32::from(id))
            .ok()
            .and_then(|at| self.kinds.get(at))
        {
            Some(&kind) => Ok(kind),
            None => Err(PbgError::UnknownMold { id }),
        }
    }

    /// The observation class of mold `id`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the derived class for a mold in the table.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness reads every built-in mold and
    ///   the first id past the table through this query.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::UnknownMold { id: missing } if *missing == id), |class| usize::try_from(u32::from(id)).ok().and_then(|at| self.observations.get(at)) == Some(class)))]
    #[inline]
    pub(crate) fn observation(
        &self,
        id: MoldId,
    ) -> Result<Observation, PbgError>
    {
        match usize::try_from(u32::from(id))
            .ok()
            .and_then(|at| self.observations.get(at))
        {
            Some(&class) => Ok(class),
            None => Err(PbgError::UnknownMold { id }),
        }
    }

    /// The molds of `set`, as a view of its words.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the set's stored words, one per [`MoldWordIndex`] of the
    ///   table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the automaton's witness reads every mold's bit of
    ///   every set through this view; a view of a neighbouring set or a shifted
    ///   range misreads the membership.
    /// - witness: `tests::walk::tile_kinds_observations_and_sets_agree_with_the_table`
    #[spec(ensures: |ret| ret.0.len() == self.width || ret.0.is_empty())]
    #[inline]
    pub(crate) fn set(
        &self,
        set: TileSet,
    ) -> MoldSet<'_>
    {
        let start = set.position().0.checked_mul(self.width);
        let end = start.and_then(|start| start.checked_add(self.width));
        MoldSet(
            start
                .zip(end)
                .and_then(|(start, end)| self.sets.get(start .. end))
                .unwrap_or(&[]),
        )
    }

    /// How many bytes the tables hold: the kinds, the classes and the sets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn bytes(&self) -> TileTableBytes
    {
        let kinds = self.kinds.len().saturating_mul(size_of::<TileKind>());
        let classes = self
            .observations
            .len()
            .saturating_mul(size_of::<Observation>());
        let sets = self.sets.len().saturating_mul(size_of::<MoldWord>());
        TileTableBytes(kinds.saturating_add(classes).saturating_add(sets))
    }
}
