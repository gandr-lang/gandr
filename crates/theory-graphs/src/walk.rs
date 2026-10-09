//! The walk machine: a finite, declarative description of how a grammar's
//! tiles meet, closed into the canonical walks between every pair of ends.
//!
//! A [`Walk`] alternates swings — runs of nonterminals — with the stances
//! between them. A [`WalkSpec`] supplies walks two ways: directly, between two
//! ends, and generated, by a swing machine whose arcs extend a swing, cross a
//! stance into a new one, or emit the walk so far at an end.
//! [`WalkIndex::build`] closes the direct walks transitively through
//! intermediate ends, keeps the valid and minimal walks of each row in the
//! canonical order, and fingerprints the result; it answers the equal, less and
//! greater queries a parser asks of two adjacent tiles.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::error::Error;
use core::fmt::Debug;
use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;
use core::num::TryFromIntError;

use crate::Fingerprint;
use crate::FingerprintByte;
use crate::FingerprintWord64;
use crate::Fnv64;
use crate::SwingHeight;
use crate::WalkChainLength;
use crate::WalkHeight;
use crate::types::primitive_newtype;

/// The direction a walk faces.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Dir
{
    /// Left-facing.
    Left,
    /// Right-facing.
    Right,
}

/// One end of a walk: the root, or a stance.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum End<T>
{
    /// The root, which every walk of the whole program starts from.
    Root,
    /// A stance.
    Node(T),
}

primitive_newtype! {
    /// Whether a stance is tile-sorted, which the minimality filter reads.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct StanceTileSorted(bool);
}

primitive_newtype! {
    /// A symbol's stable key in the walk fingerprint.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct WalkSymbolKey(u64);
}

impl From<WalkSymbolKey> for FingerprintWord64
{
    /// Frames the key as a fingerprint word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WalkSymbolKey) -> Self
    {
        Self::from(u64::from(value))
    }
}

primitive_newtype! {
    /// Whether every swing of a walk has zero height.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct WalkEquality(bool);
}

primitive_newtype! {
    /// Whether a walk's destination-adjacent swing has nonzero height.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct WalkInequality(bool);
}

primitive_newtype! {
    /// Whether a walk survives the minimality filter.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    struct WalkMinimal(bool);
}

/// The symbol vocabulary a walk machine runs over.
pub trait WalkSym: Clone + Debug + Eq + Ord
{
    /// A nonterminal a swing passes through.
    type Nonterminal: Clone + Eq + Ord;
    /// A stance between two swings, and a walk's end.
    type Stance: Clone + Eq + Ord;
    /// The sort nonterminals and stances share.
    type Sort: Clone + Eq + Ord;
    /// The bounds that refine a nonterminal's sort when a swing closure
    /// decides whether it has already continued from a state.
    type Bounds: Clone + Eq + Ord;
    /// A tile label, the key of the molds projection.
    type Label: Clone + Eq + Ord;
    /// A mold, the value of the molds projection.
    type Mold: Clone + Eq + Ord;

    /// Reports a nonterminal's sort.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same nonterminal always has the same sort.
    /// - panics: none.
    fn nonterminal_sort(nonterminal: &Self::Nonterminal) -> Self::Sort;

    /// Reports a nonterminal's bounds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same nonterminal always has the same bounds.
    /// - panics: none.
    fn nonterminal_bounds(nonterminal: &Self::Nonterminal) -> Self::Bounds;

    /// Reports a stance's sort.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same stance always has the same sort.
    /// - panics: none.
    fn stance_sort(stance: &Self::Stance) -> Self::Sort;

    /// Reports whether a stance is tile-sorted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same stance always gives the same answer.
    /// - panics: none.
    fn stance_tile_sorted(stance: &Self::Stance) -> StanceTileSorted;

    /// Reports the label and mold of a tile stance; any other stance has
    /// none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same stance always gives the same answer.
    /// - panics: none.
    fn label_mold(stance: &Self::Stance) -> Option<(Self::Label, Self::Mold)>;

    /// Reports a nonterminal's fingerprint key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same nonterminal always has the same key, across
    ///   processes and builds.
    /// - panics: none.
    fn nonterminal_key(nonterminal: &Self::Nonterminal) -> WalkSymbolKey;

    /// Reports a stance's fingerprint key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same stance always has the same key, across processes and
    ///   builds.
    /// - panics: none.
    fn stance_key(stance: &Self::Stance) -> WalkSymbolKey;
}

/// One end of a machine walk.
type WalkEnd<S> = End<<S as WalkSym>::Stance>;
/// One walk over a machine's symbols.
type MachineWalk<S> = Walk<<S as WalkSym>::Nonterminal, <S as WalkSym>::Stance>;
/// One direct walk: its direction, ends and shape.
type DirectStep<S> = (Dir, WalkEnd<S>, WalkEnd<S>, MachineWalk<S>);
/// One swing-closure seed: its direction, source end and first nonterminal.
type SwingSeed<S> = (Dir, WalkEnd<S>, <S as WalkSym>::Nonterminal);
/// The key of a direction-sensitive row.
type DirectKey<S> = (Dir, WalkEnd<S>, WalkEnd<S>);
/// The key of a query row.
type QueryKey<S> = (WalkEnd<S>, WalkEnd<S>);
/// Direction-sensitive rows.
type DirectRows<S> = BTreeMap<DirectKey<S>, Vec<MachineWalk<S>>>;
/// Query rows.
type QueryRows<S> = BTreeMap<QueryKey<S>, Vec<MachineWalk<S>>>;
/// One molded end and its mold.
type MoldRow<S> = (WalkEnd<S>, <S as WalkSym>::Mold);
/// Molded ends by label.
type MoldRows<S> = BTreeMap<<S as WalkSym>::Label, Vec<MoldRow<S>>>;
/// Every end and walk one swing closure emits.
type SwingClosureOutput<S> = Vec<(WalkEnd<S>, MachineWalk<S>)>;
/// One queued outer-closure prefix: its last end, its walk, and the ends its
/// path has passed through.
type ClosureQueueItem<S> = (WalkEnd<S>, MachineWalk<S>, BTreeSet<WalkEnd<S>>);
/// Direct rows indexed by direction and source end.
type RowsBySource<'rows, S> =
    BTreeMap<(Dir, &'rows WalkEnd<S>), Vec<(&'rows WalkEnd<S>, &'rows Vec<MachineWalk<S>>)>>;
/// Swing arcs indexed by their source nonterminal.
type ArcsBySource<'spec, S> = BTreeMap<&'spec <S as WalkSym>::Nonterminal, Vec<&'spec SwingArc<S>>>;
/// The canonical-order key of one machine walk.
type WalkSortKey<S> =
    CanonicalWalkKey<<S as WalkSym>::Nonterminal, <S as WalkSym>::Stance, <S as WalkSym>::Sort>;

/// A non-empty run of nonterminals, in source-to-destination order.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Swing<N>
{
    /// The nonterminals, source first.
    nonterminals: Vec<N>,
}

impl<N> Swing<N>
{
    /// Builds a swing from its nonterminals.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the swing holds `nonterminals` in order.
    /// - fails: `nonterminals` is empty.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::EmptySwing`] for no nonterminals.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — singleton and longer swings are accepted
    ///   and an empty one is refused by name.
    /// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
    #[inline]
    pub fn new(nonterminals: Vec<N>) -> Result<Self, WalkBuildError>
    {
        if nonterminals.is_empty() {
            Err(WalkBuildError::EmptySwing)
        }
        else {
            Ok(Self { nonterminals })
        }
    }

    /// Borrows the nonterminals, source first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nonterminals(&self) -> &[N]
    {
        &self.nonterminals
    }

    /// Reports the swing's height: its nonterminal count less one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a singleton swing has height zero; otherwise the height is
    ///   one less than the nonterminal count.
    /// - fails: the count exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::ArithmeticOverflow`] for a count past `u32`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — the canonical order observes zero and
    ///   nonzero heights through exact rows.
    /// - witness: `tests::walk::canonical_height_counts_nonzero_swings_only`
    #[inline]
    pub fn height(&self) -> Result<SwingHeight, WalkBuildError>
    {
        let count = u32::try_from(self.nonterminals.len())?;
        count
            .checked_sub(1)
            .map(SwingHeight::from)
            .ok_or(WalkBuildError::InvalidWalkShape)
    }
}

impl<N: Ord> Ord for Swing<N>
{
    /// Orders swings by their nonterminals, lexicographically.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.nonterminals.cmp(&other.nonterminals)
    }
}

impl<N: Ord> PartialOrd for Swing<N>
{
    /// Orders swings as [`Ord`] does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

/// One step of a walk given as a sequence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WalkStep<N, T>
{
    /// A swing.
    Swing(Swing<N>),
    /// A stance between two swings.
    Stance(T),
}

/// A walk: swings alternating with the stances between them, beginning and
/// ending with a swing, in source-to-destination order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Walk<N, T>
{
    /// The swings; never empty.
    swings: Vec<Swing<N>>,
    /// The stances; exactly one fewer than the swings.
    stances: Vec<T>,
}

impl<N, T> Walk<N, T>
{
    /// Builds a walk from its swings and the stances between them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the walk holds `swings` and `stances` in order.
    /// - fails: `swings` is empty, or there is not exactly one fewer stance
    ///   than swings.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::InvalidWalkShape`] for a shape that does not
    /// alternate; [`WalkBuildError::ArithmeticOverflow`] when the stance count
    /// is `usize::MAX`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — singleton and multi-swing walks are
    ///   accepted, and a walk with as many stances as swings is refused.
    /// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
    #[inline]
    pub fn new(
        swings: Vec<Swing<N>>,
        stances: Vec<T>,
    ) -> Result<Self, WalkBuildError>
    {
        if swings.is_empty() {
            return Err(WalkBuildError::InvalidWalkShape);
        }
        let expected = stances
            .len()
            .checked_add(1)
            .ok_or(WalkBuildError::ArithmeticOverflow)?;
        if swings.len() == expected {
            Ok(Self { swings, stances })
        }
        else {
            Err(WalkBuildError::InvalidWalkShape)
        }
    }

    /// Builds a walk from a sequence of steps.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the walk is the steps' swings and stances in
    ///   order.
    /// - fails: the steps are empty, do not alternate, or begin or end with a
    ///   stance.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::InvalidWalkShape`] for steps that do not alternate.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — an alternating sequence equals the same
    ///   walk built from parts, and a trailing stance and two adjacent swings
    ///   are each refused.
    /// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
    #[inline]
    pub fn from_steps(steps: Vec<WalkStep<N, T>>) -> Result<Self, WalkBuildError>
    {
        let mut swings = Vec::new();
        let mut stances = Vec::new();
        for step in steps {
            match (swings.len() == stances.len(), step) {
                | (true, WalkStep::Swing(swing)) => swings.push(swing),
                | (false, WalkStep::Stance(stance)) => stances.push(stance),
                | (true, WalkStep::Stance(_)) | (false, WalkStep::Swing(_)) => {
                    return Err(WalkBuildError::InvalidWalkShape);
                },
            }
        }
        Self::new(swings, stances)
    }

    /// Borrows the swings, source first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn swings(&self) -> &[Swing<N>]
    {
        &self.swings
    }

    /// Borrows the stances, source first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn stances(&self) -> &[T]
    {
        &self.stances
    }

    /// Reports whether every swing has zero height: the shape of an equality
    /// walk.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when every swing has height zero.
    /// - fails: a swing's length exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::ArithmeticOverflow`] for a swing past `u32`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — a single-swing equality walk is answered by
    ///   the equal query and a two-nonterminal walk by the less query.
    /// - witness: `tests::walk::query_orientation_filters_direct_rows`
    #[inline]
    pub fn is_eq(&self) -> Result<WalkEquality, WalkBuildError>
    {
        for swing in &self.swings {
            if swing.height()? != SwingHeight::default() {
                return Ok(WalkEquality::from(false));
            }
        }
        Ok(WalkEquality::from(true))
    }

    /// Reports whether the destination-adjacent swing has nonzero height: the
    /// shape of a less or greater walk.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when the last swing has nonzero height.
    /// - fails: the last swing's length exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::ArithmeticOverflow`] for a swing past `u32`;
    /// [`WalkBuildError::InvalidWalkShape`] for a walk without swings, which
    /// [`Walk::new`] never builds.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — a walk whose prefix rises but whose last
    ///   swing is flat is excluded from the less query.
    /// - witness: `tests::walk::direct_rows_reject_nonzero_prefix_with_zero_height_final_swing`
    #[inline]
    pub fn is_neq(&self) -> Result<WalkInequality, WalkBuildError>
    {
        let last = self.swings.last().ok_or(WalkBuildError::InvalidWalkShape)?;
        let height = last.height()?;
        Ok(WalkInequality::from(height != SwingHeight::default()))
    }

    /// Reports the walk's height: how many swings have nonzero height.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: counts exactly the swings of nonzero height.
    /// - fails: a swing's length or the count exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::ArithmeticOverflow`] past `u32`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — the canonical order's first key separates
    ///   one rising swing from two.
    /// - witness: `tests::walk::canonical_height_counts_nonzero_swings_only`
    #[inline]
    pub fn height(&self) -> Result<WalkHeight, WalkBuildError>
    {
        let mut height = 0_u32;
        for swing in &self.swings {
            if swing.height()? != SwingHeight::default() {
                height = height
                    .checked_add(1)
                    .ok_or(WalkBuildError::ArithmeticOverflow)?;
            }
        }
        Ok(WalkHeight::from(height))
    }

    /// Reports the walk's alternating length: twice its swing count, less
    /// one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns `2 * swings - 1`.
    /// - fails: the length exceeds `u32`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::ArithmeticOverflow`] past `u32`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — the cap refuses a two-swing walk under a
    ///   cap of one, naming length three.
    /// - witness: `tests::walk::cyclic_outer_closure_terminates_and_cap_errors_are_typed`
    #[inline]
    pub fn chain_len(&self) -> Result<WalkChainLength, WalkBuildError>
    {
        let swings = u32::try_from(self.swings.len())?;
        swings
            .checked_mul(2)
            .and_then(|doubled| doubled.checked_sub(1))
            .map(WalkChainLength::from)
            .ok_or(WalkBuildError::ArithmeticOverflow)
    }

    /// Joins this walk to `right` through the stance `mid` both meet at.
    ///
    /// # Specification
    /// - requires: this walk ends at `mid` and `right` starts there.
    /// - ensures: the swings of both, with `mid` and the stances of both
    ///   between them.
    /// - fails: `mid` is the root, which no walk passes through.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::InvalidWalkShape`] for a root `mid`.
    fn append_through(
        &self,
        mid: &End<T>,
        right: &Self,
    ) -> Result<Self, WalkBuildError>
    where
        N: Clone,
        T: Clone,
    {
        let End::Node(ref stance) = *mid
        else {
            return Err(WalkBuildError::InvalidWalkShape);
        };
        let mut swings = self.swings.clone();
        swings.extend(right.swings.iter().cloned());
        let mut stances = self.stances.clone();
        stances.push(stance.clone());
        stances.extend(right.stances.iter().cloned());
        Self::new(swings, stances)
    }
}

impl<N: Ord, T: Ord> Ord for Walk<N, T>
{
    /// Orders walks by their swings, then their stances.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.swings
            .cmp(&other.swings)
            .then_with(|| self.stances.cmp(&other.stances))
    }
}

impl<N: Ord, T: Ord> PartialOrd for Walk<N, T>
{
    /// Orders walks as [`Ord`] does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

/// What a swing-machine arc does to the swing in progress.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SwingAdvance<N, T>
{
    /// Leaves the swing as it is.
    Stay,
    /// Extends the swing by one nonterminal.
    Extend(N),
    /// Crosses a stance and starts a new swing.
    Cross
    {
        /// The stance crossed.
        stance: T,
        /// The new swing's first nonterminal.
        next: N,
    },
}

/// One arc of the swing machine: from a nonterminal, an advance, then an
/// emitted walk, a continuation, or both.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SwingArc<S: WalkSym>
{
    /// The nonterminal the arc leaves.
    from: S::Nonterminal,
    /// What the arc does to the swing.
    advance: SwingAdvance<S::Nonterminal, S::Stance>,
    /// The end the walk so far is emitted at, if the arc emits.
    emit: Option<End<S::Stance>>,
    /// The nonterminal the closure continues from, if the arc continues.
    continue_from: Option<S::Nonterminal>,
}

impl<S: WalkSym> SwingArc<S>
{
    /// Builds an arc that emits, continues, or both.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the arc holds the four parts as given.
    /// - fails: the arc neither emits nor continues.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::UselessArc`] for an arc that does neither.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — emitting, continuing and dual arcs build,
    ///   and an arc that does neither is refused by name.
    /// - witness: `tests::walk::construction_guards_refuse_malformed_shapes`
    #[inline]
    pub fn new(
        from: S::Nonterminal,
        advance: SwingAdvance<S::Nonterminal, S::Stance>,
        emit: Option<End<S::Stance>>,
        continue_from: Option<S::Nonterminal>,
    ) -> Result<Self, WalkBuildError>
    {
        if emit.is_none() && continue_from.is_none() {
            return Err(WalkBuildError::UselessArc);
        }
        Ok(Self {
            from,
            advance,
            emit,
            continue_from,
        })
    }
}

/// A finite walk machine: the ends, the direct walks, the swing seeds and
/// arcs, and the cap on how long a walk may grow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WalkSpec<S: WalkSym>
{
    /// The ends, the root among them.
    ends: BTreeSet<End<S::Stance>>,
    /// The direct walks. A set keeps insertion logarithmic and insertion
    /// order unobservable.
    direct_steps: BTreeSet<DirectStep<S>>,
    /// The swing-closure seeds.
    swing_seeds: BTreeSet<SwingSeed<S>>,
    /// The swing-machine arcs.
    swing_arcs: BTreeSet<SwingArc<S>>,
    /// The nonterminal the molds projection enters from; with none, the
    /// projection is empty.
    root_entry: Option<S::Nonterminal>,
    /// The longest alternating length a walk may reach.
    max_chain_len: WalkChainLength,
}

impl<S: WalkSym> WalkSpec<S>
{
    /// Starts a machine whose only end is the root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the machine has the root as its one end, no walks,
    ///   seeds or arcs, and `max_chain_len` as its cap.
    /// - fails: the cap is zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::ZeroMaxChainLen`] for a zero cap.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — a zero cap is refused, and every accepted
    ///   cap is reported back exactly.
    /// - witness: `tests::walk::max_chain_len_reports_exact_accepted_cap`
    #[inline]
    pub fn new(max_chain_len: WalkChainLength) -> Result<Self, WalkBuildError>
    {
        if max_chain_len == WalkChainLength::default() {
            return Err(WalkBuildError::ZeroMaxChainLen);
        }
        Ok(Self {
            ends: BTreeSet::from([End::Root]),
            direct_steps: BTreeSet::new(),
            swing_seeds: BTreeSet::new(),
            swing_arcs: BTreeSet::new(),
            root_entry: None,
            max_chain_len,
        })
    }

    /// Adds an end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn insert_end(
        &mut self,
        end: End<S::Stance>,
    )
    {
        self.ends.insert(end);
    }

    /// Adds a direct walk from `src` to `dst`, and both ends.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the walk and both ends are in the machine; adding the same
    ///   walk again changes nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — repeated and permuted insertions build the
    ///   same index and fingerprint.
    /// - witness: `tests::walk::insertion_permutation_duplicate_canonicalization_and_fingerprint_are_stable`
    #[inline]
    pub fn insert_direct(
        &mut self,
        dir: Dir,
        src: End<S::Stance>,
        dst: End<S::Stance>,
        walk: Walk<S::Nonterminal, S::Stance>,
    )
    {
        self.insert_end(src.clone());
        self.insert_end(dst.clone());
        self.direct_steps.insert((dir, src, dst, walk));
    }

    /// Adds a swing-closure seed: from `src`, facing `dir`, a swing starts at
    /// `start`; and the end `src`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn insert_swing_seed(
        &mut self,
        dir: Dir,
        src: End<S::Stance>,
        start: S::Nonterminal,
    )
    {
        self.insert_end(src.clone());
        self.swing_seeds.insert((dir, src, start));
    }

    /// Adds a swing-machine arc, and the end it emits at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn insert_swing_arc(
        &mut self,
        arc: SwingArc<S>,
    )
    {
        if let Some(ref end) = arc.emit {
            self.insert_end(end.clone());
        }
        self.swing_arcs.insert(arc);
    }

    /// Enables the molds projection, entered from `root_entry`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn set_root_entry(
        &mut self,
        root_entry: S::Nonterminal,
    )
    {
        self.root_entry = Some(root_entry);
    }

    /// Reports the cap on a walk's alternating length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn max_chain_len(&self) -> WalkChainLength
    {
        self.max_chain_len
    }
}

/// Whether a machine's direct rows depend on the bounds part of the swing
/// closure's seen key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SeenKeyVerdict
{
    /// Keying on the sort alone yields the same direct rows.
    Equivalent,
    /// Keying on the sort alone yields different direct rows.
    Divergent,
}

/// A refused walk, arc, machine or index.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WalkBuildError
{
    /// A swing has no nonterminals.
    EmptySwing,
    /// A walk does not alternate swing, stance, swing.
    InvalidWalkShape,
    /// A machine's cap is zero.
    ZeroMaxChainLen,
    /// An arc neither emits nor continues.
    UselessArc,
    /// A walk grew past the machine's cap.
    ChainLengthExceeded
    {
        /// The cap.
        max: WalkChainLength,
        /// The walk's alternating length.
        actual: WalkChainLength,
    },
    /// A checked conversion or count overflowed.
    ArithmeticOverflow,
}

impl From<TryFromIntError> for WalkBuildError
{
    /// Reports a failed conversion as an overflow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_overflow: TryFromIntError) -> Self
    {
        Self::ArithmeticOverflow
    }
}

impl Display for WalkBuildError
{
    /// Writes the refusal with the values it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        match *self {
            | Self::EmptySwing => f.write_str("walk swing is empty"),
            | Self::InvalidWalkShape => f.write_str("walk shape is invalid"),
            | Self::ZeroMaxChainLen => f.write_str("walk maximum chain length is zero"),
            | Self::UselessArc => f.write_str("walk swing arc neither emits nor continues"),
            | Self::ChainLengthExceeded { max, actual } => {
                write!(f, "walk chain length {actual} exceeds maximum {max}")
            },
            | Self::ArithmeticOverflow => f.write_str("walk arithmetic overflow"),
        }
    }
}

impl Error for WalkBuildError
{
}

/// A closed walk machine: every row's valid, minimal walks in canonical
/// order, the query projections, the molds projection, and the fingerprint.
#[derive(Clone)]
pub struct WalkIndex<S: WalkSym>
{
    /// The ends, ascending.
    ends: Vec<End<S::Stance>>,
    /// Left-facing direct equality walks, by query key.
    eq_rows: QueryRows<S>,
    /// Left-facing direct less walks, by query key.
    lt_rows: QueryRows<S>,
    /// Right-facing direct walks, by reversed query key.
    gt_rows: QueryRows<S>,
    /// Transitive walks, by direction and ends.
    transitive_rows: DirectRows<S>,
    /// Molded ends reachable from the root, by label.
    mold_rows: MoldRows<S>,
    /// The fingerprint.
    fingerprint: Fingerprint,
}

impl<S: WalkSym> WalkIndex<S>
{
    /// Closes a machine into its index, keying swing closure on sort and
    /// bounds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success each direct row holds the machine's direct and
    ///   generated walks for its key, and each transitive row every walk that
    ///   chains direct walks through intermediate stances without passing an
    ///   end twice; every row keeps only valid, minimal walks, one per
    ///   canonical key, in canonical order; the result, its projections and its
    ///   fingerprint are independent of insertion order.
    /// - fails: a walk grows past the cap, or a count overflows.
    /// - panics: none.
    /// - intension: both closures are iterative breadth-first searches; a swing
    ///   closure continues from a state only on the first visit of its sort and
    ///   bounds, and the outer closure never re-enters an end its path has
    ///   passed and drops a non-minimal prefix, which no extension can make
    ///   minimal again.
    ///
    /// # Errors
    /// [`WalkBuildError::ChainLengthExceeded`] past the cap,
    /// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — the paper's figure-33
    ///   fragments and section-4.1 filters, query orientation, cyclic closure,
    ///   the cap, the outer queue's pruning, duplicate and permutation
    ///   stability, converging prefixes and the molds projection each pin exact
    ///   rows; generated chains agree under permuted insertion.
    /// - witness: `tests::walk::figure_33_fragments_are_literate_external_oracle`
    /// - witness: `tests::walk::section_4_1_filters_and_canonical_order_are_observable`
    /// - witness: `tests::walk::query_orientation_filters_direct_rows`
    /// - witness: `tests::walk::transitive_queue_prunes_only_node_endpoints_not_already_seen`
    /// - witness: `tests::walk::cyclic_outer_closure_terminates_and_cap_errors_are_typed`
    /// - witness: `tests::walk::insertion_permutation_duplicate_canonicalization_and_fingerprint_are_stable`
    /// - witness: `tests::walk::converged_equality_prefixes_all_expand_through_shared_endpoint`
    /// - witness: `tests::walk::small_chain_keyings_agree_under_permuted_insertion`
    #[inline]
    pub fn build(spec: &WalkSpec<S>) -> Result<Self, WalkBuildError>
    {
        let direct = direct_rows(spec, SwingKeyMode::SortBounds)?;
        let transitive = transitive_rows(spec, &direct)?;
        let direct = filter_rows::<S>(direct)?;
        let transitive_rows = filter_rows::<S>(transitive)?;
        let eq_rows = query_rows::<S>(&direct, QueryKind::Eq)?;
        let lt_rows = query_rows::<S>(&direct, QueryKind::Lt)?;
        let gt_rows = query_rows::<S>(&direct, QueryKind::Gt)?;
        let mold_rows = mold_rows(spec, &transitive_rows);
        let fingerprint =
            fingerprint_index::<S>(spec.max_chain_len, &direct, &transitive_rows, &mold_rows)?;
        Ok(Self {
            ends: spec.ends.iter().cloned().collect(),
            eq_rows,
            lt_rows,
            gt_rows,
            transitive_rows,
            mold_rows,
            fingerprint,
        })
    }

    /// Reports whether keying swing closure on the sort alone would change
    /// a machine's direct rows.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`SeenKeyVerdict::Equivalent`] exactly when the direct rows
    ///   under the sort-only key equal those under the sort-and-bounds key
    ///   [`build`](Self::build) uses.
    /// - provides: the diagnostic that shows the bounds part of the key is
    ///   needed; the sort-only key is used nowhere else.
    /// - fails: as [`build`](Self::build), for either key.
    /// - panics: none.
    ///
    /// # Errors
    /// Any [`WalkBuildError`] either closure raises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — a machine whose alias
    ///   shares a sort but not bounds diverges, one that does not agrees, and
    ///   generated chains agree.
    /// - witness: `tests::walk::seen_key_verdicts_separate_safe_and_legacy_closure`
    /// - witness: `tests::walk::same_sort_bounds_different_identity_continuation_is_suppressed`
    /// - witness: `tests::walk::small_chain_keyings_agree_under_permuted_insertion`
    #[inline]
    pub fn compare_seen_keys(spec: &WalkSpec<S>) -> Result<SeenKeyVerdict, WalkBuildError>
    {
        let production = direct_rows(spec, SwingKeyMode::SortBounds)?;
        let sort_only = direct_rows(spec, SwingKeyMode::SortOnly)?;
        if production == sort_only {
            Ok(SeenKeyVerdict::Equivalent)
        }
        else {
            Ok(SeenKeyVerdict::Divergent)
        }
    }

    /// Borrows the transitive walks facing `dir` from `src` to `dst`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn walks(
        &self,
        dir: Dir,
        src: &End<S::Stance>,
        dst: &End<S::Stance>,
    ) -> &[Walk<S::Nonterminal, S::Stance>]
    {
        self.transitive_rows
            .get(&(dir, src.clone(), dst.clone()))
            .map_or(&[], Vec::as_slice)
    }

    /// Borrows the left-facing direct equality walks from `left` to `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn eq(
        &self,
        left: &End<S::Stance>,
        right: &End<S::Stance>,
    ) -> &[Walk<S::Nonterminal, S::Stance>]
    {
        self.eq_rows
            .get(&(left.clone(), right.clone()))
            .map_or(&[], Vec::as_slice)
    }

    /// Borrows the left-facing direct less walks from `left` to `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lt(
        &self,
        left: &End<S::Stance>,
        right: &End<S::Stance>,
    ) -> &[Walk<S::Nonterminal, S::Stance>]
    {
        self.lt_rows
            .get(&(left.clone(), right.clone()))
            .map_or(&[], Vec::as_slice)
    }

    /// Borrows the right-facing direct walks from `right` to `left`: `left`
    /// is greater than `right`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn gt(
        &self,
        left: &End<S::Stance>,
        right: &End<S::Stance>,
    ) -> &[Walk<S::Nonterminal, S::Stance>]
    {
        self.gt_rows
            .get(&(left.clone(), right.clone()))
            .map_or(&[], Vec::as_slice)
    }

    /// Borrows the molded ends with `label` that left-facing walks reach
    /// from the root, each with its mold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per distinct molded end, ascending; empty when the
    ///   machine has no root entry or the label is not reached.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — reachable ends of one label appear in
    ///   order, another label keeps its own row, and an unreached label has
    ///   none.
    /// - witness: `tests::walk::molds_projection_is_reachable_canonical_and_label_indexed`
    #[inline]
    #[must_use]
    pub fn molds(
        &self,
        label: &S::Label,
    ) -> &[(End<S::Stance>, S::Mold)]
    {
        self.mold_rows.get(label).map_or(&[], Vec::as_slice)
    }

    /// Reports the index's fingerprint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the FNV-1a hash of the frame `gandr.walk.v1`, the cap, the
    ///   direct rows, the transitive rows and the molds projection, each row in
    ///   canonical order with every symbol written as its stable key; so two
    ///   machines with the same rows have the same fingerprint, whatever their
    ///   insertion order.
    /// - provides: a cache key for tables built over the index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — permuted and repeated
    ///   insertion keep the fingerprint, on a fixture and on generated chains.
    /// - witness: `tests::walk::insertion_permutation_duplicate_canonicalization_and_fingerprint_are_stable`
    /// - witness: `tests::walk::small_chain_keyings_agree_under_permuted_insertion`
    #[inline]
    #[must_use]
    pub const fn fingerprint(&self) -> Fingerprint
    {
        self.fingerprint
    }

    /// Borrows the ends, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ends(&self) -> &[End<S::Stance>]
    {
        &self.ends
    }
}

/// Which seen key a swing closure continues by.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SwingKeyMode
{
    /// The sort and the bounds: the key [`WalkIndex::build`] uses.
    SortBounds,
    /// The sort alone: the diagnostic key.
    SortOnly,
}

/// The seen key of one swing-closure state.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SeenKey<Sort, Bounds>
{
    /// Keyed on the sort and the bounds.
    SortBounds(Sort, Bounds),
    /// Keyed on the sort alone.
    SortOnly(Sort),
}

/// Keeps each row's valid, minimal walks in canonical order and drops rows
/// left empty.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each kept row is [`canonical_walks`] of the input row, and no
///   kept row is empty.
/// - fails: as [`canonical_walks`].
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn filter_rows<S>(rows: DirectRows<S>) -> Result<DirectRows<S>, WalkBuildError>
where
    S: WalkSym,
{
    let mut filtered = BTreeMap::new();
    for (key, walks) in rows {
        let kept = canonical_walks::<S>(walks)?;
        if !kept.is_empty() {
            filtered.insert(key, kept);
        }
    }
    Ok(filtered)
}

/// Collects every direct row: the machine's direct walks and every walk its
/// swing closures emit.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each row holds, ascending and without repetition, the direct
///   walks and the closure-emitted walks for its key.
/// - fails: a walk is past the cap, or a count overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ChainLengthExceeded`] past the cap,
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn direct_rows<S>(
    spec: &WalkSpec<S>,
    mode: SwingKeyMode,
) -> Result<DirectRows<S>, WalkBuildError>
where
    S: WalkSym,
{
    let mut rows: DirectRows<S> = BTreeMap::new();
    for &(dir, ref src, ref dst, ref walk) in &spec.direct_steps {
        guard_cap(walk, spec.max_chain_len)?;
        rows.entry((dir, src.clone(), dst.clone()))
            .or_default()
            .push(walk.clone());
    }
    let mut arcs: ArcsBySource<'_, S> = BTreeMap::new();
    for arc in &spec.swing_arcs {
        arcs.entry(&arc.from).or_default().push(arc);
    }
    for &(dir, ref src, ref start) in &spec.swing_seeds {
        for (dst, walk) in swing_closure::<S>(&arcs, start, mode)? {
            guard_cap(&walk, spec.max_chain_len)?;
            rows.entry((dir, src.clone(), dst)).or_default().push(walk);
        }
    }
    for walks in rows.values_mut() {
        canonicalize(walks);
    }
    Ok(rows)
}

/// Closes the direct rows transitively through intermediate stances.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for each direction and source end, each row holds the direct
///   walks from that source and every chain of direct walks through
///   intermediate stances that never passes an end twice and stays minimal,
///   ascending and without repetition.
/// - fails: a walk is past the cap, or a count overflows.
/// - panics: none.
/// - intension: the direct rows are indexed by direction and source once, so
///   each successor lookup is logarithmic rather than a scan of every row.
///
/// # Errors
/// [`WalkBuildError::ChainLengthExceeded`] past the cap,
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn transitive_rows<S>(
    spec: &WalkSpec<S>,
    direct_rows: &DirectRows<S>,
) -> Result<DirectRows<S>, WalkBuildError>
where
    S: WalkSym,
{
    let mut by_source: RowsBySource<'_, S> = BTreeMap::new();
    for (&(dir, ref src, ref dst), walks) in direct_rows {
        by_source.entry((dir, src)).or_default().push((dst, walks));
    }
    let mut rows: DirectRows<S> = BTreeMap::new();
    for dir in [Dir::Left, Dir::Right] {
        for src in &spec.ends {
            let mut queue: VecDeque<ClosureQueueItem<S>> = VecDeque::new();
            let start = BTreeSet::from([src.clone()]);
            for &(dst, walks) in by_source.get(&(dir, src)).into_iter().flatten() {
                for walk in walks {
                    guard_cap(walk, spec.max_chain_len)?;
                    // Minimality is monotone under extension: a tile-sorted
                    // interior stance stays interior in every continuation.
                    // A non-minimal prefix can neither be kept nor extend
                    // into a minimal walk, so it is dropped here.
                    if !bool::from(minimal::<S>(walk)?) {
                        continue;
                    }
                    let mut visited = start.clone();
                    let expand = matches!(*dst, End::Node(_)) && visited.insert(dst.clone());
                    rows.entry((dir, src.clone(), dst.clone()))
                        .or_default()
                        .push(walk.clone());
                    if expand {
                        queue.push_back((dst.clone(), walk.clone(), visited));
                    }
                }
            }
            while let Some((mid, path, visited)) = queue.pop_front() {
                for &(dst, walks) in by_source.get(&(dir, &mid)).into_iter().flatten() {
                    for suffix in walks {
                        let combined = path.append_through(&mid, suffix)?;
                        guard_cap(&combined, spec.max_chain_len)?;
                        if !bool::from(minimal::<S>(&combined)?) {
                            continue;
                        }
                        let mut next_visited = visited.clone();
                        let expand =
                            matches!(*dst, End::Node(_)) && next_visited.insert(dst.clone());
                        rows.entry((dir, src.clone(), dst.clone()))
                            .or_default()
                            .push(combined.clone());
                        if expand {
                            queue.push_back((dst.clone(), combined, next_visited));
                        }
                    }
                }
            }
        }
    }
    for walks in rows.values_mut() {
        canonicalize(walks);
    }
    Ok(rows)
}

/// Refuses a walk longer than the cap.
///
/// # Specification
/// - requires: nothing.
/// - ensures: succeeds exactly when the walk's alternating length is at most
///   `max`.
/// - fails: the walk is longer than `max`, or its length overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ChainLengthExceeded`] naming both lengths,
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed length.
fn guard_cap<N, T>(
    walk: &Walk<N, T>,
    max: WalkChainLength,
) -> Result<(), WalkBuildError>
{
    let actual = walk.chain_len()?;
    if actual > max {
        return Err(WalkBuildError::ChainLengthExceeded { max, actual });
    }
    Ok(())
}

/// Runs the swing machine from one seed and returns every walk it emits,
/// with the end it emits at.
///
/// # Specification
/// - requires: `arcs` indexes every arc of one machine by its source.
/// - ensures: every walk an arc emits, from any state the closure reaches,
///   ascending and without repetition; a state continues only on the first
///   visit of its seen key under `mode`, so the closure terminates.
/// - fails: an advance yields a malformed walk, or a count overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::InvalidWalkShape`] for a malformed walk,
/// [`WalkBuildError::EmptySwing`] never in practice, and
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn swing_closure<S>(
    arcs: &ArcsBySource<'_, S>,
    start: &S::Nonterminal,
    mode: SwingKeyMode,
) -> Result<SwingClosureOutput<S>, WalkBuildError>
where
    S: WalkSym,
{
    let initial = PartialWalk {
        current: start.clone(),
        swings: vec![Swing::new(vec![start.clone()])?],
        stances: Vec::new(),
    };
    let mut queue = VecDeque::from([initial]);
    let mut seen = BTreeSet::new();
    let mut output = Vec::new();
    while let Some(partial) = queue.pop_front() {
        let first_visit = seen.insert(seen_key::<S>(&partial.current, mode));
        for arc in arcs.get(&partial.current).into_iter().flatten() {
            let next = partial.apply(&arc.advance)?;
            if let Some(ref dst) = arc.emit {
                let walk = Walk::new(next.swings.clone(), next.stances.clone())?;
                output.push((dst.clone(), walk));
            }
            if first_visit && let Some(ref continue_from) = arc.continue_from {
                queue.push_back(next.with_current(continue_from.clone()));
            }
        }
    }
    canonicalize(&mut output);
    Ok(output)
}

/// Keeps the valid, minimal walks of one row, one per canonical key, in
/// canonical order.
///
/// # Specification
/// - requires: `walks` ascend by the walk order, as every closure's rows do.
/// - ensures: keeps a walk exactly when it has the equality or the inequality
///   shape and is minimal; of walks sharing a canonical key, keeps the first,
///   which is the least by the walk order; the result ascends by canonical key.
/// - fails: a count overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn canonical_walks<S>(walks: Vec<MachineWalk<S>>) -> Result<Vec<MachineWalk<S>>, WalkBuildError>
where
    S: WalkSym,
{
    let mut kept = BTreeMap::new();
    for walk in walks {
        let shaped = bool::from(walk.is_eq()?) || bool::from(walk.is_neq()?);
        if shaped && bool::from(minimal::<S>(&walk)?) {
            let key = canonical_walk_key::<S>(&walk)?;
            kept.entry(key).or_insert(walk);
        }
    }
    Ok(kept.into_values().collect())
}

/// Reports whether a walk survives the minimality filter: an equality walk
/// always does; any other walk does unless a tile-sorted stance sits strictly
/// inside its rising swings.
///
/// # Specification
/// - requires: nothing.
/// - ensures: true for an equality walk; otherwise false exactly when some
///   stance follows at least one rising swing, precedes the last, and is
///   tile-sorted.
/// - fails: a count overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn minimal<S>(walk: &MachineWalk<S>) -> Result<WalkMinimal, WalkBuildError>
where
    S: WalkSym,
{
    if bool::from(walk.is_eq()?) {
        return Ok(WalkMinimal::from(true));
    }
    let height = walk.height()?;
    let mut rising = 0_u32;
    let mut stances = walk.stances.iter();
    for swing in &walk.swings {
        if swing.height()? != SwingHeight::default() {
            rising = rising
                .checked_add(1)
                .ok_or(WalkBuildError::ArithmeticOverflow)?;
        }
        if let Some(stance) = stances.next()
            && rising > 0
            && WalkHeight::from(rising) < height
            && bool::from(S::stance_tile_sorted(stance))
        {
            return Ok(WalkMinimal::from(false));
        }
    }
    Ok(WalkMinimal::from(true))
}

/// Projects the molded ends that left-facing walks reach from the root.
///
/// # Specification
/// - requires: `transitive_rows` holds only non-empty rows.
/// - ensures: when the machine has a root entry, each label maps to every
///   molded end with that label some left-facing root row reaches, with its
///   mold, ascending and without repetition; otherwise empty.
/// - panics: none.
fn mold_rows<S>(
    spec: &WalkSpec<S>,
    transitive_rows: &DirectRows<S>,
) -> MoldRows<S>
where
    S: WalkSym,
{
    let mut rows: MoldRows<S> = BTreeMap::new();
    if spec.root_entry.is_none() {
        return rows;
    }
    for &(dir, ref src, ref dst) in transitive_rows.keys() {
        if dir == Dir::Left
            && *src == End::Root
            && let End::Node(ref stance) = *dst
            && let Some((label, mold)) = S::label_mold(stance)
        {
            rows.entry(label).or_default().push((dst.clone(), mold));
        }
    }
    for row in rows.values_mut() {
        canonicalize(row);
    }
    rows
}

/// Sorts and deduplicates in place.
///
/// # Specification
/// trivial.
fn canonicalize<T>(values: &mut Vec<T>)
where
    T: Ord,
{
    values.sort();
    values.dedup();
}

/// Which query a projection answers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum QueryKind
{
    /// Left-facing equality.
    Eq,
    /// Left-facing less.
    Lt,
    /// Right-facing, reversed.
    Gt,
}

/// Projects the direct rows a query reads.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`QueryKind::Eq`] keeps left-facing equality walks and
///   [`QueryKind::Lt`] left-facing inequality walks under `(src, dst)`;
///   [`QueryKind::Gt`] keeps right-facing inequality walks under `(dst, src)`.
/// - fails: a count overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn query_rows<S>(
    direct_rows: &DirectRows<S>,
    kind: QueryKind,
) -> Result<QueryRows<S>, WalkBuildError>
where
    S: WalkSym,
{
    let mut rows: QueryRows<S> = BTreeMap::new();
    for (&(dir, ref src, ref dst), walks) in direct_rows {
        for walk in walks {
            let keep = match kind {
                | QueryKind::Eq => dir == Dir::Left && bool::from(walk.is_eq()?),
                | QueryKind::Lt => dir == Dir::Left && bool::from(walk.is_neq()?),
                | QueryKind::Gt => dir == Dir::Right && bool::from(walk.is_neq()?),
            };
            if keep {
                let key = match kind {
                    | QueryKind::Gt => (dst.clone(), src.clone()),
                    | QueryKind::Eq | QueryKind::Lt => (src.clone(), dst.clone()),
                };
                rows.entry(key).or_default().push(walk.clone());
            }
        }
    }
    Ok(rows)
}

/// A swing closure's walk in progress.
#[derive(Clone, Debug, Eq, PartialEq)]
struct PartialWalk<N, T>
{
    /// The machine state the next arcs leave.
    current: N,
    /// The swings so far.
    swings: Vec<Swing<N>>,
    /// The stances so far.
    stances: Vec<T>,
}

impl<N: Clone, T: Clone> PartialWalk<N, T>
{
    /// Applies one advance.
    ///
    /// # Specification
    /// - requires: the walk has at least one swing.
    /// - ensures: [`SwingAdvance::Stay`] keeps the walk; `Extend(next)` appends
    ///   `next` to the last swing and moves to it; `Cross` appends the stance
    ///   and a new swing at `next` and moves to it.
    /// - fails: there is no swing to extend.
    /// - panics: none.
    ///
    /// # Errors
    /// [`WalkBuildError::InvalidWalkShape`] for a walk without swings.
    fn apply(
        &self,
        advance: &SwingAdvance<N, T>,
    ) -> Result<Self, WalkBuildError>
    {
        let mut next = self.clone();
        match *advance {
            | SwingAdvance::Stay => {},
            | SwingAdvance::Extend(ref nonterminal) => {
                let last = next
                    .swings
                    .last_mut()
                    .ok_or(WalkBuildError::InvalidWalkShape)?;
                last.nonterminals.push(nonterminal.clone());
                next.current = nonterminal.clone();
            },
            | SwingAdvance::Cross {
                ref stance,
                next: ref nonterminal,
            } => {
                let swing = Swing::new(vec![nonterminal.clone()])?;
                next.swings.push(swing);
                next.stances.push(stance.clone());
                next.current = nonterminal.clone();
            },
        }
        Ok(next)
    }

    /// Moves the walk to another machine state.
    ///
    /// # Specification
    /// trivial.
    fn with_current(
        mut self,
        current: N,
    ) -> Self
    {
        self.current = current;
        self
    }
}

/// Computes a state's seen key under a mode.
///
/// # Specification
/// trivial.
fn seen_key<S>(
    nonterminal: &S::Nonterminal,
    mode: SwingKeyMode,
) -> SeenKey<S::Sort, S::Bounds>
where
    S: WalkSym,
{
    match mode {
        | SwingKeyMode::SortBounds => SeenKey::SortBounds(
            S::nonterminal_sort(nonterminal),
            S::nonterminal_bounds(nonterminal),
        ),
        | SwingKeyMode::SortOnly => SeenKey::SortOnly(S::nonterminal_sort(nonterminal)),
    }
}

/// The canonical-order key of one walk, compared field by field in
/// declaration order.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CanonicalWalkKey<N: Ord, T: Ord, Sort: Ord>
{
    /// How many swings rise.
    height: WalkHeight,
    /// The sort of the first stance before any swing rises.
    top: Option<Sort>,
    /// The sorts of the stances strictly inside the rising swings.
    mids: Vec<Sort>,
    /// The sort of the first stance after the last swing rises.
    bottom: Option<Sort>,
    /// The alternating length.
    chain_len: WalkChainLength,
    /// The swings, destination first, each destination first.
    fallback_swings: Vec<FallbackSwing<N>>,
    /// The stances, destination first.
    fallback_stances: Vec<T>,
}

/// One swing in the destination-first fallback of the canonical key.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FallbackSwing<N: Ord>
{
    /// The swing's height.
    height: SwingHeight,
    /// The swing's nonterminals, destination first.
    nonterminals: Vec<N>,
}

/// Computes a walk's canonical-order key.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the key orders walks by rising-swing count, then the top stance
///   sort, the interior stance sorts, the bottom stance sort, the alternating
///   length, and finally the swings and stances read from the destination.
/// - fails: a count overflows.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for an overflowed count.
fn canonical_walk_key<S>(walk: &MachineWalk<S>) -> Result<WalkSortKey<S>, WalkBuildError>
where
    S: WalkSym,
{
    let height = walk.height()?;
    let mut rising = 0_u32;
    let mut top = None;
    let mut mids = Vec::new();
    let mut bottom = None;
    let mut stances = walk.stances.iter();
    for swing in &walk.swings {
        if swing.height()? != SwingHeight::default() {
            rising = rising
                .checked_add(1)
                .ok_or(WalkBuildError::ArithmeticOverflow)?;
        }
        if let Some(stance) = stances.next() {
            let sort = S::stance_sort(stance);
            if rising == 0 && top.is_none() {
                top = Some(sort);
            }
            else if WalkHeight::from(rising) < height {
                mids.push(sort);
            }
            else if WalkHeight::from(rising) == height && bottom.is_none() {
                bottom = Some(sort);
            }
        }
    }
    let mut fallback_swings = Vec::with_capacity(walk.swings.len());
    for swing in walk.swings.iter().rev() {
        fallback_swings.push(FallbackSwing {
            height: swing.height()?,
            nonterminals: swing.nonterminals.iter().rev().cloned().collect(),
        });
    }
    Ok(CanonicalWalkKey {
        height,
        top,
        mids,
        bottom,
        chain_len: walk.chain_len()?,
        fallback_swings,
        fallback_stances: walk.stances.iter().rev().cloned().collect(),
    })
}

/// Fingerprints a closed index.
///
/// # Specification
/// - requires: the rows are canonical.
/// - ensures: the hash of the frame `gandr.walk.v1` and the cap as a 32-bit
///   word, the direct rows under tag `D`, the transitive rows under tag `T`,
///   then tag `M` and per label, in label order, tag `L`, the label's ordinal,
///   the row length and each end with its ordinal.
/// - fails: a count exceeds `u32`.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for a count past `u32`.
fn fingerprint_index<S>(
    max_chain_len: WalkChainLength,
    direct_rows: &DirectRows<S>,
    transitive_rows: &DirectRows<S>,
    mold_rows: &MoldRows<S>,
) -> Result<Fingerprint, WalkBuildError>
where
    S: WalkSym,
{
    let mut hash = Fnv64::new();
    hash.write_bytes(b"gandr.walk.v1");
    hash.write_u32(u32::from(max_chain_len));
    hash_walk_rows::<S>(&mut hash, FingerprintByte::from(b'D'), direct_rows)?;
    hash_walk_rows::<S>(&mut hash, FingerprintByte::from(b'T'), transitive_rows)?;
    hash.write_byte(b'M');
    for (label_ordinal, row) in (0_u64 ..).zip(mold_rows.values()) {
        hash.write_byte(b'L');
        hash.write_u64(label_ordinal);
        hash.write_u32(u32::try_from(row.len())?);
        for (mold_ordinal, entry) in (0_u64 ..).zip(row) {
            hash_end::<S>(&mut hash, &entry.0);
            hash.write_u64(mold_ordinal);
        }
    }
    Ok(hash.finish())
}

/// Absorbs one table of rows under its tag.
///
/// # Specification
/// - requires: the rows are canonical.
/// - ensures: absorbs the tag, the row count, and per row its direction (`L` or
///   `R`), both ends, its walk count and each walk.
/// - fails: a count exceeds `u32`.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for a count past `u32`.
fn hash_walk_rows<S>(
    hash: &mut Fnv64,
    tag: FingerprintByte,
    rows: &DirectRows<S>,
) -> Result<(), WalkBuildError>
where
    S: WalkSym,
{
    hash.write_byte(tag);
    hash.write_u32(u32::try_from(rows.len())?);
    for (&(dir, ref src, ref dst), walks) in rows {
        hash.write_byte(match dir {
            | Dir::Left => b'L',
            | Dir::Right => b'R',
        });
        hash_end::<S>(hash, src);
        hash_end::<S>(hash, dst);
        hash.write_u32(u32::try_from(walks.len())?);
        for walk in walks {
            hash_walk::<S>(hash, walk)?;
        }
    }
    Ok(())
}

/// Absorbs one end: `0` for the root, `1` and the stance's key otherwise.
///
/// # Specification
/// trivial.
fn hash_end<S>(
    hash: &mut Fnv64,
    end: &End<S::Stance>,
) where
    S: WalkSym,
{
    match *end {
        | End::Root => hash.write_byte(0_u8),
        | End::Node(ref stance) => {
            hash.write_byte(1_u8);
            hash.write_u64(S::stance_key(stance));
        },
    }
}

/// Absorbs one walk: its alternating length, its swings with their heights
/// and nonterminal keys, and its stance keys.
///
/// # Specification
/// - requires: nothing.
/// - ensures: absorbs the alternating length, the swing count, per swing its
///   height, length and nonterminal keys, then the stance count and stance
///   keys, every count a 32-bit word.
/// - fails: a count exceeds `u32`.
/// - panics: none.
///
/// # Errors
/// [`WalkBuildError::ArithmeticOverflow`] for a count past `u32`.
fn hash_walk<S>(
    hash: &mut Fnv64,
    walk: &MachineWalk<S>,
) -> Result<(), WalkBuildError>
where
    S: WalkSym,
{
    hash.write_u32(u32::from(walk.chain_len()?));
    hash.write_u32(u32::try_from(walk.swings.len())?);
    for swing in &walk.swings {
        hash.write_u32(u32::from(swing.height()?));
        hash.write_u32(u32::try_from(swing.nonterminals.len())?);
        for nonterminal in &swing.nonterminals {
            hash.write_u64(S::nonterminal_key(nonterminal));
        }
    }
    hash.write_u32(u32::try_from(walk.stances.len())?);
    for stance in &walk.stances {
        hash.write_u64(S::stance_key(stance));
    }
    Ok(())
}
