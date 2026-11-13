//! **The releases of an environment** whose commits the cursor has not read
//! yet.
//!
//! A release reserves the next position of the entries and the rank of its
//! declaration. Its check runs apart from the environment. Its commit fills
//! the reserved slot in any order that the dependences allow, and a later
//! check reads the commit as soon as it comes.
//!
//! Some state reads the order of every commit: the rows of the dependents,
//! the order flag, the chain key and the records of the verdicts. The cursor
//! folds that state. It reads the slots in position order, and it stops at the
//! first slot that waits for its commit. So the folded state is the state of
//! the serial run, in each order that the commits come in.
//!
//! A release that reads an earlier commit before that commit comes holds
//! ([`Hold`]). The environment hands its declaration back, and the caller
//! settles each outstanding check before it releases the declaration again.
//!
//! With `speculation.rank` on ([`crate::speculation`]), a release with no
//! rank goes ahead where the rank would hold. It takes the rank past each
//! reservation, as if each outstanding release admits ([`Ranked::Predicted`]).
//! The fold checks the rank at the cursor, and moves the entry to the rank of
//! the serial run when an earlier release was refused. A check reads a rank
//! only as an order among the live entries, and the move keeps that order,
//! so no check runs again.
//!
//! # References
//!
//! - gandr #3476 — the parallel replay, § "Where the next landing starts": the
//!   reserved slot and rank, the commit in dependence order, the cursor in
//!   position order, and each read of order that holds a release; and the plan
//!   of the optimistic landing, whose first part predicts the rank.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::SourceRank;
use quenchant_shape::shape::Maybe;

use crate::encoding::ConstantName;
use crate::env::UnsettledCount;
use crate::environment::Hold;
use crate::verdict::VerdictKey;
use crate::verdict::keyed;

/// How a release finds its chain key.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub enum Chained
{
    /// The cursor stood at the release, so the release took the chain key.
    Taken(Maybe<VerdictKey, keyed::Absent>),
    /// The cursor stood behind the release, so the fold takes the chain key.
    Deferred,
}

/// Whether a declaration holds each release after it until its commit.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sway
{
    /// An abstract type, a presented type or a role holder. Each check after
    /// it reads it, named or not.
    Ordering,
    /// No later check reads it unless the check names it.
    Free,
}

/// How a release took its rank.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Ranked
{
    /// The rank of the serial run: the rank staged, or the rank past every
    /// live entry when no outstanding release reads into it.
    Serial,
    /// The rank past each outstanding reservation, as if each outstanding
    /// release admits. The fold checks it at the cursor.
    Predicted,
}

/// What a later release reads of an outstanding release before its commit.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Reservation
{
    /// The rank of the declaration.
    rank: SourceRank,
    /// Whether the declaration holds each release after it.
    sway: Sway,
    /// The content key of a generative declaration, which the entry key of a
    /// later one with the same content counts.
    generative: Maybe<VerdictKey, generative::Absent>,
    /// The name of the declaration. The name of a later plain definition
    /// with the same content counts a plain definition.
    name: ConstantName,
}

quenchant_shape::reason_enum! {
    /// Why a reservation carries no generative content.
    pub mod generative {
        /// The reason no content is carried.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The declaration is a definition or a literal identity, whose
            /// content no later entry key counts.
            Plain,
            /// The declaration has no content key.
            Unkeyed,
        }
    }
}

impl Reservation
{
    /// The reservation of a declaration at `rank` with `sway`, its generative
    /// content and its name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn new(
        rank: SourceRank,
        sway: Sway,
        generative: Maybe<VerdictKey, generative::Absent>,
        name: ConstantName,
    ) -> Self
    {
        Self {
            rank,
            sway,
            generative,
            name,
        }
    }
}

/// What the slot at one position from the cursor on holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub enum Unfolded
{
    /// A release whose commit has not come.
    Reserved(Reservation),
    /// An admission, how it finds its chain key, and the reading that a
    /// record of its verdict keeps when the record is due.
    Admitted(Chained, Option<crate::check::Accessibility>),
    /// A refusal, and how it found its chain key.
    Vacated(Chained),
}

quenchant_shape::reason_enum! {
    /// Why the cursor reads no slot.
    pub mod cursor {
        /// The reason no slot is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every slot below the length is folded.
            Folded,
            /// The slot at the cursor waits for its commit.
            Waiting,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a commit finds no reservation at its position.
    pub mod reserved {
        /// The reason no reservation is found.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The cursor passed the position, or the position is past the
            /// last slot.
            Outside,
            /// The slot at the position holds its commit.
            Committed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a release needs no earlier commit.
    pub mod free {
        /// The reason the release goes ahead.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No outstanding release reads into it.
            Unread,
            /// It goes ahead on a prediction of what it reads, which the fold
            /// checks.
            Predicted,
        }
    }
}

/// The releases whose commits the cursor has not read, and what each
/// outstanding release holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
pub struct Releases
{
    /// The slot at each position from the cursor on, in position order, with
    /// how its release took its rank. The front is reserved whenever the
    /// queue holds a slot.
    unfolded: VecDeque<(Ranked, Unfolded)>,
    /// How many outstanding releases there are.
    outstanding: usize,
    /// How many outstanding releases hold each release after them.
    ordering: usize,
    /// The ranks that the outstanding releases reserve, with their positions.
    ranks: BTreeMap<SourceRank, ConstantIndex>,
    /// The ranks of the outstanding generative declarations, by content key.
    generative: BTreeMap<VerdictKey, Vec<SourceRank>>,
    /// The ranks and names of the outstanding plain definitions, by digest.
    definitions: BTreeMap<ContentDigest, Vec<(SourceRank, ConstantName)>>,
    /// How many slots from the cursor on hold a predicted rank.
    predicting: usize,
}

impl Releases
{
    /// How many releases are outstanding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn outstanding(&self) -> UnsettledCount
    {
        UnsettledCount::from(self.outstanding)
    }

    /// How many slots below the length the cursor has not folded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn unfolded(&self) -> gandr_kernel_term::ArenaLength
    {
        gandr_kernel_term::ArenaLength::from(self.unfolded.len())
    }

    /// Reserve the slot past every slot for the release of a declaration,
    /// which took its rank as `ranked` states.
    ///
    /// # Specification
    /// - requires: `position` is the position past every slot of the entries.
    /// - ensures: one more outstanding release, at the back of the queue, and
    ///   each index holds what `reservation` states.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::environment::Environment::release`].
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[spec(captures: [queued = self.unfolded.len(), outstanding = self.outstanding],
        ensures: self.unfolded.len() == queued.saturating_add(1)
            && self.outstanding == outstanding.saturating_add(1))]
    pub fn reserve(
        &mut self,
        position: ConstantIndex,
        reservation: Reservation,
        ranked: Ranked,
    )
    {
        self.outstanding = self.outstanding.saturating_add(1);
        if reservation.sway == Sway::Ordering {
            self.ordering = self.ordering.saturating_add(1);
        }
        let _previous = self.ranks.insert(reservation.rank, position);
        if let Maybe::Present(content) = reservation.generative {
            self.generative
                .entry(content)
                .or_default()
                .push(reservation.rank);
        }
        if let ConstantName::Definition { digest, .. } = reservation.name {
            self.definitions
                .entry(digest)
                .or_default()
                .push((reservation.rank, reservation.name));
        }
        if ranked == Ranked::Predicted {
            self.predicting = self.predicting.saturating_add(1);
        }
        self.unfolded
            .push_back((ranked, Unfolded::Reserved(reservation)));
    }

    /// Note the refusal of a release at the position past every slot, made
    /// before its check while earlier releases are outstanding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn vacate(&mut self)
    {
        self.unfolded
            .push_back((Ranked::Serial, Unfolded::Vacated(Chained::Deferred)));
    }

    /// Fill the reserved slot at `offset` from the cursor with its commit, and
    /// answer what it reserved.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on a reservation at `offset`, its slot holds `commit`, one
    ///   release less is outstanding, and no index holds the reservation.
    ///   Nothing changes otherwise.
    /// - provides: the reservation, or why `offset` holds none
    ///   ([`reserved::Absent`]).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`crate::environment::Environment::settle`].
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[spec(captures: outstanding = self.outstanding, ensures: |ret| match ret {
        Maybe::Present(_) => self.outstanding.saturating_add(1) == outstanding,
        Maybe::Absent(_) => self.outstanding == outstanding,
    })]
    pub fn commit(
        &mut self,
        offset: gandr_kernel_term::ArenaLength,
        commit: Unfolded,
    ) -> Maybe<Reservation, reserved::Absent>
    {
        let Some(&mut (_, ref mut slot)) = self.unfolded.get_mut(usize::from(offset))
        else {
            return Maybe::Absent(reserved::Absent::Outside);
        };
        if !matches!(*slot, Unfolded::Reserved(_)) {
            return Maybe::Absent(reserved::Absent::Committed);
        }
        let Unfolded::Reserved(reservation) = core::mem::replace(slot, commit)
        else {
            return Maybe::Absent(reserved::Absent::Committed);
        };
        self.outstanding = self.outstanding.saturating_sub(1);
        if reservation.sway == Sway::Ordering {
            self.ordering = self.ordering.saturating_sub(1);
        }
        let _freed = self.ranks.remove(&reservation.rank);
        if let Maybe::Present(content) = reservation.generative
            && let Some(ranks) = self.generative.get_mut(&content)
        {
            ranks.retain(|&held| held != reservation.rank);
            if ranks.is_empty() {
                let _emptied = self.generative.remove(&content);
            }
        }
        if let ConstantName::Definition { digest, .. } = reservation.name
            && let Some(names) = self.definitions.get_mut(&digest)
        {
            names.retain(|&(held, _)| held != reservation.rank);
            if names.is_empty() {
                let _emptied = self.definitions.remove(&digest);
            }
        }
        Maybe::Present(reservation)
    }

    /// Take the slot at the cursor once its commit came, so the cursor passes
    /// it, with how its release took its rank.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on a slot that holds its commit, one slot less in the queue;
    ///   nothing changes otherwise.
    /// - provides: the slot, or why the cursor reads none ([`cursor::Absent`]).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cursor that passes a reserved slot folds a later
    ///   commit before an earlier one, and the folded state of the serial run
    ///   differs.
    /// - witness: `environment::tests::each_commit_order_of_a_released_source_folds_as_the_serial_run_3476`
    #[spec(captures: queued = self.unfolded.len(), ensures: |ret| match ret {
        Maybe::Present(_) => self.unfolded.len().saturating_add(1) == queued,
        Maybe::Absent(_) => self.unfolded.len() == queued,
    })]
    pub fn next(&mut self) -> Maybe<(Ranked, Unfolded), cursor::Absent>
    {
        match self.unfolded.front() {
            None => Maybe::Absent(cursor::Absent::Folded),
            Some(&(_, Unfolded::Reserved(_))) => Maybe::Absent(cursor::Absent::Waiting),
            Some(&(_, Unfolded::Admitted(..) | Unfolded::Vacated(_))) => {
                let Some(slot) = self.unfolded.pop_front()
                else {
                    return Maybe::Absent(cursor::Absent::Folded);
                };
                if slot.0 == Ranked::Predicted {
                    self.predicting = self.predicting.saturating_sub(1);
                }
                Maybe::Present(slot)
            },
        }
    }

    /// Why a release that reads order of its own, as `sway` states, holds:
    /// when it or an outstanding release holds each release after it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn ordering(
        &self,
        sway: Sway,
    ) -> Maybe<Hold, free::Absent>
    {
        if sway == Sway::Ordering || self.ordering != 0 {
            return Maybe::Present(Hold::Ordering);
        }
        Maybe::Absent(free::Absent::Unread)
    }

    /// Why a release at `rank`, or at the rank past every rank when it
    /// carries none, holds: an outstanding release reserves its rank, or the
    /// rank past every rank reads one. `committed` is the rank past every
    /// rank that a live entry holds, and `speculating` is the setting of the
    /// rank: on, a release with no rank goes ahead on its prediction where
    /// it would hold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn rank(
        &self,
        rank: Maybe<SourceRank, crate::environment::unranked::Absent>,
        committed: SourceRank,
        speculating: crate::speculation::Setting,
    ) -> Maybe<Hold, free::Absent>
    {
        let read = match rank {
            // A staged rank reads a reservation of it. While a predicted rank
            // is unfolded, the rank of a live entry may move at the fold, so
            // a staged rank holds until no prediction is unfolded.
            Maybe::Present(rank) => self.ranks.contains_key(&rank) || self.predicting != 0,
            // The rank past every rank reads an outstanding release when it
            // reserves a rank past the ones that live entries hold: the
            // release's refusal moves the rank past every rank. It reads an
            // unfolded prediction too, which `committed` may hold.
            Maybe::Absent(crate::environment::unranked::Absent::Unranked) => {
                let read = self.predicting != 0
                    || self.ranks.last_key_value().is_some_and(|(&top, _)| {
                        usize::from(top).saturating_add(1) >= usize::from(committed)
                    });
                if read && speculating == crate::speculation::Setting::On {
                    return Maybe::Absent(free::Absent::Predicted);
                }
                read
            },
        };
        if read {
            return Maybe::Present(Hold::Rank);
        }
        Maybe::Absent(free::Absent::Unread)
    }

    /// The rank past every rank that an outstanding release reserves, or `past`
    /// when it is higher.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn past(
        &self,
        past: SourceRank,
    ) -> SourceRank
    {
        self.ranks.last_key_value().map_or(past, |(&top, _)| {
            past.max(SourceRank::from(usize::from(top).saturating_add(1)))
        })
    }

    /// Why the release of a generative declaration with the content key
    /// `content` at `rank` holds: an outstanding generative release ranked
    /// below it carries the same content, which its entry key counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn generative(
        &self,
        content: VerdictKey,
        rank: SourceRank,
    ) -> Maybe<Hold, free::Absent>
    {
        if self
            .generative
            .get(&content)
            .is_some_and(|ranks| ranks.iter().any(|&held| held < rank))
        {
            return Maybe::Present(Hold::Content);
        }
        Maybe::Absent(free::Absent::Unread)
    }

    /// The names of the outstanding plain definitions ranked below `rank`
    /// whose content digests to `digest`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn definitions(
        &self,
        digest: ContentDigest,
        rank: SourceRank,
    ) -> impl Iterator<Item = ConstantName> + '_
    {
        self.definitions
            .get(&digest)
            .into_iter()
            .flatten()
            .filter(move |&&(held, _)| held < rank)
            .map(|&(_, name)| name)
    }
}
