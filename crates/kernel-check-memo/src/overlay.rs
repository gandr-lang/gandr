//! The overlay of a memo at a fork point.
//!
//! A job that runs apart from its parent, a check on a worker or an obligation
//! that a check forks, reads the memo as it stood at the fork and records
//! into its own entries. A fork freezes the memo it opens on, so each child
//! reads the frozen layers by reference and copies none of them. A join folds
//! the entries of each child into the parent, in the order of the children.
//! So the joined memo holds what a serial run holds that recorded the children
//! in that order. Two children that answer one support with two outcomes do
//! not glue, and the join refuses them with both outcomes named. A settle
//! merges a frozen layer that no child reads any more back into its owner, so
//! the layers do not grow with the forks.
//!
//! The layers are a flat stack, oldest first, and no layer points at another:
//! a drop and a walk of the stack are loops.
//!
//! An entry folds unchanged: a key names its content and no position of a
//! table, so a key means one thing in the child and in the parent.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the session at a
//!   job's release with an overlay of its own, folded at the commit in
//!   dependence order (§ kernel-reassessment-design item 10).
//! - `vault:01a178aa-56f5-7082-acef-f7c1b85fc0a2` — anchor: the bracket's
//!   support is exactly the nontrivial overlaps, so a join checks agreement on
//!   the supports that two children both keep (§ The bracket oracle).
//! - `vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa` — anchor: the memo glues by
//!   agreement on its keys, which the join computes and never asserts (§
//!   sharing-rule-descent).

use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;

use crate::accounting::MemoEntryCount;
use crate::accounting::MemoError;
use crate::digest::ContentDigest;
use crate::key::MemoKey;
use crate::memo::CheckMemo;
use crate::memo::HashedMemo;
use crate::memo::MemoActivity;
use crate::memo::MemoHit;
use crate::memo::MemoRecord;

/// A memo over the layers frozen at the fork points that opened it.
///
/// # Specification
/// - requires: supports obey the consumer laws of [`MemoKey`], and a support
///   names content alone, so an entry means one thing in every layer.
/// - ensures: a recall serves the newest agreeing entry: the memo's own first,
///   then each frozen layer, newest first. A record writes the memo's own
///   entries and no frozen layer.
/// - provides: the memo a forked job reads by reference and records apart.
/// - panics: none.
/// - executable: none — a data declaration; its operations carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — two children forked at one point, each recording an entry
///   the other records, joined in either order, against a serial memo that
///   records the same entries in that order.
/// - witness: `overlay::tests::a_join_folds_the_children_in_their_order_as_a_serial_memo_records_them`
/// - witness: `overlay::tests::a_child_reads_the_memo_as_it_stood_at_the_fork`
#[derive(Clone)]
pub struct OverlaidMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// The layers frozen at the fork points below this memo, oldest first.
    layers: Vec<Arc<HashedMemo<Support, Outcome>>>,
    /// The entries recorded since the newest fork point.
    own: HashedMemo<Support, Outcome>,
}

impl<Support, Outcome> core::fmt::Debug for OverlaidMemo<Support, Outcome>
where
    Support: MemoKey,
    HashedMemo<Support, Outcome>: core::fmt::Debug,
{
    /// The memo's frozen layers and its own entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("OverlaidMemo")
            .field("layers", &self.layers)
            .field("own", &self.own)
            .finish()
    }
}

impl<Support, Outcome> Default for OverlaidMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// A memo of its own, holding nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

/// Two outcomes that a join meets under one support: the outcome that the
/// memo recorded since the child's fork, and the outcome that the child
/// offers. The two do not glue, so the join refuses them.
///
/// # Specification
/// - requires: made by [`OverlaidMemo::join`].
/// - ensures: the support, and the two outcomes that differ under it.
/// - panics: none.
/// - executable: none — the fields are private and set only by the join.
///
/// # Adequacy
/// - hypothesis: L3 — as [`OverlaidMemo::join`].
/// - witness: `overlay::tests::a_join_refuses_two_outcomes_under_one_key_and_names_both`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Disagreement<Support, Outcome>
{
    /// The support that both outcomes answer.
    support: Support,
    /// The outcome that the memo recorded since the child's fork.
    held: Outcome,
    /// The outcome that the child offers.
    offered: Outcome,
}

impl<Support, Outcome> Disagreement<Support, Outcome>
{
    /// The support that both outcomes answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn support(&self) -> &Support
    {
        &self.support
    }

    /// The outcome that the memo recorded since the child's fork.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn held(&self) -> &Outcome
    {
        &self.held
    }

    /// The outcome that the child offers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn offered(&self) -> &Outcome
    {
        &self.offered
    }

    /// The support, the held outcome and the offered outcome, by value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (Support, Outcome, Outcome)
    {
        (self.support, self.held, self.offered)
    }
}

impl<Support, Outcome> OverlaidMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// A memo of its own, holding nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            layers: Vec::new(),
            own: HashedMemo::new(),
        }
    }

    /// Open a child at this fork point: a memo that reads this one as it
    /// stands, by reference, and records apart.
    ///
    /// This memo freezes its own entries into a new layer, when it holds any,
    /// and records into fresh entries above it. So each sibling of one fork
    /// point reads the same layers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the child and this memo serve each support as this memo
    ///   served it before the call; neither holds an entry of its own.
    /// - provides: the memo a forked job reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OverlaidMemo`].
    /// - witness: `overlay::tests::a_child_reads_the_memo_as_it_stood_at_the_fork`
    #[spec(ensures: |ret| ret.own.entry_count() == MemoEntryCount::zero()
        && self.own.entry_count() == MemoEntryCount::zero())]
    #[must_use]
    #[inline]
    pub fn fork(&mut self) -> Self
    {
        if self.own.entry_count() != MemoEntryCount::zero() {
            let frozen = core::mem::take(&mut self.own);
            self.layers.push(Arc::new(frozen));
        }
        Self {
            layers: self.layers.clone(),
            own: HashedMemo::new(),
        }
    }

    /// Fold `child`'s own entries into this memo, in the order the child
    /// recorded them, keeping each entry that `keep` answers for, when each
    /// agrees with what this memo recorded since the child's fork.
    ///
    /// The entries recorded since the fork are this memo's own entries and
    /// the entries of each layer frozen after the child's newest one: the
    /// joins of earlier siblings, which the child did not read. Two entries
    /// under one support with two outcomes do not glue. So the join refuses
    /// them, names both, and folds nothing. A child replaces an entry of a
    /// layer that it read, as a serial run that records it again replaces
    /// it. The join first settles this memo, so a serial fold records each
    /// entry once.
    ///
    /// # Specification
    /// - requires: `child` was forked from this memo or from a layer below it.
    /// - ensures: on success, each kept entry of the child is recorded into
    ///   this memo's own entries, as [`CheckMemo::remember`] records it; the
    ///   child's hold on its frozen layers ends, and this memo is settled as
    ///   [`Self::settle`] settles it. On a refusal, this memo serves each
    ///   support as it served it before the call.
    /// - provides: the fold of a job's memo at its join or its commit, and the
    ///   agreement check of two jobs that keep one support.
    /// - fails: a kept entry of the child and an entry recorded since its fork
    ///   answer one support with two outcomes.
    /// - panics: none.
    /// - executable: none — the fold's order is the caller's, and the child's
    ///   entries leave with the call, so no predicate reads them after it.
    ///
    /// # Errors
    /// [`Disagreement`], naming the support, the outcome that this memo holds
    /// and the outcome that the child offers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OverlaidMemo`]; an entry that `keep` drops is
    ///   not served after the join, and two siblings that keep two outcomes
    ///   under one support are refused in either order.
    /// - witness: `overlay::tests::a_join_folds_the_children_in_their_order_as_a_serial_memo_records_them`
    /// - witness: `overlay::tests::a_join_drops_what_the_parent_does_not_keep`
    /// - witness: `overlay::tests::a_join_refuses_two_outcomes_under_one_key_and_names_both`
    #[inline]
    pub fn join<Keep>(
        &mut self,
        child: Self,
        mut keep: Keep,
    ) -> Result<(), Disagreement<Support, Outcome>>
    where
        Keep: FnMut(&Support, &Outcome) -> bool,
        Support: Clone,
        Outcome: Clone + PartialEq,
    {
        let Self { layers, own } = child;
        // The child read each layer up to its newest one. A settle never
        // merges a layer that a child still holds, so the layers past those
        // and this memo's own entries came after the child's fork.
        let since = self.layers.get(layers.len() ..).unwrap_or_default();
        for (support, outcome) in own.entries() {
            if !keep(support, outcome) {
                continue;
            }
            let held = self
                .own
                .recall(support)
                .or_else(|| since.iter().rev().find_map(|layer| layer.recall(support)));
            if let Some(held) = held
                && held.outcome() != outcome
            {
                return Err(Disagreement {
                    support: support.clone(),
                    held: held.outcome().clone(),
                    offered: outcome.clone(),
                });
            }
        }
        drop(layers);
        self.settle();
        for (support, outcome) in own.into_entries() {
            if keep(&support, &outcome) {
                // A memo at its ceiling declines the entry, which costs reuse
                // alone, as it does at a serial record.
                let _recorded = self.own.remember(support, outcome);
            }
        }
        Ok(())
    }

    /// Merge each frozen layer that no child reads any more into this memo,
    /// newest first, so the frozen layers of a memo are the ones a child
    /// still reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the memo serves each support as it served it before; the
    ///   newest frozen layer, if any, is one that another memo still reads.
    /// - provides: the step after a join that keeps the stack of layers as deep
    ///   as the forks still open.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — which layer another memo reads is a count of its
    ///   holders, which no predicate over this memo reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a settle after the last join leaves one layer that
    ///   counts each entry once.
    /// - witness: `overlay::tests::a_join_folds_the_children_in_their_order_as_a_serial_memo_records_them`
    #[inline]
    pub fn settle(&mut self)
    {
        while let Some(newest) = self.layers.pop() {
            match Arc::try_unwrap(newest) {
                Ok(mut layer) => {
                    for (support, outcome) in core::mem::take(&mut self.own).into_entries() {
                        // As at a join: an entry declined at the ceiling costs
                        // reuse alone.
                        let _recorded = layer.remember(support, outcome);
                    }
                    self.own = layer;
                },
                Err(shared) => {
                    self.layers.push(shared);
                    return;
                },
            }
        }
    }
}

impl<Support, Outcome> CheckMemo<Support, Outcome> for OverlaidMemo<Support, Outcome>
where
    Support: MemoKey,
{
    const ACTIVITY: MemoActivity = MemoActivity::Active;

    /// The entries filed under `digest`: this memo's own first, then each
    /// frozen layer's, newest first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every entry of every layer whose support carries `digest`,
    ///   each layer's in its own probe order. A layer's entry may shadow an
    ///   agreeing entry of an older one, and the consumer's first agreeing hit
    ///   is the newer.
    /// - provides: the candidates a recall decides among.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the result is a lazy iterator borrowing the memo.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OverlaidMemo`].
    /// - witness: `overlay::tests::a_child_reads_the_memo_as_it_stood_at_the_fork`
    #[inline]
    fn filed<'memo>(
        &'memo self,
        digest: ContentDigest,
    ) -> impl Iterator<Item = MemoHit<'memo, Support, Outcome>>
    where
        Support: 'memo,
        Outcome: 'memo,
    {
        self.own.filed(digest).chain(
            self.layers
                .iter()
                .rev()
                .flat_map(move |layer| layer.filed(digest)),
        )
    }

    /// Record `outcome` for `support` in this memo's own entries.
    ///
    /// # Specification
    /// - requires: as [`HashedMemo`]'s record.
    /// - ensures: as [`HashedMemo`]'s record over this memo's own entries; an
    ///   agreeing entry of a frozen layer stays, and the new entry shadows it.
    /// - provides: a forked job's record.
    /// - fails: as [`HashedMemo`]'s record.
    /// - panics: none.
    /// - executable: none — [`HashedMemo`]'s record checks its own predicate
    ///   over this memo's own entries.
    ///
    /// # Errors
    /// [`MemoError::EntryCountOverflow`] as [`HashedMemo`]'s record.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OverlaidMemo`].
    /// - witness: `overlay::tests::a_child_reads_the_memo_as_it_stood_at_the_fork`
    #[inline]
    fn remember(
        &mut self,
        support: Support,
        outcome: Outcome,
    ) -> Result<MemoRecord, MemoError>
    {
        self.own.remember(support, outcome)
    }

    /// The entries of every layer, an entry and the one it shadows counted
    /// apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entry_count(&self) -> MemoEntryCount
    {
        self.layers
            .iter()
            .fold(self.own.entry_count(), |sum, layer| {
                sum.saturating_add(layer.entry_count())
            })
    }

    /// The entries of every layer on `plane`, as [`Self::entry_count`] counts
    /// them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane_entry_count(
        &self,
        plane: Support::Plane,
    ) -> MemoEntryCount
    {
        self.layers
            .iter()
            .fold(self.own.plane_entry_count(plane), |sum, layer| {
                sum.saturating_add(layer.plane_entry_count(plane))
            })
    }

    /// A child of this memo at this fork point, as [`Self::fork`] opens it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: some child, as [`Self::fork`] ensures.
    /// - provides: the memo a forked job of a check records into.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::fork`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OverlaidMemo`].
    /// - witness: `overlay::tests::a_child_reads_the_memo_as_it_stood_at_the_fork`
    #[inline]
    fn fork_child(&mut self) -> Option<Self>
    {
        Some(self.fork())
    }

    /// Fold `child` into this memo, as [`Self::join`] folds it.
    ///
    /// # Specification
    /// - requires: as [`Self::join`].
    /// - ensures: as [`Self::join`].
    /// - provides: the fold of a forked job's memo at its join.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::join`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`OverlaidMemo`].
    /// - witness: `overlay::tests::a_join_folds_the_children_in_their_order_as_a_serial_memo_records_them`
    #[inline]
    fn join_child<Keep>(
        &mut self,
        child: Self,
        keep: Keep,
    ) where
        Keep: FnMut(&Support, &Outcome) -> bool,
    {
        self.join(child, keep);
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use anodized::spec;

    use super::OverlaidMemo;
    use crate::digest::ContentAgreement;
    use crate::digest::ContentDigest;
    use crate::digest::DigestWord;
    use crate::key::MemoKey;
    use crate::memo::CheckMemo as _;
    use crate::memo::HashedMemo;

    /// The one plane of the fixture.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    struct Plane;

    /// A support that names its content by one word.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Named(u64);

    /// An outcome the fixture keeps, by one word.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Kept(u64);

    impl MemoKey for Named
    {
        type Plane = Plane;

        /// The fixture's one plane.
        ///
        /// # Specification
        /// trivial.
        fn plane(&self) -> Plane
        {
            Plane
        }

        /// The name's word, in the high word of the digest.
        ///
        /// # Specification
        /// trivial.
        fn digest(&self) -> ContentDigest
        {
            ContentDigest::new(DigestWord::from(self.0), DigestWord::from(0_u64))
        }

        /// Agrees exactly when the two names are equal.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: answers `ContentAgreement::Agree` exactly when `self` and
        ///   `other` are equal.
        /// - provides: the deciding comparison of the fixture.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — a child's entry under one name shadows the
        ///   parent's, and a name the child did not record reads the layer
        ///   below.
        /// - witness: `overlay::tests::a_child_reads_the_memo_as_it_stood_at_the_fork`
        #[spec(ensures: |ret| matches!(ret, ContentAgreement::Agree) == (self == other))]
        fn agreement(
            &self,
            other: &Self,
        ) -> ContentAgreement
        {
            if self == other {
                ContentAgreement::Agree
            }
            else {
                ContentAgreement::Differ
            }
        }
    }

    /// The outcome `memo` serves for `named`.
    ///
    /// # Specification
    /// trivial.
    fn served<M>(
        memo: &M,
        named: Named,
    ) -> Option<Kept>
    where
        M: crate::memo::CheckMemo<Named, Kept>,
    {
        memo.recall(&named).map(|hit| *hit.outcome())
    }

    /// Record each pair of `entries` in `memo`, in order.
    ///
    /// # Specification
    /// trivial.
    fn record<M>(
        memo: &mut M,
        entries: &[(Named, Kept)],
    ) where
        M: crate::memo::CheckMemo<Named, Kept>,
    {
        for &(named, outcome) in entries {
            let _recorded = memo.remember(named, outcome);
        }
    }

    #[test]
    fn a_join_folds_the_children_in_their_order_as_a_serial_memo_records_them()
    {
        let before = [(Named(1), Kept(10))];
        let first = [(Named(2), Kept(20)), (Named(1), Kept(11))];
        // The two children answer `Named(2)` alike, so they glue in either
        // order.
        let second = [(Named(2), Kept(20)), (Named(3), Kept(30))];
        for swapped in [false, true] {
            let mut parent = OverlaidMemo::new();
            record(&mut parent, &before);
            let mut left = parent.fork();
            let mut right = parent.fork();
            record(&mut left, &first);
            record(&mut right, &second);
            let mut serial = HashedMemo::new();
            record(&mut serial, &before);
            let order = if swapped {
                [(right, second), (left, first)]
            }
            else {
                [(left, first), (right, second)]
            };
            for (child, entries) in order {
                parent
                    .join(child, |_, _| true)
                    .expect("children that answer each support alike glue");
                record(&mut serial, &entries);
            }
            parent.settle();
            let found = (0_u64 .. 5)
                .map(|named| served(&parent, Named(named)))
                .collect::<Vec<_>>();
            let expected = (0_u64 .. 5)
                .map(|named| served(&serial, Named(named)))
                .collect::<Vec<_>>();
            assert_eq!(
                found, expected,
                "the joined memo serves what the serial memo serves, swapped: {swapped}"
            );
            assert_eq!(
                parent.entry_count(),
                serial.entry_count(),
                "after the settle each entry counts once, swapped: {swapped}"
            );
        }
    }

    #[test]
    fn a_child_reads_the_memo_as_it_stood_at_the_fork()
    {
        let mut parent = OverlaidMemo::new();
        record(&mut parent, &[(Named(1), Kept(10))]);
        let mut child = parent.fork();
        record(&mut parent, &[(Named(2), Kept(20))]);
        record(&mut child, &[(Named(1), Kept(11))]);
        assert_eq!(
            served(&child, Named(1)),
            Some(Kept(11)),
            "the child's own entry shadows the one below"
        );
        assert_eq!(
            served(&child, Named(2)),
            None,
            "the child does not read what the parent records after the fork"
        );
        assert_eq!(
            served(&parent, Named(1)),
            Some(Kept(10)),
            "the parent does not read the child's entry before the join"
        );
        parent
            .join(child, |_, _| true)
            .expect("a child that answers again an entry it read glues");
        parent.settle();
        assert_eq!([served(&parent, Named(1)), served(&parent, Named(2))], [
            Some(Kept(11)),
            Some(Kept(20))
        ]);
    }

    #[test]
    fn a_join_drops_what_the_parent_does_not_keep()
    {
        let mut parent = OverlaidMemo::new();
        let mut child = parent.fork();
        record(&mut child, &[(Named(1), Kept(10)), (Named(2), Kept(20))]);
        parent
            .join(child, |named, _| *named != Named(2))
            .expect("a lone child glues");
        parent.settle();
        assert_eq!([served(&parent, Named(1)), served(&parent, Named(2))], [
            Some(Kept(10)),
            None
        ]);
    }

    #[test]
    fn a_join_refuses_two_outcomes_under_one_key_and_names_both()
    {
        for swapped in [false, true] {
            let mut parent = OverlaidMemo::new();
            record(&mut parent, &[(Named(1), Kept(10))]);
            let mut left = parent.fork();
            let mut right = parent.fork();
            record(&mut left, &[(Named(2), Kept(20))]);
            record(&mut right, &[(Named(2), Kept(21)), (Named(3), Kept(30))]);
            let (first, second, held, offered, third) = if swapped {
                (right, left, Kept(21), Kept(20), Some(Kept(30)))
            }
            else {
                (left, right, Kept(20), Kept(21), None)
            };
            parent
                .join(first, |_, _| true)
                .expect("the first child glues");
            let refused = parent
                .join(second, |_, _| true)
                .expect_err("two outcomes under one key do not glue");
            assert_eq!(
                (*refused.support(), *refused.held(), *refused.offered()),
                (Named(2), held, offered),
                "the refusal names the key and both outcomes, swapped: {swapped}"
            );
            assert_eq!(
                [
                    served(&parent, Named(1)),
                    served(&parent, Named(2)),
                    served(&parent, Named(3))
                ],
                [Some(Kept(10)), Some(held), third],
                "the refused child folds nothing, swapped: {swapped}"
            );
        }
    }
}
