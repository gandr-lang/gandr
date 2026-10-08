//! The seam: one interface, a null implementation and an ordered one.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;

use crate::accounting::EntryCensus;
use crate::accounting::MemoBucketCount;
use crate::accounting::MemoEntryCount;
use crate::accounting::MemoError;
use crate::digest::ContentAgreement;
use crate::digest::ContentDigest;
use crate::key::MemoKey;

/// Whether a [`CheckMemo`] implementation ever answers.
///
/// Read at compile time through [`CheckMemo::ACTIVITY`], so a consumer's
/// memo-handling branch costs nothing when the memo is inactive. A consumer
/// matches on it directly — `matches!(M::ACTIVITY, MemoActivity::Active)` —
/// rather than through a predicate, so the guard stays a constant the optimizer
/// folds away and no boolean crosses an interface.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MemoActivity
{
    /// The memo may answer, so the consumer builds supports and consults it.
    Active,
    /// The memo never answers, so the consumer may skip the whole interaction
    /// — support construction included.
    Inactive,
}

/// What a memo did with a support it was asked to record.
///
/// Returned rather than discarded because the three cases are observably
/// different and a consumer's accounting depends on telling them apart: only
/// [`MemoRecord::Recorded`] moves an entry count.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MemoRecord
{
    /// The support was not held before, so a fresh entry now holds it.
    Recorded,
    /// An entry for a support this one agrees with was already held, and its
    /// outcome was replaced.
    Replaced,
    /// Nothing was stored. This is what an inactive memo always answers.
    Discarded,
}

/// A served memo entry: the outcome **together with the support it was
/// recorded under**.
///
/// The support travels with the hit because a support is an output of the
/// judgement rather than a scan beside it, so a hit *carries* its support
/// instead of asserting it. A consumer that must check adoption compares the
/// carried support against the one it demanded, pointwise, rather than
/// intersecting footprints.
///
/// Borrowed rather than cloned: the memo owns the entry for as long as the
/// borrow lives, and an outcome that is expensive to clone is not cloned to be
/// read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemoHit<'memo, Support, Outcome>
{
    /// The support the served entry was recorded under.
    support: &'memo Support,
    /// The outcome recorded for that support.
    outcome: &'memo Outcome,
}

impl<'memo, Support, Outcome> MemoHit<'memo, Support, Outcome>
{
    /// The support the served entry was recorded under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn support(&self) -> &'memo Support
    {
        self.support
    }

    /// The outcome recorded for that support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outcome(&self) -> &'memo Outcome
    {
        self.outcome
    }
}

/// A process-local store of already-computed outcomes, keyed by support.
///
/// # What a hit claims, and what it does not
///
/// A hit claims exactly this: **this process already computed this answer for
/// this support**. It does not claim the answer is right, that the support was
/// well formed, or that anything was validated. The memo is sound only when the
/// consumer's support is the *whole* input to the computation it indexes; the
/// consumer owns that argument, and no property of this crate rescues a support
/// that is not.
///
/// Nothing here persists and nothing here is a wire format. The lifetime of a
/// memo is the consumer's, and the two-wall rule — a hit claims only its own
/// history, and no kernel-checked support discipline exists — is what keeps it
/// inside one process.
///
/// # Specification
/// - requires: `Support` is the complete input to the computation the outcome
///   indexes, per [`MemoKey`].
/// - ensures: [`CheckMemo::recall`] serves only an entry whose support answers
///   [`ContentAgreement::Agree`] against the demanded support — never one
///   selected by digest alone.
/// - provides: the checker's skip-a-repeated-question seam, with storage,
///   policy, and lifetime outside the checker. This stays prose: a clause on
///   this trait would turn each declaration into a wrapper over a generated
///   required method and change what an implementor implements. The recall
///   claim is a clause on [`OrderedMemo::recall`] instead, where the served
///   entry is in hand.
/// - fails: only through [`CheckMemo::remember`]; a miss is [`Option::None`],
///   not an error.
/// - panics: none.
pub trait CheckMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// Whether this implementation ever answers, known at compile time.
    const ACTIVITY: MemoActivity;

    /// The entry already recorded for a support this one agrees with, if any.
    ///
    /// # Specification
    /// - requires: `support` is the complete input to the computation whose
    ///   outcome is being recalled.
    /// - ensures: answers `Some` only for an entry whose recorded support
    ///   answers `ContentAgreement::Agree` against `support`, and `None`
    ///   otherwise; a digest match alone never serves an entry, and a miss is
    ///   an absence rather than a failure.
    /// - provides: the skip-a-repeated-question half of the seam, with the
    ///   served support carried beside its outcome so a consumer checks
    ///   adoption pointwise. This stays prose: a clause on a trait declaration
    ///   turns each declaration into a wrapper over a generated required method
    ///   and changes what an implementor implements; the agreement clause sits
    ///   on `OrderedMemo::recall`, where the served entry is in hand.
    /// - panics: none.
    fn recall<'memo>(
        &'memo self,
        support: &Support,
    ) -> Option<MemoHit<'memo, Support, Outcome>>;

    /// Record `outcome` as the answer for `support`.
    ///
    /// # Specification
    /// - requires: `support` is the complete input to the computation `outcome`
    ///   answers.
    /// - ensures: `MemoRecord::Recorded` exactly when no held support agreed
    ///   with this one and a fresh entry now holds it, `MemoRecord::Replaced`
    ///   when an agreeing entry's outcome was overwritten, and
    ///   `MemoRecord::Discarded` when nothing was stored, which is what an
    ///   inactive implementation always answers; only the recorded case moves
    ///   an entry count.
    /// - provides: the record half of the seam. This stays prose for the same
    ///   reason as `CheckMemo::recall`, and the two shipped implementations
    ///   carry their own clauses.
    /// - fails: the entry accounting refuses another entry, and the memo then
    ///   holds what it held before.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MemoError::EntryCountOverflow`] when the entry accounting cannot admit
    /// another entry. The memo then holds what it held before.
    fn remember(
        &mut self,
        support: Support,
        outcome: Outcome,
    ) -> Result<MemoRecord, MemoError>;

    /// How many entries are held across every plane.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers how many entries the implementation holds across
    ///   every plane, which is zero for one declaring `MemoActivity::Inactive`.
    /// - provides: the total half of the entry-count contract a consumer
    ///   measures collapse against. This stays prose for the same reason as
    ///   `CheckMemo::recall`, and both shipped implementations carry their own
    ///   clauses.
    /// - panics: none.
    fn entry_count(&self) -> MemoEntryCount;

    /// How many entries are held on one plane.
    ///
    /// # Specification
    /// - requires: nothing; a plane that has recorded nothing reads zero rather
    ///   than being absent.
    /// - ensures: answers how many entries the implementation holds on `plane`,
    ///   never more than the total across planes.
    /// - provides: the per-plane half of the entry-count contract, so neither
    ///   of a two-machine consumer's planes hides its collapse behind the
    ///   other's numbers. This stays prose for the same reason as
    ///   `CheckMemo::recall`.
    /// - panics: none.
    fn plane_entry_count(
        &self,
        plane: Support::Plane,
    ) -> MemoEntryCount;
}

/// The memo that never answers: the unmemoized path, as a type parameter.
///
/// Zero-sized, and every method is a constant, so a consumer instantiated here
/// compiles to the code it would have had with no memo at all. This is the
/// differential's fresh side — the same checker, not a second one.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NullMemo;

impl<Support, Outcome> CheckMemo<Support, Outcome> for NullMemo
where
    Support: MemoKey,
{
    const ACTIVITY: MemoActivity = MemoActivity::Inactive;

    /// Answers nothing, whatever the support.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers `None` unconditionally, so a consumer instantiated
    ///   here runs the path it would have run with no memo at all.
    /// - provides: the fresh side of the differential — the same consumer, not
    ///   a second one.
    /// - panics: none.
    #[inline]
    fn recall<'memo>(
        &'memo self,
        _support: &Support,
    ) -> Option<MemoHit<'memo, Support, Outcome>>
    {
        None
    }

    /// Stores nothing, and reports that it stored nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: retains neither support nor outcome and answers
    ///   `Ok(MemoRecord::Discarded)`, so no entry count moves.
    /// - provides: the record path that is no path at all.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn remember(
        &mut self,
        _support: Support,
        _outcome: Outcome,
    ) -> Result<MemoRecord, MemoError>
    {
        Ok(MemoRecord::Discarded)
    }

    /// Reports the constant zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entry_count(&self) -> MemoEntryCount
    {
        MemoEntryCount::zero()
    }

    /// Reports the constant zero, for every plane.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn plane_entry_count(
        &self,
        _plane: Support::Plane,
    ) -> MemoEntryCount
    {
        MemoEntryCount::zero()
    }
}

/// One recorded answer, held beside the support it was recorded under.
#[derive(Clone, Debug, Eq, PartialEq)]
struct MemoEntry<Support, Outcome>
{
    /// The support, kept so a hit can carry it.
    support: Support,
    /// The answer recorded for that support.
    outcome: Outcome,
}

/// An ordered in-memory memo: the storage half, owned here so the checker holds
/// none of it.
///
/// **Ordered rather than hashed on purpose.** No hasher enters the kernel's
/// dependency wall, and iteration order is deterministic — which is what makes
/// a measurement over the memo re-derivable rather than run-dependent.
///
/// **Bucketed by digest, decided by content.** The map is keyed by the
/// support's [`ContentDigest`], and each key holds the bucket of supports that
/// digested to it. A lookup picks the bucket, then scans it with the deciding
/// comparison. So a digest collision costs one comparison and degrades to a
/// miss; it cannot answer for the wrong support. That is the
/// positive-fast-path-only discipline as a data structure rather than as a rule
/// to remember, and it is what lets the key be content-derived — and therefore
/// arena-free — from the start.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OrderedMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// The recorded answers, bucketed by digest and ordered by it.
    buckets: BTreeMap<ContentDigest, Vec<MemoEntry<Support, Outcome>>>,
    /// The entry counts, maintained as entries are recorded.
    census: EntryCensus<Support::Plane>,
}

impl<Support, Outcome> OrderedMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// An empty memo.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            buckets: BTreeMap::new(),
            census: EntryCensus::empty(),
        }
    }

    /// How many digest buckets are held.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number of distinct digests recorded, which is at most the
    ///   entry count and equal to it exactly when no two recorded supports
    ///   collided.
    /// - provides: the observation that separates a collision from a miss — a
    ///   bucket count below the entry count is a collision, and a consumer
    ///   measuring collapse needs to know its digest is not degenerate.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the surface is which map is measured, separated
    ///   by a colliding pair (two entries, one bucket) against a non-colliding
    ///   pair (two entries, two buckets), both asserted exactly.
    /// - witness: `memo::tests::colliding_digests_share_a_bucket_and_still_decide`
    /// - witness: `memo::tests::distinct_supports_take_distinct_entries`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| usize::from(ret) <= usize::from(self.census.total()))]
    pub fn bucket_count(&self) -> MemoBucketCount
    {
        MemoBucketCount::from(self.buckets.len())
    }
}

impl<Support, Outcome> Default for OrderedMemo<Support, Outcome>
where
    Support: MemoKey,
{
    /// The empty memo.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl<Support, Outcome> CheckMemo<Support, Outcome> for OrderedMemo<Support, Outcome>
where
    Support: MemoKey,
{
    const ACTIVITY: MemoActivity = MemoActivity::Active;

    /// The entry recorded for a support this one agrees with, if any.
    ///
    /// # Specification
    /// - requires: `support` is the complete input to the computation whose
    ///   outcome is being recalled.
    /// - ensures: a served hit's own support answers `ContentAgreement::Agree`
    ///   against `support`. The digest picks the bucket and the deciding
    ///   comparison scans it, so a collision costs one comparison and degrades
    ///   to a miss rather than answering for the wrong support, and a support
    ///   whose digest disagrees costs collapse rather than correctness.
    /// - provides: the hit, carrying the support it was recorded under beside
    ///   its outcome.
    /// - fails: never; a miss is `None`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the bucket lookup and the
    ///   deciding scan inside it, separated by three cases that a digest-only
    ///   implementation and a content-only implementation answer differently:
    ///   equal content with equal digests (a hit), distinct content with equal
    ///   digests (a miss), and equal content with distinct digests (a miss),
    ///   each asserted as an exact outcome or `None`.
    /// - witness: `memo::tests::an_ordered_memo_serves_what_it_was_told`
    /// - witness: `memo::tests::colliding_digests_share_a_bucket_and_still_decide`
    /// - witness: `memo::tests::a_disagreeing_digest_costs_collapse_and_not_correctness`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|hit| {
        matches!(hit.support().agreement(support), ContentAgreement::Agree)
    }))]
    #[inline]
    fn recall<'memo>(
        &'memo self,
        support: &Support,
    ) -> Option<MemoHit<'memo, Support, Outcome>>
    {
        let bucket = self.buckets.get(&support.digest())?;
        let entry = bucket
            .iter()
            .find(|entry| matches!(entry.support.agreement(support), ContentAgreement::Agree))?;
        Some(MemoHit {
            support: &entry.support,
            outcome: &entry.outcome,
        })
    }

    /// Records `outcome` as the answer for `support`.
    ///
    /// # Specification
    /// - requires: `support` is the complete input to the computation `outcome`
    ///   answers.
    /// - ensures: a fresh support takes a new entry in its digest's bucket and
    ///   leaves the entry count one greater; a support an agreeing entry
    ///   already holds has that entry's outcome replaced and leaves every count
    ///   where it was.
    /// - provides: the record path, with the accounting bumped before the entry
    ///   is pushed, so a refusal at the ceiling leaves the memo exactly as it
    ///   was.
    /// - fails: `MemoError::EntryCountOverflow` when the accounting cannot
    ///   admit another entry.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MemoError::EntryCountOverflow`] when the entry accounting cannot admit
    /// another entry; the memo then holds what it held before.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the fresh-versus-replaced
    ///   branch and the accounting that rides only the fresh arm, separated by
    ///   recording one support twice (exactly `Recorded` then `Replaced`, one
    ///   entry, the later outcome served) against recording two agreeing-free
    ///   supports (two entries, both served).
    /// - witness: `memo::tests::an_ordered_memo_serves_what_it_was_told`
    /// - witness: `memo::tests::remembering_an_agreeing_support_replaces_rather_than_accumulates`
    /// - witness: `memo::tests::distinct_supports_take_distinct_entries`
    #[spec(
        captures: [entry_count = self.entry_count()],
        ensures: |ret| if matches!(ret, Ok(MemoRecord::Recorded)) {
            usize::from(self.entry_count()) == usize::from(entry_count).saturating_add(1)
        } else {
            self.entry_count() == entry_count
        }
    )]
    #[inline]
    fn remember(
        &mut self,
        support: Support,
        outcome: Outcome,
    ) -> Result<MemoRecord, MemoError>
    {
        let digest = support.digest();
        if let Some(bucket) = self.buckets.get_mut(&digest) {
            let held = bucket
                .iter_mut()
                .find(|entry| matches!(entry.support.agreement(&support), ContentAgreement::Agree));
            if let Some(entry) = held {
                entry.outcome = outcome;
                return Ok(MemoRecord::Replaced);
            }
        }
        // The accounting is bumped before the entry is pushed, so a refusal at
        // the ceiling leaves the memo exactly as it was.
        self.census.record(support.plane())?;
        self.buckets
            .entry(digest)
            .or_default()
            .push(MemoEntry { support, outcome });
        Ok(MemoRecord::Recorded)
    }

    /// The total across every plane.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn entry_count(&self) -> MemoEntryCount
    {
        self.census.total()
    }

    /// # Specification
    /// - requires: nothing.
    /// - ensures: the plane's count never exceeds the total across planes.
    /// - provides: the per-plane collapse measurement.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surface is which partition is read,
    ///   separated by two planes holding different numbers of entries, each
    ///   asserted as an exact count against the total.
    /// - witness: `memo::tests::entries_are_accounted_to_their_own_plane`
    #[inline]
    #[spec(ensures: |ret| ret <= self.entry_count())]
    fn plane_entry_count(
        &self,
        plane: Support::Plane,
    ) -> MemoEntryCount
    {
        self.census.plane(plane)
    }
}

#[cfg(test)]
mod tests
{
    use super::CheckMemo;
    use super::MemoActivity;
    use super::MemoRecord;
    use super::NullMemo;
    use super::OrderedMemo;
    use crate::accounting::MemoBucketCount;
    use crate::accounting::MemoEntryCount;
    use crate::digest::ContentAgreement;
    use crate::digest::ContentDigest;
    use crate::digest::DigestWord;
    use crate::key::MemoKey;

    /// A plane standing in for a consumer's accounting partition.
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum TestPlane
    {
        /// The plane a term-checking machine would account to.
        Term,
        /// The plane a type-formation machine would account to.
        Type,
    }

    /// A support whose content and digest are supplied separately, so a test
    /// can drive the digest and the deciding comparison apart from each other.
    ///
    /// That separation is the point: no honest consumer would build such a
    /// support, and it is the only way to exhibit a collision and a digest
    /// disagreement without a hash function that cooperates.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TestSupport
    {
        /// The accounting partition.
        plane: TestPlane,
        /// The content the deciding comparison reads.
        content: TestContent,
        /// The digest the fast path reads.
        digest: DigestWord,
    }

    /// The content of a [`TestSupport`].
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TestContent(u8);

    /// An outcome standing in for a consumer's own verdict type.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TestOutcome(u8);

    impl TestSupport
    {
        /// A support whose digest is a function of its content, as an honest
        /// consumer's would be.
        ///
        /// # Specification
        /// trivial.
        fn honest(
            plane: TestPlane,
            content: TestContent,
        ) -> Self
        {
            Self {
                plane,
                content,
                digest: DigestWord::from(u64::from(content.0)),
            }
        }
    }

    impl MemoKey for TestSupport
    {
        type Plane = TestPlane;

        /// The support's accounting partition.
        ///
        /// # Specification
        /// trivial.
        fn plane(&self) -> Self::Plane
        {
            self.plane
        }

        /// The digest the fast path reads, carried in the low word.
        ///
        /// # Specification
        /// trivial.
        fn digest(&self) -> ContentDigest
        {
            ContentDigest::new(DigestWord::from(0), self.digest)
        }

        /// Agrees exactly when plane and content both match.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: answers `ContentAgreement::Agree` exactly when `self` and
        ///   `other` carry the same plane and the same content, reading neither
        ///   digest.
        /// - provides: the deciding comparison a collision and a digest
        ///   disagreement are exhibited through, since the digest is supplied
        ///   apart from the content.
        /// - panics: none.
        fn agreement(
            &self,
            other: &Self,
        ) -> ContentAgreement
        {
            if self.plane == other.plane && self.content == other.content {
                ContentAgreement::Agree
            }
            else {
                ContentAgreement::Differ
            }
        }
    }

    #[test]
    fn the_two_implementations_declare_opposite_activities()
    {
        assert_eq!(
            MemoActivity::Inactive,
            <NullMemo as CheckMemo<TestSupport, TestOutcome>>::ACTIVITY,
            "the null memo declares itself inactive so the consumer's branch is constant"
        );
        assert_eq!(
            MemoActivity::Active,
            <OrderedMemo<TestSupport, TestOutcome> as CheckMemo<TestSupport, TestOutcome>>::ACTIVITY,
            "and the ordered memo declares itself active, so the two are distinguishable at compile time"
        );
    }

    #[test]
    fn the_null_memo_never_answers_and_never_accounts()
    {
        let support = TestSupport::honest(TestPlane::Term, TestContent(1));
        let mut memo = NullMemo;
        assert_eq!(
            Ok(MemoRecord::Discarded),
            CheckMemo::remember(&mut memo, support, TestOutcome(9)),
            "the null memo says plainly that it stored nothing"
        );
        assert!(
            CheckMemo::<TestSupport, TestOutcome>::recall(&memo, &support).is_none(),
            "the null memo forgets what it was told, which is what makes it the fresh side"
        );
        assert_eq!(
            MemoEntryCount::zero(),
            CheckMemo::<TestSupport, TestOutcome>::entry_count(&memo),
            "and it accounts nothing, so a differential can assert the fresh side served nothing"
        );
        assert_eq!(
            MemoEntryCount::zero(),
            CheckMemo::<TestSupport, TestOutcome>::plane_entry_count(&memo, TestPlane::Term),
            "per plane too"
        );
    }

    #[test]
    fn an_ordered_memo_serves_what_it_was_told()
    {
        let mut memo: OrderedMemo<TestSupport, TestOutcome> = OrderedMemo::new();
        let first = TestSupport::honest(TestPlane::Term, TestContent(1));
        let second = TestSupport::honest(TestPlane::Term, TestContent(2));
        let unasked = TestSupport::honest(TestPlane::Term, TestContent(3));
        assert_eq!(
            MemoEntryCount::zero(),
            memo.entry_count(),
            "a fresh memo holds nothing"
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(first, TestOutcome(9))
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(second, TestOutcome(8))
        );

        let hit = memo.recall(&first).expect("the first support was recorded");
        assert_eq!(&TestOutcome(9), hit.outcome(), "the first answer");
        assert_eq!(
            &first,
            hit.support(),
            "and the hit carries the support it was recorded under rather than asserting one"
        );
        let hit = memo
            .recall(&second)
            .expect("the second support was recorded");
        assert_eq!(&TestOutcome(8), hit.outcome(), "the second answer");
        assert!(memo.recall(&unasked).is_none(), "an unasked support misses");
        assert_eq!(
            MemoEntryCount::from(2),
            memo.entry_count(),
            "two distinct supports were answered"
        );
    }

    #[test]
    fn remembering_an_agreeing_support_replaces_rather_than_accumulates()
    {
        let mut memo: OrderedMemo<TestSupport, TestOutcome> = OrderedMemo::new();
        let support = TestSupport::honest(TestPlane::Term, TestContent(1));
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(support, TestOutcome(9))
        );
        assert_eq!(
            Ok(MemoRecord::Replaced),
            memo.remember(support, TestOutcome(7)),
            "the second recording of one support replaces rather than growing a second entry"
        );
        let hit = memo.recall(&support).expect("the support was recorded");
        assert_eq!(
            &TestOutcome(7),
            hit.outcome(),
            "the later answer stands, so a consumer cannot grow two answers for one support"
        );
        assert_eq!(
            MemoEntryCount::from(1),
            memo.entry_count(),
            "one support, one entry — a replacement does not move the accounting"
        );
    }

    #[test]
    fn distinct_supports_take_distinct_entries()
    {
        let mut memo: OrderedMemo<TestSupport, TestOutcome> = OrderedMemo::new();
        let first = TestSupport::honest(TestPlane::Term, TestContent(1));
        let second = TestSupport::honest(TestPlane::Term, TestContent(2));
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(first, TestOutcome(9))
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(second, TestOutcome(8))
        );
        assert_eq!(MemoEntryCount::from(2), memo.entry_count(), "two entries");
        assert_eq!(
            MemoBucketCount::from(2),
            memo.bucket_count(),
            "in two buckets, since these two digests do not collide"
        );
    }

    #[test]
    fn entries_are_accounted_to_their_own_plane()
    {
        let mut memo: OrderedMemo<TestSupport, TestOutcome> = OrderedMemo::new();
        let term = TestSupport::honest(TestPlane::Term, TestContent(1));
        let other_term = TestSupport::honest(TestPlane::Term, TestContent(2));
        // Same content as `term`, different plane: the plane is part of the
        // support, so this is a different question with a different answer.
        let formation = TestSupport::honest(TestPlane::Type, TestContent(1));
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(term, TestOutcome(9))
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(other_term, TestOutcome(8))
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(formation, TestOutcome(7))
        );
        assert_eq!(
            MemoEntryCount::from(2),
            memo.plane_entry_count(TestPlane::Term),
            "the term plane counts its own two"
        );
        assert_eq!(
            MemoEntryCount::from(1),
            memo.plane_entry_count(TestPlane::Type),
            "the type plane counts its own one, so neither plane's collapse hides behind the other"
        );
        assert_eq!(
            MemoEntryCount::from(3),
            memo.entry_count(),
            "three in total"
        );
        let hit = memo
            .recall(&formation)
            .expect("the formation support was recorded");
        assert_eq!(
            &TestOutcome(7),
            hit.outcome(),
            "and the same content on another plane is served its own answer, not the term plane's"
        );
    }

    #[test]
    fn colliding_digests_share_a_bucket_and_still_decide()
    {
        let mut memo: OrderedMemo<TestSupport, TestOutcome> = OrderedMemo::new();
        let first = TestSupport {
            plane: TestPlane::Term,
            content: TestContent(1),
            digest: DigestWord::from(42),
        };
        let second = TestSupport {
            plane: TestPlane::Term,
            content: TestContent(2),
            digest: DigestWord::from(42),
        };
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(first, TestOutcome(9))
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(second, TestOutcome(8)),
            "an equal digest over differing content is a second entry, not a replacement"
        );
        assert_eq!(MemoEntryCount::from(2), memo.entry_count(), "two entries");
        assert_eq!(
            MemoBucketCount::from(1),
            memo.bucket_count(),
            "in one bucket, which is what a collision looks like"
        );
        let hit = memo.recall(&first).expect("the first support was recorded");
        assert_eq!(
            &TestOutcome(9),
            hit.outcome(),
            "and each support is still served its own answer: the digest narrowed, the content decided"
        );
        let hit = memo
            .recall(&second)
            .expect("the second support was recorded");
        assert_eq!(&TestOutcome(8), hit.outcome(), "the second answer likewise");

        let uncollided = TestSupport {
            plane: TestPlane::Term,
            content: TestContent(3),
            digest: DigestWord::from(42),
        };
        assert!(
            memo.recall(&uncollided).is_none(),
            "and a third support colliding with both is a miss, priced as recomputation rather than as a wrong answer"
        );
    }

    #[test]
    fn a_disagreeing_digest_costs_collapse_and_not_correctness()
    {
        let mut memo: OrderedMemo<TestSupport, TestOutcome> = OrderedMemo::new();
        let recorded = TestSupport {
            plane: TestPlane::Term,
            content: TestContent(1),
            digest: DigestWord::from(1),
        };
        // The same content under a different digest. A digest that does not
        // agree where the content does can only lose reuse.
        let demanded = TestSupport {
            plane: TestPlane::Term,
            content: TestContent(1),
            digest: DigestWord::from(2),
        };
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(recorded, TestOutcome(9))
        );
        assert!(
            memo.recall(&demanded).is_none(),
            "the demand misses, which costs the collapse and cannot manufacture a hit"
        );
        assert_eq!(
            Ok(MemoRecord::Recorded),
            memo.remember(demanded, TestOutcome(9)),
            "and recording it again is a fresh entry in a second bucket rather than a replacement"
        );
        assert_eq!(MemoEntryCount::from(2), memo.entry_count());
        assert_eq!(MemoBucketCount::from(2), memo.bucket_count());
    }
}
