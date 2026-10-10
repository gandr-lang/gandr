//! Entry-count accounting, per plane and in total.
//!
//! The counts are the measurement surface. A memo's collapse is asserted by
//! comparing its entry count against the expansion count from the other
//! direction, and a two-machine checker asserts the two planes separately so
//! neither machine's collapse hides behind the other's numbers. That makes the
//! counts a contract rather than telemetry, which is why they are maintained
//! with checked arithmetic and a typed overflow rather than saturated.

use alloc::collections::BTreeMap;

use anodized::spec;

/// A failure of the memo's own bookkeeping.
///
/// The memo has no other failure mode: a miss is [`Option::None`], not an
/// error, and nothing here validates a support or an outcome.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum MemoError
{
    /// An entry count is at its ceiling and cannot be incremented, so the memo
    /// declines to record rather than wrap a number a measurement reads.
    EntryCountOverflow,
}

impl core::fmt::Display for MemoError
{
    /// Writes the message for this bookkeeping failure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::EntryCountOverflow => {
                f.write_str("memo entry count is at its ceiling and cannot be incremented")
            },
        }
    }
}

impl core::error::Error for MemoError
{
}

/// How many entries a memo holds — in one plane, or across all of them.
///
/// One type for both roles because both are the same quantity asked over a
/// different partition; a memo's total is the sum of its planes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MemoEntryCount(usize);

impl MemoEntryCount
{
    /// The count of an empty memo, or of a plane holding nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn zero() -> Self
    {
        Self(0)
    }

    /// The next count up.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the count one greater than `self` when representable.
    /// - provides: the only way this crate increments a count, so no bare
    ///   overflowing arithmetic runs on a number a measurement reads.
    /// - fails: returns [`MemoError::EntryCountOverflow`] at the ceiling rather
    ///   than wrapping to zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MemoError::EntryCountOverflow`] when `self` is already the largest
    /// representable count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the sole decision surface is the `checked_add`
    ///   guard, separated by the boundary pair `usize::MAX - 1` (whose
    ///   successor is asserted exactly) and `usize::MAX` (whose refusal is
    ///   asserted as the exact error variant), plus one ordinary value.
    /// - witness: `accounting::tests::successor_of_an_ordinary_count_is_exact`
    /// - witness: `accounting::tests::successor_at_the_ceiling_is_a_typed_refusal`
    #[inline]
    #[spec(ensures: |ret| ret.map(usize::from)
        == usize::from(self).checked_add(1).ok_or(MemoError::EntryCountOverflow))]
    pub fn successor(self) -> Result<Self, MemoError>
    {
        self.0
            .checked_add(1)
            .map_or(Err(MemoError::EntryCountOverflow), |next| Ok(Self(next)))
    }
}

impl From<usize> for MemoEntryCount
{
    /// The count of `value` entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<MemoEntryCount> for usize
{
    /// How many entries `value` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: MemoEntryCount) -> Self
    {
        value.0
    }
}

/// How many distinct digests a memo's storage is bucketed into.
///
/// A separate type from [`MemoEntryCount`] because the two are semantically
/// distinct quantities that a consumer reads *against* each other: a bucket
/// count below the entry count means digests collided, and a consumer measuring
/// collapse needs that distinction rather than a second number in the same
/// units.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MemoBucketCount(usize);

impl From<usize> for MemoBucketCount
{
    /// The count of `value` buckets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<MemoBucketCount> for usize
{
    /// How many buckets `value` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: MemoBucketCount) -> Self
    {
        value.0
    }
}

/// The per-plane and total entry counts a memo maintains as it records.
///
/// Kept incrementally rather than derived on demand so that a measurement over
/// a large memo costs a lookup rather than a walk, and so that the ceiling is
/// reached — if it ever is — at the recording site where it can be refused.
///
/// # Specification
/// - requires: each retained plane count is positive and the sum is
///   representable.
/// - ensures: the total is exactly the sum of the distinct plane counts.
/// - provides: incremental accounting without recounting the memo's entries.
/// - panics: none.
/// - executable: none — a data-item predicate is not checked at construction;
///   the recording operation checks both counters at its mutation boundary.
///
/// # Adequacy
/// - hypothesis: L3 — from an empty census and a valid census one below the
///   ceiling, exact per-plane and total counts distinguish cross-plane bumps,
///   missing-plane mistakes and an early overflow guard. At the ceiling,
///   full-state equality after refusal distinguishes partial mutation for both
///   an existing and an absent plane.
/// - witness: `accounting::tests::recording_bumps_one_plane_and_the_total`
/// - witness: `accounting::tests::ceiling_refusal_preserves_existing_and_absent_planes`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EntryCensus<Plane>
{
    /// The count for each plane that has ever recorded an entry.
    planes: BTreeMap<Plane, MemoEntryCount>,
    /// The sum over every plane.
    total: MemoEntryCount,
}

impl<Plane> EntryCensus<Plane>
where
    Plane: Copy + Ord,
{
    /// A census over no entries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn empty() -> Self
    {
        Self {
            planes: BTreeMap::new(),
            total: MemoEntryCount::zero(),
        }
    }

    /// The total across every plane.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn total(&self) -> MemoEntryCount
    {
        self.total
    }

    /// The count for one plane, zero if that plane has recorded nothing.
    ///
    /// # Specification
    /// - requires: nothing; a plane that has recorded nothing reads zero rather
    ///   than being absent.
    /// - ensures: the returned count never exceeds the total, since the total
    ///   is the sum over planes and no count is negative.
    /// - provides: the per-plane half of the entry-count contract.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for a valid census, a present plane with two entries,
    ///   another with one and an absent plane distinguish zero defaults,
    ///   wrong-plane reads and accidental total-count answers by exact counts.
    /// - witness: `accounting::tests::recording_bumps_one_plane_and_the_total`
    #[inline]
    #[spec(ensures: |ret| ret <= self.total()
        && ret == self.planes.get(&plane).copied().unwrap_or(MemoEntryCount::zero()))]
    pub(crate) fn plane(
        &self,
        plane: Plane,
    ) -> MemoEntryCount
    {
        self.planes
            .get(&plane)
            .map_or_else(MemoEntryCount::zero, |count| *count)
    }

    /// Accounts one freshly recorded entry to `plane`.
    ///
    /// # Specification
    /// - requires: the caller has established that the entry is *fresh* — a
    ///   replaced entry is not counted, since the memo still holds one answer
    ///   for that support.
    /// - ensures: on success both the plane's count and the total are one
    ///   greater; on failure neither moved, so the census never records a
    ///   partial bump.
    /// - provides: the accounting the entry-count contract is asserted through.
    /// - fails: returns [`MemoError::EntryCountOverflow`] if either count is at
    ///   its ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MemoError::EntryCountOverflow`], propagated from
    /// [`MemoEntryCount::successor`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for a valid census and a fresh entry, exact counts
    ///   across two planes distinguish a wrong-plane or missing total bump. A
    ///   total one below the ceiling must advance to the ceiling; the next
    ///   attempt must refuse without changing any field, for both existing and
    ///   absent planes. This separates early guards, wrapping and partial
    ///   mutation. A plane cannot overflow before its valid total does.
    /// - witness: `accounting::tests::recording_bumps_one_plane_and_the_total`
    /// - witness: `accounting::tests::ceiling_refusal_preserves_existing_and_absent_planes`
    #[spec(
        captures: [entry_plane = self.plane(plane), entry_total = self.total()],
        ensures: |ret| match usize::from(entry_total).checked_add(1)
            .zip(usize::from(entry_plane).checked_add(1)) {
            Some((total, count)) => ret.is_ok()
                && usize::from(self.total()) == total
                && usize::from(self.plane(plane)) == count,
            None => ret == Err(MemoError::EntryCountOverflow)
                && self.plane(plane) == entry_plane && self.total() == entry_total,
        }
    )]
    pub(crate) fn record(
        &mut self,
        plane: Plane,
    ) -> Result<(), MemoError>
    {
        let total = self.total.successor()?;
        let current = self.plane(plane);
        let bumped = current.successor()?;
        let _prior = self.planes.insert(plane, bumped);
        self.total = total;
        Ok(())
    }

    /// A valid one-plane census at the representable ceiling, for fault
    /// injection.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: only `plane` is present, and its count and the total are MAX.
    /// - provides: the accounting boundary without allocating MAX memo entries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the census reached by one increment from MAX - 1 is
    ///   compared in full with this fixture, then existing and absent-plane
    ///   records must both refuse unchanged. This catches wrong counts and
    ///   extra-plane fixtures, without representing the memo entries
    ///   themselves.
    /// - witness: `accounting::tests::ceiling_refusal_preserves_existing_and_absent_planes`
    #[cfg(test)]
    #[spec(ensures: |ret| ret.planes.len() == 1
        && usize::from(ret.total()) == usize::MAX
        && usize::from(ret.plane(plane)) == usize::MAX)]
    pub(crate) fn at_ceiling_for_test(plane: Plane) -> Self
    {
        Self {
            planes: BTreeMap::from([(plane, MemoEntryCount::from(usize::MAX))]),
            total: MemoEntryCount::from(usize::MAX),
        }
    }
}

#[cfg(test)]
mod tests
{
    #[cfg(anodized_panic)]
    use anodized::spec;

    use super::MemoEntryCount;
    use super::MemoError;

    /// One below the ceiling: the largest count whose successor still exists.
    /// Evaluated at compile time, so the subtraction is checked by the
    /// compiler rather than at run time.
    const PENULTIMATE_COUNT: usize = usize::MAX - 1;

    /// A plane type standing in for a consumer's own accounting partition.
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum TestPlane
    {
        /// The first partition.
        First,
        /// The second partition.
        Second,
    }

    /// Reject a deliberately invalid caller before entering the body.
    ///
    /// # Specification
    /// - requires: `count` is nonzero.
    /// - ensures: returns the supplied count on valid inputs.
    /// - panics: enforcing builds reject zero with `precondition failed`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero distinguishes an enforcing macro build from a
    ///   target-only flag or stale non-enforcing dependency.
    /// - witness: `accounting::tests::anodized_precondition_sentinel`
    #[cfg(anodized_panic)]
    #[spec(requires: count != MemoEntryCount::zero())]
    fn require_nonzero(count: MemoEntryCount) -> MemoEntryCount
    {
        count
    }

    /// Return zero despite a deliberately false postcondition.
    ///
    /// # Specification
    /// - ensures: the returned count is nonzero, deliberately violated.
    /// - panics: enforcing builds reject the result with `postcondition
    ///   failed`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact postcondition panic distinguishes
    ///   enforcement from an unrelated panic or a silent unchecked return.
    /// - witness: `accounting::tests::anodized_postcondition_sentinel`
    #[cfg(anodized_panic)]
    #[spec(ensures: |count| count != MemoEntryCount::zero())]
    fn false_postcondition() -> MemoEntryCount
    {
        MemoEntryCount::zero()
    }

    #[cfg(anodized_panic)]
    #[test]
    #[should_panic(expected = "precondition failed")]
    fn anodized_precondition_sentinel()
    {
        let _count = require_nonzero(MemoEntryCount::zero());
    }

    #[cfg(anodized_panic)]
    #[test]
    #[should_panic(expected = "postcondition failed")]
    fn anodized_postcondition_sentinel()
    {
        let _count = false_postcondition();
    }

    #[test]
    fn successor_of_an_ordinary_count_is_exact()
    {
        assert_eq!(
            Ok(MemoEntryCount::from(1)),
            MemoEntryCount::zero().successor(),
            "the successor of zero is one"
        );
        assert_eq!(
            Ok(MemoEntryCount::from(usize::MAX)),
            MemoEntryCount::from(PENULTIMATE_COUNT).successor(),
            "the last representable step still succeeds, so the guard is not one too eager"
        );
    }

    #[test]
    fn successor_at_the_ceiling_is_a_typed_refusal()
    {
        assert_eq!(
            Err(MemoError::EntryCountOverflow),
            MemoEntryCount::from(usize::MAX).successor(),
            "the ceiling refuses with the exact variant rather than wrapping to zero"
        );
    }

    #[test]
    fn recording_bumps_one_plane_and_the_total()
    {
        let mut census = super::EntryCensus::<TestPlane>::empty();
        assert_eq!(
            MemoEntryCount::zero(),
            census.total(),
            "an empty census totals zero"
        );
        assert_eq!(
            MemoEntryCount::zero(),
            census.plane(TestPlane::First),
            "a plane that recorded nothing counts zero rather than being absent"
        );
        assert_eq!(Ok(()), census.record(TestPlane::First));
        assert_eq!(Ok(()), census.record(TestPlane::First));
        assert_eq!(Ok(()), census.record(TestPlane::Second));
        assert_eq!(
            MemoEntryCount::from(2),
            census.plane(TestPlane::First),
            "the first plane counts its own two entries"
        );
        assert_eq!(
            MemoEntryCount::from(1),
            census.plane(TestPlane::Second),
            "the second plane counts its own one, so neither hides behind the other"
        );
        assert_eq!(
            MemoEntryCount::from(3),
            census.total(),
            "the total is the sum over planes"
        );
    }

    #[test]
    fn ceiling_refusal_preserves_existing_and_absent_planes()
    {
        let mut census = super::EntryCensus {
            planes: alloc::collections::BTreeMap::from([(
                TestPlane::First,
                MemoEntryCount::from(PENULTIMATE_COUNT),
            )]),
            total: MemoEntryCount::from(PENULTIMATE_COUNT),
        };
        assert_eq!(Ok(()), census.record(TestPlane::First));
        let before = super::EntryCensus::at_ceiling_for_test(TestPlane::First);
        assert_eq!(before, census, "the final representable step is exact");
        for plane in [TestPlane::First, TestPlane::Second] {
            assert_eq!(Err(MemoError::EntryCountOverflow), census.record(plane));
            assert_eq!(
                before, census,
                "refusal must not add a plane or change a count"
            );
        }
    }
}
