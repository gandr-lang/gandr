//! Records, record positions and counts, and the key ranges that select them.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;

use crate::bytes::OwnedRecordKey;
use crate::bytes::OwnedRecordValue;
use crate::bytes::RecordKey;
use crate::bytes::RecordValue;
use crate::error::RecordTreeError;

/// A position in a record sequence, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordIndex(usize);

impl RecordIndex
{
    /// The first position.
    pub const ZERO: Self = Self(0_usize);

    /// Returns the position one later than this one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the position one above `self` when representable.
    /// - provides: the only way positions advance, so no caller writes the
    ///   increment itself.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] at the numeric ceiling,
    ///   rather than wrapping to zero and aliasing the first position.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the position was at the
    /// numeric ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at zero, an interior position, the last admissible
    ///   increment and the ceiling observes exact positions and overflow
    ///   identity, distinguishing skipped increments, wrapping and premature
    ///   refusal.
    /// - witness: `record::tests::arithmetic_preserves_counts_and_refuses_overflow`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().map(|index| index.0) == self.0.checked_add(1)
        && ret.as_ref().err().is_none_or(|error|
            matches!(error, &RecordTreeError::ArithmeticOverflow { .. })))]
    pub fn next(self) -> Result<Self, RecordTreeError>
    {
        self.0
            .checked_add(1_usize)
            .map(Self)
            .ok_or_else(|| RecordTreeError::ArithmeticOverflow {
                context: "record position".into(),
            })
    }
}

impl From<usize> for RecordIndex
{
    /// Reads a `usize` as a record position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<RecordIndex> for usize
{
    /// Reads the position back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: RecordIndex) -> Self
    {
        index.0
    }
}

impl fmt::Display for RecordIndex
{
    /// Writes the position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried position through the `usize` rendering, so
    ///   the width and fill options the caller set apply to it.
    /// - provides: the position a refusal message names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 at zero, 37 and the primitive ceiling compares padded
    ///   decimal rendering with the primitive; L3 observes exact sink refusal.
    ///   Substituted values, ignored flags and swallowed errors are
    ///   distinguished.
    /// - witness: `record::tests::record_quantities_preserve_formatting_and_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        usize::from(*self).fmt(f)
    }
}

/// A number of records, as committed by a root or a node header.
///
/// The width is `u64` rather than `usize` because the count is a wire field: a
/// 32-bit reader must be able to read and reject a count a 64-bit writer
/// produced, which it cannot do if the count is narrowed on the way in.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordCount(pub u64);

impl RecordCount
{
    /// The empty count.
    pub const ZERO: Self = Self(0_u64);

    /// Counts the records in a slice.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.as_ref().ok().map(|count| u64::from(*count)) ==
    ///   u64::try_from(items.len()).ok()` — the slice length as a wire-width
    ///   count, and a refusal exactly when the length exceeds that width.
    /// - provides: the one conversion from an in-memory length to the committed
    ///   count, so the widening is checked in a single place.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] when a `usize` length
    ///   exceeds the `u64` wire width, which is unreachable on every target
    ///   this crate builds for and is still not assumed away.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the length exceeds `u64`.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on empty and forty-record leaves observes decoded
    ///   records after their length was committed, distinguishing off-by-one
    ///   counts and truncation. Wider-than-u64 slice lengths are not witnessed
    ///   on the supported targets.
    /// - witness: `node::tests::an_empty_leaf_round_trips`
    /// - witness: `node::tests::leaves_round_trip`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().map(|count| u64::from(*count)) == u64::try_from(items.len()).ok())]
    pub fn of_slice<T>(items: &[T]) -> Result<Self, RecordTreeError>
    {
        let Ok(count) = u64::try_from(items.len())
        else {
            return Err(RecordTreeError::ArithmeticOverflow {
                context: "record count does not fit the wire width".into(),
            });
        };

        Ok(Self(count))
    }

    /// Adds another count to this one.
    ///
    /// # Specification
    /// - requires: nothing; both operands may come from adversarial bytes.
    /// - ensures: returns the sum when representable.
    /// - provides: the accumulation an internal node's record total is built
    ///   from.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] on overflow, so a
    ///   crafted node cannot wrap a total into agreement with its header.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the sum exceeds `u64`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, an ordinary sum, the exact ceiling and one
    ///   beyond it observes exact totals and overflow identity, distinguishing
    ///   wrapping, substituted values and premature refusal.
    /// - witness: `record::tests::arithmetic_preserves_counts_and_refuses_overflow`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().map(|count| count.0) == self.0.checked_add(other.0)
        && ret.as_ref().err().is_none_or(|error|
            matches!(error, &RecordTreeError::ArithmeticOverflow { .. })))]
    pub fn plus(
        self,
        other: Self,
    ) -> Result<Self, RecordTreeError>
    {
        self.0
            .checked_add(other.0)
            .map(Self)
            .ok_or_else(|| RecordTreeError::ArithmeticOverflow {
                context: "accumulated record count".into(),
            })
    }
}

impl From<u64> for RecordCount
{
    /// Reads a `u64` as a record count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u64) -> Self
    {
        Self(count)
    }
}

impl From<RecordCount> for u64
{
    /// Reads the count back out as a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: RecordCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for RecordCount
{
    /// Writes the count.
    ///
    /// # Specification
    /// - requires: nothing; a count read out of adversarial bytes renders like
    ///   any other.
    /// - ensures: writes the carried count through the `u64` rendering, so the
    ///   width and fill options the caller set apply to it.
    /// - provides: the count a refusal message names, uninterpreted.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 at zero, 37 and the primitive ceiling compares padded
    ///   decimal rendering with the primitive; L3 observes exact sink refusal.
    ///   Substituted values, ignored flags and swallowed errors are
    ///   distinguished.
    /// - witness: `record::tests::record_quantities_preserve_formatting_and_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        u64::from(*self).fmt(f)
    }
}

/// A borrowed key-value record.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordRef<'record>
{
    /// The record's key.
    key: RecordKey<'record>,
    /// The record's value.
    value: RecordValue<'record>,
}

impl<'record> RecordRef<'record>
{
    /// Borrows a key and a value as one record.
    ///
    /// # Specification
    /// - requires: nothing; the two borrows are independent and neither is read
    ///   as the other.
    /// - ensures: the record carries exactly the key and the value the
    ///   conversions produce, in those roles.
    /// - provides: the pairing that keeps a key and a value distinct at the
    ///   boundary, where both are byte slices.
    /// - fails: never.
    /// - panics: a caller-supplied conversion may panic.
    /// - executable: none — each generic conversion consumes its input and
    ///   exposes no borrowed image to compare with the result.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a one-record canonical leaf observes independent
    ///   bytes and a digest golden, distinguishing lost keys, lost values and
    ///   exchanged roles for the borrowed-byte conversions exercised.
    /// - witness: `node::tests::the_node_identity_is_pinned`
    #[inline]
    #[must_use]
    pub fn new<K, V>(
        key: K,
        value: V,
    ) -> Self
    where
        K: Into<RecordKey<'record>>,
        V: Into<RecordValue<'record>>,
    {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Returns the record's key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn key(&self) -> RecordKey<'record>
    {
        self.key
    }

    /// Returns the record's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn value(&self) -> RecordValue<'record>
    {
        self.value
    }
}

/// An owned key-value record.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Record
{
    /// The record's key.
    key: OwnedRecordKey,
    /// The record's value.
    value: OwnedRecordValue,
}

impl Record
{
    /// Takes ownership of a key and a value as one record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the record owns exactly the key and the value the conversions
    ///   produce, in those roles, so it outlives the borrows it was built from.
    /// - provides: the owned record a built tree holds, since a tree commits to
    ///   its records for as long as it exists.
    /// - fails: never.
    /// - panics: a caller-supplied conversion may panic.
    /// - executable: none — each generic conversion consumes its input and
    ///   exposes no borrowed image to compare with the result.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on three distinct one-byte keys and values observes
    ///   exact point results and an interior selection, distinguishing lost
    ///   values, substituted keys and exchanged roles for byte-array inputs.
    /// - witness: `record::tests::lookup_and_range_read_the_sorted_slice`
    #[inline]
    #[must_use]
    pub fn new<K, V>(
        key: K,
        value: V,
    ) -> Self
    where
        K: Into<OwnedRecordKey>,
        V: Into<OwnedRecordValue>,
    {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Returns the record's key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(&self) -> RecordKey<'_>
    {
        self.key.as_borrowed()
    }

    /// Returns the record's value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(&self) -> RecordValue<'_>
    {
        self.value.as_borrowed()
    }

    /// Borrows this record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_record_ref(&self) -> RecordRef<'_>
    {
        RecordRef::new(self.key(), self.value())
    }
}

impl From<RecordRef<'_>> for Record
{
    /// Takes ownership of a borrowed record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an owned record whose key and value are copies of the
    ///   borrowed ones, in the same roles.
    /// - provides: the crossing a build makes from a caller's borrowed records
    ///   to the sequence the tree keeps.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on forty decoded records compares the recovered
    ///   sequence with the offered borrowed records, distinguishing lost bytes,
    ///   swapped roles and reordered records for that corpus.
    /// - witness: `node::tests::leaves_round_trip`
    #[inline]
    #[spec(ensures: |ret| ret.as_record_ref() == record)]
    fn from(record: RecordRef<'_>) -> Self
    {
        Self::new(record.key(), record.value())
    }
}

/// One end of a key range.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum KeyBound<'key>
{
    /// The range is open on this side.
    Unbounded,
    /// The range includes the named key.
    Included(RecordKey<'key>),
    /// The range stops just short of the named key.
    Excluded(RecordKey<'key>),
}

impl<'key> KeyBound<'key>
{
    /// Builds an inclusive bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a bound that admits the named key itself.
    /// - provides: the inclusive end, distinct from the exclusive one so a
    ///   range's endpoint convention is in the value rather than in a
    ///   convention the caller must remember.
    /// - fails: never.
    /// - panics: a caller-supplied conversion may panic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over all nine endpoint-kind combinations and keys
    ///   before, on, between and after their endpoints observes containment;
    ///   swapped arms and changed equality decisions are distinguished.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret, Self::Included(_)))]
    pub fn included<K>(key: K) -> Self
    where
        K: Into<RecordKey<'key>>,
    {
        Self::Included(key.into())
    }

    /// Builds an exclusive bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a bound that stops just short of the named key.
    /// - provides: the exclusive end, distinct from the inclusive one.
    /// - fails: never.
    /// - panics: a caller-supplied conversion may panic.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over all nine endpoint-kind combinations and keys
    ///   before, on, between and after their endpoints observes containment;
    ///   swapped arms and changed equality decisions are distinguished.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret, Self::Excluded(_)))]
    pub fn excluded<K>(key: K) -> Self
    where
        K: Into<RecordKey<'key>>,
    {
        Self::Excluded(key.into())
    }

    /// Returns the bounding key, when the bound names one.
    ///
    /// # Specification
    /// - requires: nothing; an open bound is admissible.
    /// - ensures: the key an inclusive or exclusive bound names, and nothing
    ///   for an open one.
    /// - provides: the one read the range's own ordering check and containment
    ///   test are both written against.
    /// - fails: yields nothing for an open bound, which is the absence of a
    ///   bounding key rather than a refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over all endpoint kinds and equal or reversed keys
    ///   observes range admission and containment, distinguishing lost keys,
    ///   false open ends and substituted bounding bytes.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    /// - witness: `record::tests::range_rejects_reversed_bounds`
    /// - witness: `record::tests::range_admits_equal_bounds`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_none() == matches!(self, Self::Unbounded))]
    pub const fn key(self) -> Option<RecordKey<'key>>
    {
        match self {
            | Self::Unbounded => None,
            | Self::Included(key) | Self::Excluded(key) => Some(key),
        }
    }
}

/// An owned copy of one end of a key range.
///
/// Proofs commit to the range they answer, so the bound has to outlive the
/// borrowed query it was built from.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum OwnedKeyBound
{
    /// The range is open on this side.
    Unbounded,
    /// The range includes the named key.
    Included(OwnedRecordKey),
    /// The range stops just short of the named key.
    Excluded(OwnedRecordKey),
}

impl OwnedKeyBound
{
    /// Takes ownership of a borrowed bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same arm as `bound`, with an owned copy of its key where
    ///   it names one.
    /// - provides: the bound a proof commits to, which must outlive the
    ///   borrowed query it answers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 through an owned range and back, with L3 across all
    ///   nine endpoint-kind combinations and five ordered query keys, observes
    ///   exact containment and distinguishes lost keys or changed bound kinds.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.as_bound() == bound)]
    pub fn from_bound(bound: KeyBound<'_>) -> Self
    {
        match bound {
            | KeyBound::Unbounded => Self::Unbounded,
            | KeyBound::Included(key) => Self::Included(OwnedRecordKey::from(key)),
            | KeyBound::Excluded(key) => Self::Excluded(OwnedRecordKey::from(key)),
        }
    }

    /// Borrows this bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same arm as `self`, borrowing its key where it names one,
    ///   so the round trip through ownership changes no arm.
    /// - provides: the borrowed form the containment test reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 through an owned range and back, with L3 across all
    ///   nine endpoint-kind combinations and five ordered query keys, observes
    ///   exact containment and distinguishes lost keys or changed bound kinds.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self {
        Self::Unbounded => ret == KeyBound::Unbounded,
        Self::Included(ref key) => ret == KeyBound::Included(key.as_borrowed()),
        Self::Excluded(ref key) => ret == KeyBound::Excluded(key.as_borrowed()),
    })]
    pub fn as_bound(&self) -> KeyBound<'_>
    {
        match *self {
            | Self::Unbounded => KeyBound::Unbounded,
            | Self::Included(ref key) => KeyBound::Included(key.as_borrowed()),
            | Self::Excluded(ref key) => KeyBound::Excluded(key.as_borrowed()),
        }
    }
}

/// A borrowed key range with non-reversed endpoints.
///
/// The type exists so that a reversed range is rejected once, at construction,
/// rather than silently producing an empty answer at every consumer.
///
/// # Specification
/// - requires: nothing; constructors check the endpoint relation.
/// - ensures: named endpoints are nondecreasing; equal endpoints may denote an
///   empty query when either end is exclusive.
/// - provides: a query whose ordering has already been checked.
/// - fails: never, once constructed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on equal and reversed endpoint pairs observes refinement
///   admission, empty containment and exact refusal. These distinguish
///   too-strict and too-loose admission without requiring every query to
///   contain a key.
/// - witness: `record::tests::range_rejects_reversed_bounds`
/// - witness: `record::tests::range_admits_equal_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[spec(maintains: self.start.key().zip(self.end.key())
    .is_none_or(|(lower, upper)| lower <= upper))]
pub struct KeyRange<'key>
{
    /// The lower end.
    start: KeyBound<'key>,
    /// The upper end.
    end: KeyBound<'key>,
}

impl<'key> KeyRange<'key>
{
    /// Builds a range after rejecting a reversed one.
    ///
    /// # Specification
    /// - requires: nothing; both bounds are arbitrary.
    /// - ensures: `|ret| ret.is_ok() == start.key().zip(end.key())
    ///   .is_none_or(|(lower, upper)| lower <= upper)` — on success the bounds
    ///   are not strictly reversed, so a range value never denotes a query
    ///   whose ends contradict each other.
    /// - provides: the only constructor for a bounded range, so no consumer has
    ///   to re-check the relation.
    /// - fails: [`RecordTreeError::InvalidRange`] when both ends name keys and
    ///   the lower key sorts after the upper one.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidRange`] — the bounds are reversed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the guard's decision surface is the comparison
    ///   of the two keys, separated by the equal-key boundary (accepted, since
    ///   an empty half-open range is a legitimate query) and the adjacent
    ///   strictly-greater case (rejected).
    /// - witness: `record::tests::range_rejects_reversed_bounds`
    /// - witness: `record::tests::range_admits_equal_bounds`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == start.key().zip(end.key()).is_none_or(|(lower, upper)| lower <= upper)
        && ret.as_ref().map_or(true, |range| range.start == start && range.end == end))]
    pub fn new(
        start: KeyBound<'key>,
        end: KeyBound<'key>,
    ) -> Result<Self, RecordTreeError>
    {
        if let (Some(start_key), Some(end_key)) = (start.key(), end.key())
            && start_key > end_key
        {
            return Err(RecordTreeError::InvalidRange {
                context: "lower bound sorts after upper bound".into(),
            });
        }

        Ok(Self { start, end })
    }

    /// Builds the range that admits every key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: both ends open, so every key lies inside.
    /// - provides: the whole-tree query, minted without the ordering check
    ///   because an open pair cannot be inverted.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over five ordered query keys observes unrestricted
    ///   containment; an end-to-end proof returns all 300 corpus records. These
    ///   distinguish bounded substitutions on the observed domains, not every
    ///   possible byte string.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    /// - witness: `tests::range::the_unbounded_range_proves`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret.start, KeyBound::Unbounded)
        && matches!(ret.end, KeyBound::Unbounded))]
    pub const fn all() -> Self
    {
        Self {
            start: KeyBound::Unbounded,
            end: KeyBound::Unbounded,
        }
    }

    /// Returns the lower end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> KeyBound<'key>
    {
        self.start
    }

    /// Returns the upper end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> KeyBound<'key>
    {
        self.end
    }

    /// Reports whether `key` lies inside this range.
    ///
    /// # Specification
    /// - requires: nothing; every key is admissible, and an open end admits
    ///   every key on its side.
    /// - ensures: [`RangeContainment::Inside`] exactly when `key` is at or
    ///   above an inclusive lower end, strictly above an exclusive one, and
    ///   symmetrically at the upper end; keys compare by their bytes in
    ///   lexicographic order, which is the order the tree is built in.
    /// - provides: the containment decision a range query and a range proof are
    ///   both checked against, as a named pair of states rather than a bare
    ///   `bool`.
    /// - fails: never — being outside the range is an answer, not a refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on all nine endpoint-kind pairs and query keys before,
    ///   on, between and after the endpoints observes a literal membership
    ///   table, distinguishing wrong inequalities, ignored bounds and swapped
    ///   lower/upper roles. Equal endpoints also witness an empty interval.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    /// - witness: `record::tests::range_admits_equal_bounds`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| (ret == RangeContainment::Inside)
        == ((match self.start {
            KeyBound::Unbounded => true,
            KeyBound::Included(start) => key >= start,
            KeyBound::Excluded(start) => key > start,
        }) && (match self.end {
            KeyBound::Unbounded => true,
            KeyBound::Included(end) => key <= end,
            KeyBound::Excluded(end) => key < end,
        })))]
    pub fn contains(
        &self,
        key: RecordKey<'_>,
    ) -> RangeContainment
    {
        let above_start = match self.start {
            | KeyBound::Unbounded => true,
            | KeyBound::Included(start) => key.as_ref() >= start.as_ref(),
            | KeyBound::Excluded(start) => key.as_ref() > start.as_ref(),
        };

        if !above_start {
            return RangeContainment::Outside;
        }

        let below_end = match self.end {
            | KeyBound::Unbounded => true,
            | KeyBound::Included(end) => key.as_ref() <= end.as_ref(),
            | KeyBound::Excluded(end) => key.as_ref() < end.as_ref(),
        };

        if below_end {
            RangeContainment::Inside
        }
        else {
            RangeContainment::Outside
        }
    }
}

/// An owned key range with non-reversed endpoints.
///
/// # Specification
/// - requires: nothing; ownership starts from a checked borrowed range.
/// - ensures: both endpoint kinds and bytes survive ownership; their named keys
///   remain nondecreasing.
/// - provides: a query a proof can retain after the original borrow ends.
/// - fails: never, once constructed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 through ownership and back and L3 on nine endpoint-kind
///   pairs with five ordered queries observe expected containment. A privately
///   reversed pair has a false refinement and an exact borrowing refusal.
///   Swapped endpoints, erased exclusivity and lost bytes are distinguished.
/// - witness: `record::tests::range_containment_respects_each_bound_kind`
/// - witness: `record::tests::range_rejects_reversed_bounds`
#[derive(Clone, Debug, Eq, PartialEq)]
#[spec(maintains: self.start.as_bound().key().zip(self.end.as_bound().key())
    .is_none_or(|(lower, upper)| lower <= upper))]
pub struct OwnedKeyRange
{
    /// The lower end.
    start: OwnedKeyBound,
    /// The upper end.
    end: OwnedKeyBound,
}

impl OwnedKeyRange
{
    /// Takes ownership of a borrowed range.
    ///
    /// # Specification
    /// - requires: `range` was minted by [`KeyRange::new`] or
    ///   [`KeyRange::all`], so its ends are ordered; the ordering is not
    ///   re-checked here and [`OwnedKeyRange::as_range`] re-checks it on the
    ///   way back.
    /// - ensures: both ends owned, each the same arm as the borrowed one.
    /// - provides: the range a proof commits to, which must outlive the query
    ///   it answers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 through ownership and back, with L3 on nine bound
    ///   combinations and five ordered queries, observes literal containment
    ///   and distinguishes lost bound kinds, endpoint swaps and substituted
    ///   bytes.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.start.as_bound() == range.start()
        && ret.end.as_bound() == range.end())]
    pub fn from_range(range: KeyRange<'_>) -> Self
    {
        Self {
            start: OwnedKeyBound::from_bound(range.start()),
            end: OwnedKeyBound::from_bound(range.end()),
        }
    }

    /// Borrows this range, re-checking the bound relation.
    ///
    /// # Specification
    /// - requires: nothing; the endpoint relation is checked again even for an
    ///   already-owned range.
    /// - ensures: `|ret| ret.is_ok() ==
    ///   self.start.as_bound().key().zip(self.end.as_bound().key())
    ///   .is_none_or(|(lower, upper)| lower <= upper)` — the returned range
    ///   satisfies [`KeyRange::new`]'s guarantee.
    /// - provides: the re-entry point from carried proof material back into the
    ///   checked range type.
    /// - fails: [`RecordTreeError::InvalidRange`] when the carried bounds are
    ///   reversed.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidRange`] — the carried bounds are reversed.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on nine owned bound-kind combinations and L3 on five
    ///   query positions observe literal containment. A privately reversed pair
    ///   yields the exact range error. These distinguish lost exclusivity,
    ///   swapped bounds and trusting malformed carried bounds.
    /// - witness: `record::tests::range_containment_respects_each_bound_kind`
    /// - witness: `record::tests::range_rejects_reversed_bounds`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == self
            .start
            .as_bound()
            .key()
            .zip(self.end.as_bound().key())
            .is_none_or(|(lower, upper)| lower <= upper)
        && ret.as_ref().map_or(true, |range| range.start() == self.start.as_bound()
            && range.end() == self.end.as_bound()))]
    pub fn as_range(&self) -> Result<KeyRange<'_>, RecordTreeError>
    {
        KeyRange::new(self.start.as_bound(), self.end.as_bound())
    }
}

/// Whether a key lies inside a range.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RangeContainment
{
    /// The key lies inside.
    Inside,
    /// The key lies outside.
    Outside,
}

/// Whether a key sequence is strictly increasing.
///
/// # Specification
/// - requires: nothing; the sequence is caller-supplied and arbitrary.
/// - ensures: on success every adjacent pair is strictly increasing, which is
///   the precondition every encoder and every leaf decoder relies on.
/// - provides: one order check shared by the builder and by the node decoder,
///   so admitted bytes and admitted inputs obey the same rule. The predicate
///   checks adjacent refusal positions; the consumed sequence cannot be
///   replayed without strengthening the iterator contract.
/// - fails: [`RecordTreeError::DuplicateKeys`] on an equal adjacent pair,
///   [`RecordTreeError::UnsortedInput`] on a decreasing one, and
///   [`RecordTreeError::ArithmeticOverflow`] when the position counter reaches
///   its ceiling, which an [`IntoIterator`] can reach because the trait bounds
///   no length. The first two are distinguished because a duplicate is a caller
///   error and a decrease is usually a corrupt or hostile input.
/// - panics: a caller-supplied iterator may panic.
///
/// # Errors
/// [`RecordTreeError::DuplicateKeys`] — two adjacent records share a key.
/// [`RecordTreeError::UnsortedInput`] — a record's key sorts before its
/// predecessor's.
/// [`RecordTreeError::ArithmeticOverflow`] — the sequence yielded more keys
/// than a record position can count.
///
/// # Adequacy
/// - hypothesis: L3 on increasing, equal and decreasing adjacent keys in
///   three-key sequences observes exact refusal classes and positions,
///   distinguishing ignored comparisons, misclassified failures and shifted
///   indices. Arbitrary iterators and counter exhaustion are not exhausted.
/// - witness: `record::tests::sorted_keys_are_admitted`
/// - witness: `record::tests::equal_adjacent_keys_are_duplicates`
/// - witness: `record::tests::decreasing_keys_are_unsorted`
#[inline]
#[spec(ensures: |ret| ret.as_ref().err().is_none_or(|error| match *error {
    RecordTreeError::DuplicateKeys { first, second } =>
        first.0.checked_add(1) == Some(second.0),
    RecordTreeError::UnsortedInput { previous, current } =>
        previous.0.checked_add(1) == Some(current.0),
    RecordTreeError::ArithmeticOverflow { .. } => true,
    _ => false,
}))]
pub fn ensure_strictly_sorted<'key, K>(keys: K) -> Result<(), RecordTreeError>
where
    K: IntoIterator<Item = RecordKey<'key>>,
{
    let mut previous: Option<RecordKey<'key>> = None;
    let mut previous_index = RecordIndex::ZERO;
    let mut current_index = RecordIndex::ZERO;

    for key in keys {
        if let Some(earlier) = previous {
            match earlier.cmp(&key) {
                | Ordering::Less => {},
                | Ordering::Equal => {
                    return Err(RecordTreeError::DuplicateKeys {
                        first: previous_index,
                        second: current_index,
                    });
                },
                | Ordering::Greater => {
                    return Err(RecordTreeError::UnsortedInput {
                        previous: previous_index,
                        current: current_index,
                    });
                },
            }
        }

        previous = Some(key);
        previous_index = current_index;
        current_index = current_index.next()?;
    }

    Ok(())
}

/// Finds the record carrying `key` in a sorted record slice.
///
/// The search is binary over the strictly increasing slice, so presence and
/// absence both cost a logarithmic number of comparisons.
///
/// # Specification
/// - requires: `records` is sorted by strictly increasing key.
/// - ensures: `|ret| ret == records.iter().find(|record| record.key() == key)`
///   — exactly the record that carries `key`, when one exists, which a linear
///   scan decides independently of the binary search.
/// - provides: the logarithmic point lookup the proof builders select from.
/// - fails: none — absence is reported as `None`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on three sorted records and queries at every key, both
///   outer gaps and the two inner gaps observes literal values or absence,
///   distinguishing wrong insertion positions and mismatched records.
/// - witness: `record::tests::lookup_and_range_read_the_sorted_slice`
#[must_use]
#[spec(ensures: |ret| ret == records.iter().find(|record| record.key() == key))]
pub(crate) fn find_record<'record>(
    records: &'record [Record],
    key: RecordKey<'_>,
) -> Option<&'record Record>
{
    let position = records
        .binary_search_by(|record| record.key().cmp(&key))
        .ok()?;

    records.get(position)
}

/// Copies the records of a sorted slice that lie inside `range`.
///
/// # Specification
/// - requires: `records` is sorted by strictly increasing key.
/// - ensures: `|ret| ret.iter().eq(records.iter().filter(|record|
///   range.contains(record.key()) == RangeContainment::Inside))` — exactly the
///   records inside `range`, in slice order, which an unfiltered scan decides
///   independently of the early break.
/// - provides: the linear interval query that range-proof collection walks.
/// - fails: none — a key outside the range is data, not an error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 against the offered slice on an interior interval observes
///   the exact retained record; lower-prefix skipping and an upper overshoot
///   distinguish premature stopping, omitted records and leakage.
/// - witness: `record::tests::lookup_and_range_read_the_sorted_slice`
#[must_use]
#[spec(ensures: |ret| ret
    .iter()
    .eq(records.iter().filter(|record| range.contains(record.key()) == RangeContainment::Inside)))]
pub(crate) fn select_in_range(
    records: &[Record],
    range: KeyRange<'_>,
) -> Box<[Record]>
{
    let mut selected = Vec::<Record>::new();

    for record in records {
        match range.contains(record.key()) {
            | RangeContainment::Inside => selected.push(record.clone()),
            | RangeContainment::Outside => {
                // The slice is sorted, so a key past the range's upper end
                // outruns every key after it, and the scan may stop.
                let past_end = range.end().key().is_some_and(|end| record.key() > end);

                if past_end {
                    break;
                }
            },
        }
    }

    selected.into_boxed_slice()
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use core::fmt;
    use core::fmt::Write as _;

    use anodized::spec;

    use super::KeyBound;
    use super::KeyRange;
    use super::OwnedKeyBound;
    use super::OwnedKeyRange;
    use super::RangeContainment;
    use super::Record;
    use super::RecordCount;
    use super::RecordIndex;
    use super::ensure_strictly_sorted;
    use super::find_record;
    use super::select_in_range;
    use crate::bytes::RecordKey;
    use crate::error::RecordTreeError;

    #[test]
    fn sorted_keys_are_admitted()
    {
        let keys = vec![
            RecordKey::from(b"a"),
            RecordKey::from(b"b"),
            RecordKey::from(b"c"),
        ];

        assert_eq!(ensure_strictly_sorted(keys), Ok(()));
    }

    #[test]
    fn equal_adjacent_keys_are_duplicates()
    {
        let keys = vec![
            RecordKey::from(b"a"),
            RecordKey::from(b"b"),
            RecordKey::from(b"b"),
        ];

        assert_eq!(
            ensure_strictly_sorted(keys),
            Err(RecordTreeError::DuplicateKeys {
                first: RecordIndex::from(1_usize),
                second: RecordIndex::from(2_usize),
            })
        );
    }

    #[test]
    fn decreasing_keys_are_unsorted()
    {
        let keys = vec![
            RecordKey::from(b"a"),
            RecordKey::from(b"c"),
            RecordKey::from(b"b"),
        ];

        assert_eq!(
            ensure_strictly_sorted(keys),
            Err(RecordTreeError::UnsortedInput {
                previous: RecordIndex::from(1_usize),
                current: RecordIndex::from(2_usize),
            })
        );
    }

    #[test]
    fn range_rejects_reversed_bounds()
    {
        let start = KeyBound::included(b"b");
        let end = KeyBound::included(b"a");
        let borrowed = KeyRange { start, end };
        let owned = OwnedKeyRange {
            start: OwnedKeyBound::from_bound(start),
            end: OwnedKeyBound::from_bound(end),
        };
        assert!(!anodized::types::Spec::predicate(&borrowed));
        assert!(!anodized::types::Spec::predicate(&owned));
        let expected = Err(RecordTreeError::InvalidRange {
            context: "lower bound sorts after upper bound".into(),
        });
        assert_eq!(KeyRange::new(start, end), expected);
        assert_eq!(owned.as_range(), expected);
    }

    #[test]
    fn range_admits_equal_bounds()
    {
        let range = KeyRange::new(KeyBound::included(b"b"), KeyBound::excluded(b"b"))
            .expect("equal bounds are not reversed");

        assert!(anodized::types::Spec::predicate(&range));
        assert_eq!(
            range.contains(RecordKey::from(b"b")),
            RangeContainment::Outside
        );
    }

    #[test]
    fn range_containment_respects_each_bound_kind()
    {
        for (start, end, expected) in [
            (
                KeyBound::Unbounded,
                KeyBound::Unbounded,
                b"abcde".as_slice(),
            ),
            (
                KeyBound::Unbounded,
                KeyBound::included(b"d"),
                b"abcd".as_slice(),
            ),
            (
                KeyBound::Unbounded,
                KeyBound::excluded(b"d"),
                b"abc".as_slice(),
            ),
            (
                KeyBound::included(b"b"),
                KeyBound::Unbounded,
                b"bcde".as_slice(),
            ),
            (
                KeyBound::included(b"b"),
                KeyBound::included(b"d"),
                b"bcd".as_slice(),
            ),
            (
                KeyBound::included(b"b"),
                KeyBound::excluded(b"d"),
                b"bc".as_slice(),
            ),
            (
                KeyBound::excluded(b"b"),
                KeyBound::Unbounded,
                b"cde".as_slice(),
            ),
            (
                KeyBound::excluded(b"b"),
                KeyBound::included(b"d"),
                b"cd".as_slice(),
            ),
            (
                KeyBound::excluded(b"b"),
                KeyBound::excluded(b"d"),
                b"c".as_slice(),
            ),
        ] {
            let range = if start == KeyBound::Unbounded && end == KeyBound::Unbounded {
                KeyRange::all()
            }
            else {
                KeyRange::new(start, end).expect("the bounds are ordered")
            };
            let owned = OwnedKeyRange::from_range(range);
            let borrowed = owned.as_range().expect("ownership preserves ordering");
            assert!(anodized::types::Spec::predicate(&range));
            assert!(anodized::types::Spec::predicate(&owned));
            assert!(anodized::types::Spec::predicate(&borrowed));
            for key in b"abcde" {
                let expected = if expected.contains(key) {
                    RangeContainment::Inside
                }
                else {
                    RangeContainment::Outside
                };
                let key = RecordKey::from(core::slice::from_ref(key));
                assert_eq!(range.contains(key), expected);
                assert_eq!(borrowed.contains(key), expected);
            }
        }
    }

    #[test]
    fn lookup_and_range_read_the_sorted_slice()
    {
        let records = vec![
            Record::new(b"a", b"1"),
            Record::new(b"c", b"3"),
            Record::new(b"e", b"5"),
        ];

        for (key, expected) in [
            (b"".as_slice(), None),
            (b"a".as_slice(), Some(b"1".as_slice())),
            (b"b".as_slice(), None),
            (b"c".as_slice(), Some(b"3".as_slice())),
            (b"d".as_slice(), None),
            (b"e".as_slice(), Some(b"5".as_slice())),
            (b"z".as_slice(), None),
        ] {
            assert_eq!(
                find_record(records.as_slice(), RecordKey::from(key)).map(Record::value),
                expected.map(crate::bytes::RecordValue::from)
            );
        }

        let range = KeyRange::new(KeyBound::included(b"b"), KeyBound::included(b"d"))
            .expect("bounds are ordered");
        let selected = select_in_range(records.as_slice(), range);
        assert_eq!(selected.as_ref(), &records[1 .. 2]);
    }

    #[test]
    fn arithmetic_preserves_counts_and_refuses_overflow()
    {
        for (raw, expected) in [(0_usize, 1_usize), (7, 8), (usize::MAX - 1, usize::MAX)] {
            assert_eq!(
                RecordIndex::from(raw).next(),
                Ok(RecordIndex::from(expected))
            );
        }
        assert!(matches!(
            RecordIndex::from(usize::MAX).next(),
            Err(RecordTreeError::ArithmeticOverflow { .. })
        ));
        for (left, right, expected) in [
            (0_u64, 0_u64, 0_u64),
            (7, 11, 18),
            (u64::MAX - 1, 1, u64::MAX),
        ] {
            assert_eq!(
                RecordCount::from(left).plus(RecordCount::from(right)),
                Ok(RecordCount::from(expected))
            );
        }
        assert!(matches!(
            RecordCount::from(u64::MAX).plus(RecordCount::from(1_u64)),
            Err(RecordTreeError::ArithmeticOverflow { .. })
        ));
    }

    #[test]
    fn record_quantities_preserve_formatting_and_refusal()
    {
        for raw in [0_usize, 37, usize::MAX] {
            let index = RecordIndex::from(raw);
            assert_eq!(alloc::format!("{index:024}"), alloc::format!("{raw:024}"));
            assert_eq!(write!(RefusingSink, "{index}"), Err(fmt::Error));
        }
        for raw in [0_u64, 37, u64::MAX] {
            let count = RecordCount::from(raw);
            assert_eq!(alloc::format!("{count:024}"), alloc::format!("{raw:024}"));
            assert_eq!(write!(RefusingSink, "{count}"), Err(fmt::Error));
        }
    }

    /// A sink that refuses every write.
    struct RefusingSink;

    impl fmt::Write for RefusingSink
    {
        /// Refuses the offered text.
        ///
        /// # Specification
        /// - requires: nothing; any text is admissible.
        /// - ensures: returns the formatter's error for every write.
        /// - provides: a refusal observer for quantity formatting.
        /// - fails: always returns the formatter's error.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on decimal quantity writes observes the exact
        ///   error, distinguishing a sink that silently accepts a write.
        /// - witness: `record::tests::record_quantities_preserve_formatting_and_refusal`
        #[spec(ensures: |ret| ret == Err(fmt::Error))]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> fmt::Result
        {
            Err(fmt::Error)
        }
    }
}
