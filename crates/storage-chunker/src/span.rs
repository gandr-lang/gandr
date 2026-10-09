//! What a scan returns: half-open spans and the reason each one ended.

use crate::units::BytePosition;
use crate::units::RecordPosition;

/// Why a chunk ended where it did.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BoundaryReason
{
    /// The content predicate fired: the Gear state masked to zero after a
    /// complete record, or a boundary event's residue was divisible by kappa.
    HashPredicate,
    /// The hard byte cap ended the chunk after a complete record.
    MaxByteCap,
    /// The hard record cap ended the chunk after a complete record.
    MaxRecordCap,
    /// The hard token cap ended the chunk at a boundary event.
    MaxTokenCap,
    /// The input ended with a non-empty chunk still open.
    FinalRemainder,
}

/// A half-open run of positions in a canonical byte stream.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteSpan
{
    /// The first position in the run.
    start: BytePosition,
    /// One past the last position in the run.
    end: BytePosition,
}

impl ByteSpan
{
    /// Pairs a start with an end.
    ///
    /// # Specification
    /// - requires: nothing; an inverted pair is representable, and the scan
    ///   that reads spans refuses one by name.
    /// - ensures: the span carries both positions unchanged.
    /// - provides: the shape a caller states its record edges in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on arbitrary position pairs, witnessed by ordered,
    ///   equal and inverted edges; partition results and exact rejection
    ///   variants distinguish swapped endpoints and premature normalization.
    /// - witness: `tests::gear::span_lists_that_are_not_a_partition_are_refused`
    /// - witness: `tests::gear::empty_records_keep_their_record_positions`
    #[anodized::spec(ensures: |ret| matches!(ret.start.const_eq(start), crate::units::ConstEquality::Equal) && matches!(ret.end.const_eq(end), crate::units::ConstEquality::Equal))]
    #[inline]
    #[must_use]
    pub const fn new(
        start: BytePosition,
        end: BytePosition,
    ) -> Self
    {
        Self { start, end }
    }

    /// Returns the first position in the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> BytePosition
    {
        self.start
    }

    /// Returns one past the last position in the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> BytePosition
    {
        self.end
    }
}

/// A half-open run of positions in canonical record order.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RecordSpan
{
    /// The first position in the run.
    start: RecordPosition,
    /// One past the last position in the run.
    end: RecordPosition,
}

impl RecordSpan
{
    /// Pairs a start with an end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        start: RecordPosition,
        end: RecordPosition,
    ) -> Self
    {
        Self { start, end }
    }

    /// Returns the first position in the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> RecordPosition
    {
        self.start
    }

    /// Returns one past the last position in the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> RecordPosition
    {
        self.end
    }
}

/// One chunk of a record-safe scan: its bytes, its records, and why it ended.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ChunkSpan
{
    /// The bytes the chunk covers.
    bytes: ByteSpan,
    /// The records the chunk covers.
    records: RecordSpan,
    /// Why the chunk ended.
    reason: BoundaryReason,
}

impl ChunkSpan
{
    /// Assembles a chunk from its two spans and its reason.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        bytes: ByteSpan,
        records: RecordSpan,
        reason: BoundaryReason,
    ) -> Self
    {
        Self {
            bytes,
            records,
            reason,
        }
    }

    /// Returns the bytes the chunk covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bytes(&self) -> ByteSpan
    {
        self.bytes
    }

    /// Returns the records the chunk covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn records(&self) -> RecordSpan
    {
        self.records
    }

    /// Returns why the chunk ended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reason(&self) -> BoundaryReason
    {
        self.reason
    }
}
