//! Limits, corpora and partition checks the area suites share.

use gandr_storage_chunker::ByteCount;
use gandr_storage_chunker::BytePosition;
use gandr_storage_chunker::ByteSpan;
use gandr_storage_chunker::CanonicalBytes;
use gandr_storage_chunker::CanonicalRecords;
use gandr_storage_chunker::ChunkLimits;
use gandr_storage_chunker::ChunkSpan;
use gandr_storage_chunker::ChunkerParams;
use gandr_storage_chunker::GearTableVersion;
use gandr_storage_chunker::NormalizationPolicy;
use gandr_storage_chunker::RecordBoundaryRule;
use gandr_storage_chunker::RecordCount;
use gandr_storage_chunker::RecordPosition;
use gandr_storage_chunker::SeedPolicy;

/// Builds limits from minimum, target and maximum byte limits and the same
/// three record limits.
///
/// # Specification
/// - requires: the six limits are valid; a fixture that needs a refusal calls
///   [`ChunkLimits::new`] itself.
/// - ensures: the limits carry exactly the six values.
/// - provides: one line per fixture's limits.
/// - panics: when the limits are refused, which is a fixture defect.
pub fn limits(
    bytes: [ByteCount; 3],
    records: [RecordCount; 3],
) -> ChunkLimits
{
    let [min_bytes, target_bytes, max_bytes] = bytes;
    let [min_records, target_records, max_records] = records;

    ChunkLimits::new(
        min_bytes,
        target_bytes,
        max_bytes,
        min_records,
        target_records,
        max_records,
    )
    .expect("a fixture's limits are valid")
}

/// Builds the unsalted version-1 record-safe profile over `limits`.
///
/// # Specification
/// trivial.
pub const fn params(limits: ChunkLimits) -> ChunkerParams
{
    ChunkerParams::new(
        GearTableVersion::V1,
        SeedPolicy::Unsalted,
        NormalizationPolicy::PreserveBytes,
        RecordBoundaryRule::BetweenRecords,
        limits,
    )
}

/// Records concatenated into one canonical buffer.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Concatenated(Vec<u8>);

impl Concatenated
{
    /// Concatenates `records` in order.
    ///
    /// # Specification
    /// trivial.
    pub fn of(records: CanonicalRecords<'_>) -> Self
    {
        Self(records.as_ref().concat())
    }

    /// Borrows the buffer as canonical bytes.
    ///
    /// # Specification
    /// trivial.
    pub fn bytes(&self) -> CanonicalBytes<'_>
    {
        CanonicalBytes::from(self.0.as_slice())
    }
}

/// Returns the byte span each record occupies in the concatenated buffer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one span per record, in order, each starting where the previous
///   ended and the first at zero.
/// - provides: the record edges a partition check compares chunk edges with.
/// - panics: never for fixture-sized input.
pub fn record_spans(records: CanonicalRecords<'_>) -> Vec<ByteSpan>
{
    let mut start = 0_u64;

    records
        .as_ref()
        .iter()
        .map(|record| {
            let length = u64::try_from(record.len()).expect("a fixture record fits u64");
            let end = start.checked_add(length).expect("a fixture fits u64");
            let span = ByteSpan::new(BytePosition::from(start), BytePosition::from(end));
            start = end;
            span
        })
        .collect()
}

/// Returns the byte length of a chunk.
///
/// # Specification
/// trivial.
pub fn byte_len(chunk: &ChunkSpan) -> ByteCount
{
    let bytes = chunk.bytes();
    let length = u64::from(bytes.end())
        .checked_sub(u64::from(bytes.start()))
        .expect("a chunk's byte span is ordered");

    ByteCount::from(length)
}

/// Returns the record count of a chunk.
///
/// # Specification
/// trivial.
pub fn record_len(chunk: &ChunkSpan) -> RecordCount
{
    let records = chunk.records();
    let length = u64::from(records.end())
        .checked_sub(u64::from(records.start()))
        .expect("a chunk's record span is ordered");

    RecordCount::from(u32::try_from(length).expect("a fixture chunk's records fit u32"))
}

/// Asserts that `chunks` partition `records` exactly, on record edges.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns only when every chunk is non-empty, each starts where the
///   previous ended in both bytes and records, the first at zero, the last at
///   the input's end, and every chunk's byte edges are the byte edges of its
///   first and last records.
/// - provides: the partition invariant every record-safe scan owes, checked
///   against the records rather than against the scan's own arithmetic.
/// - panics: when any of those fails, naming the chunk.
pub fn assert_partition(
    chunks: &[ChunkSpan],
    records: CanonicalRecords<'_>,
)
{
    let spans = record_spans(records);
    let index = |position: RecordPosition| {
        usize::try_from(u64::from(position)).expect("a fixture position fits usize")
    };
    let mut byte = BytePosition::ZERO;
    let mut record = RecordPosition::ZERO;

    for (position, chunk) in chunks.iter().enumerate() {
        let first = index(chunk.records().start());
        let last = index(chunk.records().end())
            .checked_sub(1)
            .expect("a chunk holds at least one record");

        assert_eq!(
            chunk.bytes().start(),
            byte,
            "chunk {position} starts at the last end"
        );
        assert_eq!(
            chunk.records().start(),
            record,
            "chunk {position} starts at the last record"
        );
        assert_eq!(
            chunk.bytes().start(),
            spans[first].start(),
            "chunk {position} starts on its first record's edge"
        );
        assert_eq!(
            chunk.bytes().end(),
            spans[last].end(),
            "chunk {position} ends on its last record's edge"
        );

        byte = chunk.bytes().end();
        record = chunk.records().end();
    }

    let end = spans.last().map_or(BytePosition::ZERO, ByteSpan::end);
    let count = u64::try_from(spans.len()).expect("a fixture's record count fits u64");
    assert_eq!(byte, end, "the chunks cover every byte");
    assert_eq!(
        record,
        RecordPosition::from(count),
        "the chunks cover every record"
    );
}

/// Asserts that every chunk sits within the hard caps of `limits`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns only when no chunk exceeds the byte cap or the record
///   cap.
/// - provides: the cap invariant every record-safe scan owes.
/// - panics: when a chunk exceeds a cap, naming it.
pub fn assert_within_caps(
    chunks: &[ChunkSpan],
    limits: &ChunkLimits,
)
{
    for (position, chunk) in chunks.iter().enumerate() {
        assert!(
            byte_len(chunk) <= limits.max_bytes(),
            "chunk {position} is within the byte cap"
        );
        assert!(
            record_len(chunk) <= limits.max_records(),
            "chunk {position} is within the record cap"
        );
    }
}
