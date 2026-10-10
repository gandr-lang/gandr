//! Limits, corpora and partition checks the area suites share.

use anodized::spec;
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
///
/// # Adequacy
/// - hypothesis: L3 on valid cap and minimum fixtures; emitted spans and cut
///   reasons separate substitutions of the limits those corpora exercise.
/// - witness: `tests::gear::the_caps_force_their_reasons`
/// - witness: `tests::gear::minimum_limits_suppress_an_early_hash_cut`
#[spec(
    requires: {
        let [min, target, max] = bytes;
        let [min_records, target_records, max_records] = records;
        min > ByteCount::ZERO && min <= target && target <= max
            && u32::try_from(u64::from(target)).is_ok()
            && min_records > RecordCount::ZERO && min_records <= target_records && target_records <= max_records
    },
    ensures: |ret| [ret.min_bytes(), ret.target_bytes(), ret.max_bytes()] == bytes
        && [ret.min_records(), ret.target_records(), ret.max_records()] == records,
)]
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
/// - panics: when a record length or accumulated fixture length exceeds u64.
///
/// # Adequacy
/// - hypothesis: L2 on empty and nonuniform records including empty records;
///   exact prefix spans distinguish omitted lengths, gaps and off-by-one edges.
/// - witness: `tests::common::record_edges_match_independent_prefixes`
#[spec(ensures: |ret| {
    let mut expected = 0_u64;
    ret.len() == records.as_ref().len() && ret.iter().zip(records.as_ref()).all(|(span, record)| {
        let start = expected;
        let Some(end) = u64::try_from(record.len()).ok().and_then(|len| start.checked_add(len)) else { return false; };
        expected = end;
        u64::from(span.start()) == start && u64::from(span.end()) == end
    })
})]
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
/// - requires: the chunk's byte endpoints are ordered.
/// - ensures: the exact nonnegative difference of the endpoints.
/// - provides: a byte-length observer independent of scanner counters.
/// - fails: none.
/// - panics: when the endpoints are inverted.
///
/// # Adequacy
/// - hypothesis: L3 at empty, interior and maximum-width differences; exact
///   lengths distinguish reversed subtraction and narrowing.
/// - witness: `tests::common::length_observers_preserve_empty_and_width_boundaries`
#[spec(
    requires: chunk.bytes().end() >= chunk.bytes().start(),
    ensures: |ret| u64::from(chunk.bytes().start()).checked_add(u64::from(ret)) == Some(u64::from(chunk.bytes().end())),
)]
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
/// - requires: the record endpoints are ordered and their difference fits u32.
/// - ensures: the exact nonnegative difference of the endpoints.
/// - provides: a record-count observer independent of scanner counters.
/// - fails: none.
/// - panics: when endpoints are inverted or the difference exceeds u32.
///
/// # Adequacy
/// - hypothesis: L3 at empty, interior and maximum-width differences; exact
///   counts distinguish reversed subtraction and narrowing.
/// - witness: `tests::common::length_observers_preserve_empty_and_width_boundaries`
#[spec(
    requires: u64::from(chunk.records().end()).checked_sub(u64::from(chunk.records().start()))
        .is_some_and(|len| u32::try_from(len).is_ok()),
    ensures: |ret| u64::from(chunk.records().start()).checked_add(u64::from(u32::from(ret))) == Some(u64::from(chunk.records().end())),
)]
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
///
/// # Adequacy
/// - hypothesis: L1 on record-safe corpora and L3 at missing prefixes, wrong
///   record edges, missing suffixes and empty record ranges between valid
///   empty-byte records; acceptance and rejection separate coverage, alignment
///   and positivity mutations without confusing byte and record emptiness.
/// - witness: `tests::gear::the_two_entry_points_agree`
/// - witness: `tests::common::partition_oracle_rejects_empty_record_ranges`
/// - witness: `tests::common::partition_oracle_rejects_broken_geometry`
#[spec(ensures: {
    chunks.iter().all(|chunk| chunk.records().end() > chunk.records().start())
        && chunks.array_windows::<2>().all(|pair| pair[0].bytes().end() == pair[1].bytes().start()
            && pair[0].records().end() == pair[1].records().start())
        && chunks.first().is_none_or(|chunk| chunk.bytes().start() == BytePosition::ZERO
            && chunk.records().start() == RecordPosition::ZERO)
        && chunks.last().map_or(0_u64, |chunk| u64::from(chunk.records().end()))
            == u64::try_from(records.as_ref().len()).expect("fixture count fits")
})]
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
        assert!(
            chunk.records().end() > chunk.records().start(),
            "chunk {position} contains a record"
        );
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
/// - panics: when a chunk exceeds a cap, has inverted endpoints or its record
///   count exceeds the fixture observer's width.
///
/// # Adequacy
/// - hypothesis: L3 at each cap and its upper neighbor, varying one axis at a
///   time; acceptance and rejection distinguish wrong-axis and strictness
///   faults.
/// - witness: `tests::common::cap_oracle_rejects_each_excess`
#[spec(ensures: chunks.iter().all(|chunk| {
    u64::from(chunk.bytes().end()).checked_sub(u64::from(chunk.bytes().start()))
        .is_some_and(|len| len <= u64::from(limits.max_bytes()))
        && u64::from(chunk.records().end()).checked_sub(u64::from(chunk.records().start()))
            .is_some_and(|len| len <= u64::from(u32::from(limits.max_records())))
}))]
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

#[test]
fn partition_oracle_rejects_empty_record_ranges()
{
    let records: [&[u8]; 2] = [b"", b""];
    let chunks = [(0_u64, 1_u64), (1, 1), (1, 2)].map(|(start, end)| {
        ChunkSpan::new(
            ByteSpan::new(BytePosition::ZERO, BytePosition::ZERO),
            gandr_storage_chunker::RecordSpan::new(
                RecordPosition::from(start),
                RecordPosition::from(end),
            ),
            gandr_storage_chunker::BoundaryReason::FinalRemainder,
        )
    });
    assert!(
        std::panic::catch_unwind(|| assert_partition(
            &chunks,
            CanonicalRecords::from(records.as_slice())
        ))
        .is_err(),
        "a zero-record chunk must be rejected even between valid empty-byte records"
    );
}

#[test]
fn record_edges_match_independent_prefixes()
{
    let records: [&[u8]; 4] = [b"", b"ab", b"cde", b""];
    let expected = [(0_u64, 0_u64), (0, 2), (2, 5), (5, 5)]
        .map(|(start, end)| ByteSpan::new(BytePosition::from(start), BytePosition::from(end)));
    assert_eq!(
        record_spans(CanonicalRecords::from(records.as_slice())).as_slice(),
        expected.as_slice()
    );
    assert_eq!(
        record_spans(CanonicalRecords::from([].as_slice())).as_slice(),
        [].as_slice()
    );
}

#[test]
fn length_observers_preserve_empty_and_width_boundaries()
{
    for (bytes, records, expected_bytes, expected_records) in [
        ([0_u64, 0_u64], [0_u64, 0_u64], 0_u64, 0_u32),
        ([7, 10], [11, 15], 3, 4),
        ([0, u64::MAX], [0, u64::from(u32::MAX)], u64::MAX, u32::MAX),
    ] {
        let [start, end] = bytes.map(BytePosition::from);
        let [first, last] = records.map(RecordPosition::from);
        let chunk = ChunkSpan::new(
            ByteSpan::new(start, end),
            gandr_storage_chunker::RecordSpan::new(first, last),
            gandr_storage_chunker::BoundaryReason::FinalRemainder,
        );
        assert_eq!(byte_len(&chunk), ByteCount::from(expected_bytes));
        assert_eq!(record_len(&chunk), RecordCount::from(expected_records));
    }
}

#[test]
fn cap_oracle_rejects_each_excess()
{
    let limits = limits(
        [1, 4, 8].map(ByteCount::from),
        [1, 2, 3].map(RecordCount::from),
    );
    for (bytes, records, expected_refusal) in [(8_u64, 3_u64, false), (9, 1, true), (1, 4, true)] {
        let chunk = ChunkSpan::new(
            ByteSpan::new(BytePosition::ZERO, BytePosition::from(bytes)),
            gandr_storage_chunker::RecordSpan::new(
                RecordPosition::ZERO,
                RecordPosition::from(records),
            ),
            gandr_storage_chunker::BoundaryReason::FinalRemainder,
        );
        assert_eq!(
            std::panic::catch_unwind(|| assert_within_caps(&[chunk], &limits)).is_err(),
            expected_refusal
        );
    }
}

#[test]
fn partition_oracle_rejects_broken_geometry()
{
    let records: [&[u8]; 3] = [b"ab", b"cde", b"f"];
    let records = CanonicalRecords::from(records.as_slice());
    let chunk = |bytes: [u64; 2], records: [u64; 2]| {
        let [start, end] = bytes.map(BytePosition::from);
        let [first, last] = records.map(RecordPosition::from);
        ChunkSpan::new(
            ByteSpan::new(start, end),
            gandr_storage_chunker::RecordSpan::new(first, last),
            gandr_storage_chunker::BoundaryReason::FinalRemainder,
        )
    };
    let valid = [chunk([0, 2], [0, 1]), chunk([2, 6], [1, 3])];
    assert_partition(&valid, records);
    for invalid in [
        [chunk([1, 2], [0, 1]), valid[1]],
        [chunk([0, 3], [0, 1]), chunk([3, 6], [1, 3])],
        [valid[0], chunk([2, 6], [2, 3])],
    ] {
        assert!(std::panic::catch_unwind(|| assert_partition(&invalid, records)).is_err());
    }
    assert!(std::panic::catch_unwind(|| assert_partition(&valid[.. 1], records)).is_err());
}
