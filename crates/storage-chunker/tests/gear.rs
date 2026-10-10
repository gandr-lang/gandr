//! The record-safe profile: where a Gear scan over record bytes cuts, and what
//! it refuses.
//!
//! Every successful scan is checked against the records themselves — the
//! chunks must partition them on record edges and sit inside the caps — rather
//! than against the scan's own arithmetic.

use anodized::spec;
use gandr_storage_chunker::BoundaryReason;
use gandr_storage_chunker::ByteCount;
use gandr_storage_chunker::BytePosition;
use gandr_storage_chunker::ByteSpan;
use gandr_storage_chunker::CanonicalBytes;
use gandr_storage_chunker::CanonicalRecords;
use gandr_storage_chunker::ChunkLimits;
use gandr_storage_chunker::ChunkerError;
use gandr_storage_chunker::InvalidParameterReason;
use gandr_storage_chunker::RecordCount;
use gandr_storage_chunker::RecordPosition;
use gandr_storage_chunker::chunk_record_slices;
use gandr_storage_chunker::chunk_spans;

use crate::common::Concatenated;
use crate::common::assert_partition;
use crate::common::assert_within_caps;
use crate::common::byte_len;
use crate::common::limits;
use crate::common::params;
use crate::common::record_len;
use crate::common::record_spans;

/// Calls [`ChunkLimits::new`] with six raw limits.
///
/// # Specification
/// - requires: nothing; both arrays may contain arbitrary limits.
/// - ensures: validation preserves the six offered fields on success and the
///   first parameter-refusal reason on failure.
/// - provides: array-shaped inputs for the validation boundary witnesses.
/// - fails: returns the validating constructor's exact refusal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 at zero, ordering and width boundaries, including competing
///   failures; exact fields and refusal reasons separate argument permutation
///   and altered error mapping.
/// - witness: `tests::gear::invalid_limits_are_refused_by_reason`
/// - witness: `tests::gear::equal_limits_are_admitted`
#[spec(ensures: |ret| {
    let [min, target, max] = bytes;
    let [min_records, target_records, max_records] = records;
    ret == ChunkLimits::new(min, target, max, min_records, target_records, max_records)
})]
fn raw_limits(
    bytes: [ByteCount; 3],
    records: [RecordCount; 3],
) -> Result<ChunkLimits, ChunkerError>
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
}

/// The refusal [`ChunkLimits::new`] reports for `reason`.
///
/// # Specification
/// trivial.
const fn refused(reason: InvalidParameterReason) -> Result<ChunkLimits, ChunkerError>
{
    Err(ChunkerError::InvalidParameters { reason })
}

#[test]
fn invalid_limits_are_refused_by_reason()
{
    let widest = u64::from(u32::MAX);
    let past_widest = widest.checked_add(1_u64).expect("u32::MAX + 1 fits u64");

    let cases = [
        ([0, 1, 2], [1, 1, 2], InvalidParameterReason::ZeroByteLimit),
        ([1, 0, 2], [1, 1, 2], InvalidParameterReason::ZeroByteLimit),
        ([1, 1, 0], [1, 1, 2], InvalidParameterReason::ZeroByteLimit),
        (
            [1, 1, 2],
            [0, 1, 2],
            InvalidParameterReason::ZeroRecordLimit,
        ),
        (
            [1, 1, 2],
            [1, 0, 2],
            InvalidParameterReason::ZeroRecordLimit,
        ),
        (
            [1, 1, 2],
            [1, 1, 0],
            InvalidParameterReason::ZeroRecordLimit,
        ),
        (
            [9, 8, 16],
            [1, 2, 3],
            InvalidParameterReason::MinByteExceedsTargetByte,
        ),
        (
            [1, 17, 16],
            [1, 2, 3],
            InvalidParameterReason::InvertedByteLimits,
        ),
        (
            [1, past_widest, past_widest],
            [1, 1, 1],
            InvalidParameterReason::TargetByteExceedsU32,
        ),
        (
            [1, 8, 16],
            [4, 3, 5],
            InvalidParameterReason::InvertedRecordLimits,
        ),
        (
            [1, 8, 16],
            [1, 6, 5],
            InvalidParameterReason::InvertedRecordLimits,
        ),
        ([0, 0, 0], [0, 0, 0], InvalidParameterReason::ZeroByteLimit),
        (
            [3, 2, 1],
            [0, 0, 0],
            InvalidParameterReason::ZeroRecordLimit,
        ),
        (
            [3, 2, 1],
            [3, 2, 1],
            InvalidParameterReason::MinByteExceedsTargetByte,
        ),
        (
            [1, past_widest, 1],
            [3, 2, 1],
            InvalidParameterReason::InvertedByteLimits,
        ),
        (
            [1, past_widest, past_widest],
            [3, 2, 1],
            InvalidParameterReason::TargetByteExceedsU32,
        ),
    ];

    for (bytes, records, reason) in cases {
        assert_eq!(
            raw_limits(bytes.map(ByteCount::from), records.map(RecordCount::from)),
            refused(reason),
            "refused as {reason}"
        );
    }
}

#[test]
fn equal_limits_are_admitted()
{
    let widest = u64::from(u32::MAX);

    for (bytes, records) in [
        ([8, 8, 8], [2, 2, 2]),
        ([1, widest, widest], [1, 1, 1]),
        ([1, 3, 9], [2, 4, 7]),
    ] {
        let limits = raw_limits(bytes.map(ByteCount::from), records.map(RecordCount::from))
            .expect("valid limit boundaries");
        assert_eq!(
            [
                limits.min_bytes(),
                limits.target_bytes(),
                limits.max_bytes()
            ]
            .map(u64::from),
            bytes
        );
        assert_eq!(
            [
                limits.min_records(),
                limits.target_records(),
                limits.max_records()
            ]
            .map(u32::from),
            records
        );
    }
}

#[test]
fn identical_records_and_params_emit_identical_chunks()
{
    let records: [&[u8]; 6] = [b"alpha", b"beta", b"gamma", b"delta", b"epsilon", b"zeta"];
    let records = CanonicalRecords::from(records.as_slice());
    let limits = limits(
        [4, 16, 48].map(ByteCount::from),
        [1, 4, 16].map(RecordCount::from),
    );
    let params = params(limits);

    let first = chunk_record_slices(records, &params).expect("the corpus chunks");
    let second = chunk_record_slices(records, &params).expect("the corpus chunks again");

    assert_eq!(first, second);
    assert_partition(&first, records);
    assert_within_caps(&first, &limits);
}

#[test]
fn the_two_entry_points_agree()
{
    let records: [&[u8]; 7] = [
        b"k:a\0v:1",
        b"k:b\0v:2",
        b"k:c\0v:3",
        b"k:d\0v:4",
        b"k:e\0v:5",
        b"k:f\0v:6",
        b"k:g\0v:7",
    ];
    let records = CanonicalRecords::from(records.as_slice());
    let params = params(limits(
        [8, 24, 40].map(ByteCount::from),
        [1, 3, 8].map(RecordCount::from),
    ));
    let bytes = Concatenated::of(records);

    let from_records = chunk_record_slices(records, &params).expect("the records chunk");
    let from_spans =
        chunk_spans(bytes.bytes(), &record_spans(records), &params).expect("the spans chunk");

    assert_eq!(from_records, from_spans);
    assert_partition(&from_spans, records);
}

#[test]
fn empty_input_and_final_remainder_partition_the_input()
{
    let params = params(limits(
        [16, 32, 64].map(ByteCount::from),
        [4, 8, 16].map(RecordCount::from),
    ));

    let empty: [&[u8]; 0] = [];
    let chunks = chunk_record_slices(CanonicalRecords::from(empty.as_slice()), &params)
        .expect("empty input chunks");
    assert!(
        chunks.is_empty(),
        "empty input emits no chunk, not one empty chunk"
    );

    let records: [&[u8]; 3] = [b"a", b"bc", b"def"];
    let records = CanonicalRecords::from(records.as_slice());
    let chunks = chunk_record_slices(records, &params).expect("short input chunks");

    assert_eq!(chunks.len(), 1, "input under the minimums is one chunk");
    assert_eq!(chunks[0].reason(), BoundaryReason::FinalRemainder);
    assert_partition(&chunks, records);
}

#[test]
fn minimum_limits_suppress_an_early_hash_cut()
{
    let records: [&[u8]; 24] = [&[0xAB_u8]; 24];
    let records = CanonicalRecords::from(records.as_slice());
    let minimums = ByteCount::from(8_u64);
    let gated = params(limits(
        [8, 8, 16].map(ByteCount::from),
        [8, 8, 16].map(RecordCount::from),
    ));
    let ungated = params(limits(
        [1, 8, 16].map(ByteCount::from),
        [1, 8, 16].map(RecordCount::from),
    ));

    let chunks = chunk_record_slices(records, &gated).expect("the gated corpus chunks");
    assert_partition(&chunks, records);
    for chunk in chunks
        .iter()
        .filter(|chunk| chunk.reason() != BoundaryReason::FinalRemainder)
    {
        assert!(
            byte_len(chunk) >= minimums,
            "no cut before the minimum byte limit"
        );
        assert!(
            record_len(chunk) >= RecordCount::from(8_u32),
            "no cut before the minimum record limit"
        );
    }

    // The same corpus without the gate does cut early, so the gate is what
    // held the cuts back above.
    let chunks = chunk_record_slices(records, &ungated).expect("the ungated corpus chunks");
    assert!(
        chunks.iter().any(|chunk| {
            chunk.reason() == BoundaryReason::HashPredicate && byte_len(chunk) < minimums
        }),
        "without minimums the hash predicate cuts a chunk under eight bytes"
    );
}

#[test]
fn the_caps_force_their_reasons()
{
    let records: [&[u8]; 3] = [b"aaaa", b"bbbb", b"cccc"];
    let byte_cap = params(limits(
        [8, 8, 8].map(ByteCount::from),
        [1, 8, 16].map(RecordCount::from),
    ));
    let chunks = chunk_record_slices(CanonicalRecords::from(records.as_slice()), &byte_cap)
        .expect("the byte-cap corpus chunks");

    assert_eq!(chunks[0].reason(), BoundaryReason::MaxByteCap);
    assert_eq!(
        chunks[0].bytes(),
        ByteSpan::new(BytePosition::from(0_u64), BytePosition::from(8_u64))
    );
    assert_eq!(chunks[0].records().end(), RecordPosition::from(2_u64));

    let records: [&[u8]; 5] = [b"a", b"b", b"c", b"d", b"e"];
    let record_cap = params(limits(
        [1, 64, 128].map(ByteCount::from),
        [3, 3, 3].map(RecordCount::from),
    ));
    let chunks = chunk_record_slices(CanonicalRecords::from(records.as_slice()), &record_cap)
        .expect("the record-cap corpus chunks");

    assert_eq!(chunks[0].reason(), BoundaryReason::MaxRecordCap);
    assert_eq!(chunks[0].records().start(), RecordPosition::from(0_u64));
    assert_eq!(chunks[0].records().end(), RecordPosition::from(3_u64));
}

#[test]
fn an_oversized_record_is_refused_by_name()
{
    let params = params(limits(
        [1, 8, 8].map(ByteCount::from),
        [1, 1, 4].map(RecordCount::from),
    ));

    let fits: [&[u8]; 1] = [&[0x11_u8; 8]];
    assert!(chunk_record_slices(CanonicalRecords::from(fits.as_slice()), &params).is_ok());

    let oversized: [&[u8]; 1] = [&[0x11_u8; 9]];
    assert_eq!(
        chunk_record_slices(CanonicalRecords::from(oversized.as_slice()), &params),
        Err(ChunkerError::RecordByteLengthCapViolation {
            record_index: RecordPosition::from(0_u64),
            record_len: ByteCount::from(9_u64),
            max_bytes: ByteCount::from(8_u64),
        })
    );
}

#[test]
fn an_unreachable_minimum_is_refused_by_name()
{
    let records: [&[u8]; 2] = [&[0x21_u8; 5], &[0x22_u8; 5]];
    let params = params(limits(
        [1, 8, 8].map(ByteCount::from),
        [2, 2, 4].map(RecordCount::from),
    ));

    assert_eq!(
        chunk_record_slices(CanonicalRecords::from(records.as_slice()), &params),
        Err(ChunkerError::ChunkByteCapViolation {
            chunk_start_record: RecordPosition::from(0_u64),
            next_record_index: RecordPosition::from(1_u64),
            attempted_bytes: ByteCount::from(10_u64),
            max_bytes: ByteCount::from(8_u64),
        })
    );
}

#[test]
fn span_lists_that_are_not_a_partition_are_refused()
{
    let bytes = CanonicalBytes::from(b"abcdef".as_slice());
    let params = params(limits(
        [1, 4, 8].map(ByteCount::from),
        [1, 2, 4].map(RecordCount::from),
    ));
    let span =
        |start: u64, end: u64| ByteSpan::new(BytePosition::from(start), BytePosition::from(end));
    let second = RecordPosition::from(1_u64);

    assert_eq!(
        chunk_spans(bytes, &[span(0, 3), span(2, 6)], &params),
        Err(ChunkerError::NonMonotonicRecordSpans { index: second }),
        "an overlap is refused"
    );
    assert_eq!(
        chunk_spans(bytes, &[span(0, 2), span(3, 6)], &params),
        Err(ChunkerError::NonMonotonicRecordSpans { index: second }),
        "a gap is refused"
    );
    assert_eq!(
        chunk_spans(bytes, &[span(0, 3), span(3, 2)], &params),
        Err(ChunkerError::NonMonotonicRecordSpans { index: second }),
        "an inverted span is refused"
    );
    assert_eq!(
        chunk_spans(bytes, &[span(0, 3), span(3, 7)], &params),
        Err(ChunkerError::RecordSpanOutOfBounds {
            index: second,
            end: BytePosition::from(7_u64),
            canonical_len: BytePosition::from(6_u64),
        }),
        "a span past the bytes is refused"
    );
    assert_eq!(
        chunk_spans(bytes, &[span(0, 3)], &params),
        Err(ChunkerError::UncoveredCanonicalBytes {
            covered_end: BytePosition::from(3_u64),
            canonical_len: BytePosition::from(6_u64),
        }),
        "spans that stop short are refused"
    );
    assert!(chunk_spans(bytes, &[span(0, 3), span(3, 6)], &params).is_ok());
}

#[test]
fn low_entropy_streams_stay_within_the_caps()
{
    let records: [&[u8]; 20] = [&[0_u8; 8]; 20];
    let records = CanonicalRecords::from(records.as_slice());
    let limits = limits(
        [16, 32, 48].map(ByteCount::from),
        [1, 4, 16].map(RecordCount::from),
    );
    let params = params(limits);

    let first = chunk_record_slices(records, &params).expect("the repeated corpus chunks");
    let second = chunk_record_slices(records, &params).expect("the repeated corpus chunks again");

    assert_eq!(first, second);
    assert_partition(&first, records);
    assert_within_caps(&first, &limits);
}

#[test]
fn many_tiny_and_near_cap_records_stay_within_the_caps()
{
    let tiny: [&[u8]; 64] = [&[0x7F_u8]; 64];
    let tiny = CanonicalRecords::from(tiny.as_slice());
    let tiny_limits = limits(
        [1, 16, 32].map(ByteCount::from),
        [7, 7, 7].map(RecordCount::from),
    );
    let chunks = chunk_record_slices(tiny, &params(tiny_limits)).expect("the tiny corpus chunks");

    assert!(
        chunks.len() > 1,
        "sixty-four tiny records are more than one chunk"
    );
    assert!(
        chunks
            .iter()
            .any(|chunk| chunk.reason() == BoundaryReason::MaxRecordCap)
    );
    assert_partition(&chunks, tiny);
    assert_within_caps(&chunks, &tiny_limits);

    let near_cap: [&[u8]; 4] = [&[0x42_u8; 8], &[0x24_u8; 7], &[0x42_u8; 8], &[0x24_u8; 7]];
    let near_cap = CanonicalRecords::from(near_cap.as_slice());
    let near_cap_limits = limits(
        [1, 8, 8].map(ByteCount::from),
        [1, 4, 16].map(RecordCount::from),
    );
    let chunks = chunk_record_slices(near_cap, &params(near_cap_limits))
        .expect("the near-cap corpus chunks");

    assert_partition(&chunks, near_cap);
    assert_within_caps(&chunks, &near_cap_limits);
}

#[test]
fn empty_records_keep_their_record_positions()
{
    let records: [&[u8]; 4] = [b"", b"", b"x", b""];
    let records = CanonicalRecords::from(records.as_slice());
    let params = params(limits(
        [4, 8, 16].map(ByteCount::from),
        [1, 4, 8].map(RecordCount::from),
    ));
    let chunks = chunk_record_slices(records, &params).expect("empty records are valid");
    assert_eq!(chunks.len(), 1);
    assert_eq!(
        chunks[0].bytes(),
        ByteSpan::new(BytePosition::ZERO, BytePosition::from(1_u64))
    );
    assert_eq!(chunks[0].records().start(), RecordPosition::ZERO);
    assert_eq!(chunks[0].records().end(), RecordPosition::from(4_u64));
    assert_eq!(chunks[0].reason(), BoundaryReason::FinalRemainder);
    assert_eq!(
        chunk_spans(
            CanonicalBytes::from(b"x".as_slice()),
            &record_spans(records),
            &params
        ),
        Ok(chunks)
    );
}
