//! The byte profile's contract: its limits refuse by name, its commitment is
//! pinned, and its cuts partition a byte string and stay in place after an
//! edit before them (#6590, #6714).
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the fixtures pass a stream's seed and length and the raw limits a test refuses"
    )
)]

use gandr_storage_chunker::ByteChunkerParams;
use gandr_storage_chunker::ByteCount;
use gandr_storage_chunker::ByteLimits;
use gandr_storage_chunker::ByteScanner;
use gandr_storage_chunker::ByteSpan;
use gandr_storage_chunker::CanonicalBytes;
use gandr_storage_chunker::ChunkerError;
use gandr_storage_chunker::GearTableVersion;
use gandr_storage_chunker::InvalidParameterReason;
use gandr_storage_chunker::PARAMETER_DOMAIN;
use gandr_storage_chunker::chunk_bytes;

/// `len` bytes of a `SplitMix64` stream from `seed`, so each run reads the
/// same bytes and no two seeds share a prefix.
///
/// # Specification
/// trivial.
fn stream(
    seed: u64,
    len: usize,
) -> Vec<u8>
{
    let mut state = seed;
    let mut bytes = Vec::with_capacity(len);
    while bytes.len() < len {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15_u64);
        let mut mixed = state;
        mixed = (mixed ^ (mixed >> 30_u32)).wrapping_mul(0xBF58_476D_1CE4_E5B9_u64);
        mixed = (mixed ^ (mixed >> 27_u32)).wrapping_mul(0x94D0_49BB_1331_11EB_u64);
        mixed ^= mixed >> 31_u32;
        bytes.extend_from_slice(&mixed.to_le_bytes());
    }
    bytes.truncate(len);
    bytes
}

/// The end of each chunk the blob profile cuts `bytes` into.
///
/// # Specification
/// trivial.
fn ends(bytes: &[u8]) -> Vec<u64>
{
    chunk_bytes(CanonicalBytes::from(bytes), &ByteChunkerParams::blob())
        .expect("the blob profile cuts any bytes")
        .iter()
        .map(|chunk| u64::from(chunk.end()))
        .collect()
}

/// Limits of `min`, `target` and `max` bytes.
///
/// # Specification
/// trivial.
fn limits(
    min: u64,
    target: u64,
    max: u64,
) -> Result<ByteLimits, ChunkerError>
{
    ByteLimits::new(
        ByteCount::from(min),
        ByteCount::from(target),
        ByteCount::from(max),
    )
}

#[test]
fn each_refused_limit_names_its_reason()
{
    let refused = |reason| Err(ChunkerError::InvalidParameters { reason });
    assert_eq!(
        limits(0, 128, 256),
        refused(InvalidParameterReason::ZeroByteLimit)
    );
    assert_eq!(
        limits(64, 128, 0),
        refused(InvalidParameterReason::ZeroByteLimit)
    );
    assert_eq!(
        limits(63, 128, 256),
        refused(InvalidParameterReason::MinByteUnderGearWindow)
    );
    assert!(limits(64, 128, 256).is_ok());
    assert_eq!(
        limits(129, 128, 256),
        refused(InvalidParameterReason::MinByteExceedsTargetByte)
    );
    assert!(limits(128, 128, 256).is_ok());
    assert_eq!(
        limits(64, 257, 256),
        refused(InvalidParameterReason::InvertedByteLimits)
    );
    assert!(limits(64, 256, 256).is_ok());
    let wide = u64::from(u32::MAX);
    assert_eq!(
        limits(64, wide.saturating_add(1), u64::MAX),
        refused(InvalidParameterReason::TargetByteExceedsU32)
    );
    assert!(limits(64, wide, u64::MAX).is_ok());
}

#[test]
fn the_blob_commitment_is_pinned()
{
    let mut expected = PARAMETER_DOMAIN.to_vec();
    expected.extend_from_slice(&3_u16.to_le_bytes());
    expected.extend_from_slice(&2_u16.to_le_bytes());
    expected.extend_from_slice(&0x1000_u64.to_le_bytes());
    expected.extend_from_slice(&0x4000_u64.to_le_bytes());
    expected.extend_from_slice(&0x0001_0000_u64.to_le_bytes());
    assert_eq!(
        ByteChunkerParams::blob().commitment().as_ref(),
        expected.as_slice()
    );
}

#[test]
fn each_field_moves_the_commitment()
{
    let base = limits(64, 128, 256).expect("valid limits");
    let image = |limits| ByteChunkerParams::new(GearTableVersion::V2, limits).commitment();
    let reference = image(base);
    for moved in [
        limits(65, 128, 256),
        limits(64, 129, 256),
        limits(64, 128, 257),
    ] {
        assert_ne!(image(moved.expect("valid limits")), reference);
    }
}

#[test]
fn the_chunks_partition_the_bytes_within_the_limits()
{
    let params = ByteChunkerParams::blob();
    let min = u64::from(params.limits().min_bytes());
    let max = u64::from(params.limits().max_bytes());
    assert_eq!(
        chunk_bytes(CanonicalBytes::from([].as_slice()), &params),
        Ok(Vec::new())
    );
    for (seed, len) in [
        (1_u64, 1_usize),
        (2, 0x0FFF),
        (3, 0x1000),
        (4, 0x0001_0001),
        (5, 1_000_003),
    ] {
        let bytes = stream(seed, len);
        let chunks: Vec<ByteSpan> =
            chunk_bytes(CanonicalBytes::from(bytes.as_slice()), &params).expect("cuts");
        let mut end = 0_u64;
        for (index, chunk) in chunks.iter().enumerate() {
            let start = u64::from(chunk.start());
            let stop = u64::from(chunk.end());
            assert_eq!(
                start, end,
                "chunk {index} of seed {seed} starts where the last ended"
            );
            let length = stop.checked_sub(start).expect("ordered");
            assert!(
                length > 0 && length <= max,
                "chunk {index} of seed {seed} holds {length}"
            );
            if index.saturating_add(1) < chunks.len() {
                assert!(length >= min, "chunk {index} of seed {seed} holds {length}");
            }
            end = stop;
        }
        assert_eq!(
            usize::try_from(end).ok(),
            Some(len),
            "seed {seed} is covered"
        );
    }
}

#[test]
fn a_byte_put_before_a_stream_moves_no_later_cut()
{
    let bytes = stream(6714, 1_379_882);
    let before = ends(&bytes);
    let mut edited = Vec::with_capacity(bytes.len().saturating_add(1));
    edited.push(b'#');
    edited.extend_from_slice(&bytes);
    let after: Vec<u64> = ends(&edited)
        .iter()
        .map(|end| end.saturating_sub(1))
        .collect();
    assert!(
        before.len() > 32,
        "the stream holds {} chunks",
        before.len()
    );
    let first = before
        .iter()
        .position(|end| after.binary_search(end).is_ok())
        .expect("a cut comes back");
    assert!(first <= 1, "the cuts come back after chunk {first}");
    let tail = before.get(first ..).expect("in range");
    assert_eq!(
        after.get(after.len().saturating_sub(tail.len()) ..),
        Some(tail)
    );
}

#[test]
fn a_stream_of_one_byte_value_is_cut_at_the_maximum()
{
    let params = ByteChunkerParams::blob();
    let max = u64::from(params.limits().max_bytes());
    let bytes = vec![0_u8; 200_000];
    let chunks = chunk_bytes(CanonicalBytes::from(bytes.as_slice()), &params).expect("cuts");
    let lengths: Vec<u64> = chunks
        .iter()
        .map(|chunk| u64::from(chunk.end()).saturating_sub(u64::from(chunk.start())))
        .collect();
    let last = 200_000_u64.checked_rem(max).expect("nonzero maximum");
    assert_eq!(lengths, vec![max, max, max, last]);
}

#[test]
fn a_stream_fed_in_buffers_cuts_as_it_cuts_whole_6719()
{
    let bytes = stream(6719, 0x0010_0000 + 12_345);
    let whole = ends(&bytes);
    for size in [1_usize, 63, 64, 4_096, 0x0001_0001, 0x0010_0000] {
        let mut scanner = ByteScanner::new(&ByteChunkerParams::blob());
        let mut fed = Vec::new();
        let mut at = 0_u64;
        for buffer in bytes.chunks(size) {
            let mut rest = buffer;
            while let Some(taken) = scanner.cut(CanonicalBytes::from(rest)) {
                at = at.checked_add(u64::from(taken)).expect("in range");
                fed.push(at);
                let taken = usize::try_from(u64::from(taken)).expect("in range");
                rest = rest.get(taken ..).expect("the cut lies in the buffer");
            }
            at = at
                .checked_add(u64::try_from(rest.len()).expect("in range"))
                .expect("in range");
        }
        if fed.last() != Some(&at) {
            fed.push(at);
        }
        assert_eq!(fed, whole, "buffers of {size} bytes cut as the whole");
    }
}
