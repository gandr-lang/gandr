//! The typed profile: the cap, the predicate, their precedence, and the
//! record-safe degenerate instance.

use gandr_storage_chunker::BoundaryEvent;
use gandr_storage_chunker::BoundaryReason;
use gandr_storage_chunker::BoundaryResidue;
use gandr_storage_chunker::ByteCount;
use gandr_storage_chunker::CanonicalRecords;
use gandr_storage_chunker::ChunkerError;
use gandr_storage_chunker::CutDecision;
use gandr_storage_chunker::InvalidParameterReason;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::RecordCount;
use gandr_storage_chunker::RecordPosition;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunker;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_chunker::chunk_record_slices;

use crate::common::limits;
use crate::common::params;

/// Opens a typed scanner from a raw kappa and a raw cap.
macro_rules! scanner {
    ($kappa:expr, $cap:expr) => {
        TypedChunker::new(&TypedChunkerParams::new(
            Kappa::try_from($kappa).expect("a fixture kappa is non-zero"),
            TokenCap::try_from($cap).expect("a fixture cap is non-zero"),
        ))
    };
}

/// Builds an event from a raw token count and a raw residue.
macro_rules! event {
    ($tokens:expr, $residue:expr) => {
        BoundaryEvent::new(TokenCount::from($tokens), BoundaryResidue::from($residue))
    };
}

#[test]
fn zero_constants_are_refused_by_reason()
{
    assert_eq!(
        Kappa::try_from(0_u64),
        Err(ChunkerError::InvalidParameters {
            reason: InvalidParameterReason::ZeroKappa,
        })
    );
    assert_eq!(
        TokenCap::try_from(0_u64),
        Err(ChunkerError::InvalidParameters {
            reason: InvalidParameterReason::ZeroTokenCap,
        })
    );
    assert!(Kappa::try_from(1_u64).is_ok());
    assert!(TokenCap::try_from(1_u64).is_ok());
}

#[test]
fn the_cap_and_the_predicate_cut_at_their_boundaries()
{
    let mut chunker = scanner!(4_u64, 10_u64);

    // A residue one past a multiple of kappa continues; the pending count is
    // the sum of the events since the last cut.
    assert_eq!(
        chunker.on_boundary(event!(3_u64, 9_u64)),
        CutDecision::Continue
    );
    assert_eq!(chunker.pending(), TokenCount::from(3_u64));
    assert_eq!(
        chunker.on_boundary(event!(2_u64, 7_u64)),
        CutDecision::Continue
    );
    assert_eq!(chunker.pending(), TokenCount::from(5_u64));

    // The multiple itself cuts, and the cut resets the count.
    assert_eq!(
        chunker.on_boundary(event!(1_u64, 8_u64)),
        CutDecision::Cut(BoundaryReason::HashPredicate)
    );
    assert_eq!(chunker.pending(), TokenCount::ZERO);

    // One token under the cap continues; reaching it exactly cuts.
    assert_eq!(
        chunker.on_boundary(event!(9_u64, 1_u64)),
        CutDecision::Continue
    );
    assert_eq!(
        chunker.on_boundary(event!(1_u64, 1_u64)),
        CutDecision::Cut(BoundaryReason::MaxTokenCap)
    );
    assert_eq!(chunker.pending(), TokenCount::ZERO);

    // A single event past the cap cuts on its own.
    assert_eq!(
        chunker.on_boundary(event!(11_u64, 1_u64)),
        CutDecision::Cut(BoundaryReason::MaxTokenCap)
    );
}

#[test]
fn the_cap_takes_precedence_over_the_predicate()
{
    let mut chunker = scanner!(4_u64, 10_u64);

    assert_eq!(
        chunker.on_boundary(event!(10_u64, 8_u64)),
        CutDecision::Cut(BoundaryReason::MaxTokenCap),
        "an event that both reaches the cap and satisfies the predicate is a cap cut"
    );
}

#[test]
fn a_saturated_count_still_cuts()
{
    let mut chunker = scanner!(u64::MAX, u64::MAX);

    assert_eq!(
        chunker.on_boundary(event!(u64::MAX - 1_u64, 1_u64)),
        CutDecision::Continue
    );
    assert_eq!(
        chunker.on_boundary(event!(u64::MAX, 1_u64)),
        CutDecision::Cut(BoundaryReason::MaxTokenCap),
        "a pending count that would wrap saturates at the cap and cuts"
    );
}

#[test]
fn one_event_per_record_is_the_record_safe_degenerate_instance()
{
    // A target of one byte makes the record-safe mask zero, so every record is
    // a cut; kappa one makes every residue a multiple, so every event is a
    // cut. The two profiles must then end chunks after the same records.
    let records: [&[u8]; 4] = [b"one", b"two", b"three", b"four"];
    let record_safe = chunk_record_slices(
        CanonicalRecords::from(records.as_slice()),
        &params(limits(
            [1, 1, 64].map(ByteCount::from),
            [1, 16, 16].map(RecordCount::from),
        )),
    )
    .expect("the degenerate corpus chunks");
    let mut chunker = scanner!(1_u64, u64::MAX);
    let mut typed_ends = Vec::new();
    for (position, _record) in records.iter().enumerate() {
        if chunker.on_boundary(event!(1_u64, 0x5EED_u64))
            == CutDecision::Cut(BoundaryReason::HashPredicate)
        {
            let end = position
                .checked_add(1)
                .expect("a fixture position fits usize");
            typed_ends.push(RecordPosition::from(u64::try_from(end).expect("fits u64")));
        }
    }

    let record_safe_ends: Vec<RecordPosition> = record_safe
        .iter()
        .map(|chunk| chunk.records().end())
        .collect();
    assert_eq!(record_safe_ends, typed_ends);
    assert_eq!(typed_ends.len(), records.len());
}
