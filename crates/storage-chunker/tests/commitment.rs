//! The committed parameter blocks: their exact bytes, and that every field
//! moves them.
//!
//! A commitment is what a downstream root binds, so its bytes are protocol: a
//! golden here is written out field by field, and a change to one is a change
//! to every root built under it.

use gandr_storage_chunker::AlgorithmVersion;
use gandr_storage_chunker::ByteCount;
use gandr_storage_chunker::ChunkLimits;
use gandr_storage_chunker::ChunkerError;
use gandr_storage_chunker::ChunkerParams;
use gandr_storage_chunker::GearTableVersion;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::NormalizationPolicy;
use gandr_storage_chunker::ProfileField;
use gandr_storage_chunker::RawDiscriminator;
use gandr_storage_chunker::RecordBoundaryRule;
use gandr_storage_chunker::RecordCount;
use gandr_storage_chunker::SeedPolicy;
use gandr_storage_chunker::SeedSalt;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;

use crate::common::limits;
use crate::common::params;

/// Builds typed parameters from a raw kappa and a raw cap.
macro_rules! typed {
    ($kappa:expr, $cap:expr) => {
        TypedChunkerParams::new(
            Kappa::try_from($kappa).expect("a fixture kappa is non-zero"),
            TokenCap::try_from($cap).expect("a fixture cap is non-zero"),
        )
    };
}

/// The refusal a raw discriminator conversion reports.
///
/// # Specification
/// trivial.
const fn unsupported(
    field: ProfileField,
    raw: RawDiscriminator,
) -> ChunkerError
{
    ChunkerError::UnsupportedProfileValue { field, raw }
}

#[test]
fn the_typed_commitment_is_pinned()
{
    let mut expected = b"gandr:storage-chunker:params:v1".to_vec();
    expected.extend_from_slice(&[0x02, 0x00]);
    expected.extend_from_slice(&[0x07, 0, 0, 0, 0, 0, 0, 0]);
    expected.extend_from_slice(&[0x40, 0, 0, 0, 0, 0, 0, 0]);

    assert_eq!(
        typed!(7_u64, 64_u64).commitment().as_ref(),
        expected.as_slice()
    );
}

#[test]
fn each_typed_constant_moves_the_commitment()
{
    let base = typed!(7_u64, 64_u64).commitment();

    assert_eq!(
        base,
        typed!(7_u64, 64_u64).commitment(),
        "equal constants commit equally"
    );
    assert_ne!(
        base,
        typed!(8_u64, 64_u64).commitment(),
        "kappa moves the commitment"
    );
    assert_ne!(
        base,
        typed!(7_u64, 65_u64).commitment(),
        "the cap moves the commitment"
    );
    assert_ne!(
        base,
        typed!(64_u64, 7_u64).commitment(),
        "the constants are not interchangeable"
    );
}

#[test]
fn the_default_record_safe_commitment_is_pinned()
{
    let mut expected = b"gandr:storage-chunker:params:v1".to_vec();
    expected.extend_from_slice(&[0x01, 0x00]);
    expected.extend_from_slice(&[0x01, 0x00]);
    expected.push(0x00);
    expected.extend_from_slice(&[0_u8; 32]);
    expected.push(0x00);
    expected.push(0x00);
    expected.extend_from_slice(&[0x00, 0x10, 0, 0, 0, 0, 0, 0]);
    expected.extend_from_slice(&[0x00, 0x40, 0, 0, 0, 0, 0, 0]);
    expected.extend_from_slice(&[0x00, 0x00, 0x01, 0, 0, 0, 0, 0]);
    expected.extend_from_slice(&[0x01, 0, 0, 0]);
    expected.extend_from_slice(&[0x40, 0, 0, 0]);
    expected.extend_from_slice(&[0x00, 0x04, 0, 0]);

    assert_eq!(
        ChunkerParams::default_fastcdc().commitment().as_ref(),
        expected.as_slice()
    );
}

#[test]
fn each_record_safe_field_moves_the_commitment()
{
    let bytes = [4, 16, 64];
    let records = [1, 4, 16];
    let base = params(limits(
        bytes.map(ByteCount::from),
        records.map(RecordCount::from),
    ));
    let committed = base.commitment();

    let with_limits = |bytes: [u64; 3], records: [u32; 3]| {
        params(limits(
            bytes.map(ByteCount::from),
            records.map(RecordCount::from),
        ))
        .commitment()
    };
    let changed = [
        with_limits([5, 16, 64], records),
        with_limits([4, 17, 64], records),
        with_limits([4, 16, 65], records),
        with_limits(bytes, [2, 4, 16]),
        with_limits(bytes, [1, 5, 16]),
        with_limits(bytes, [1, 4, 17]),
    ];
    for (field, commitment) in changed.iter().enumerate() {
        assert_ne!(&committed, commitment, "limit {field} moves the commitment");
    }

    // An all-zero public salt commits the same salt bytes as no salt; the seed
    // kind is what tells them apart.
    let zero_salted = ChunkerParams::new(
        GearTableVersion::V1,
        SeedPolicy::PublicSalt(SeedSalt::from([0_u8; 32])),
        NormalizationPolicy::PreserveBytes,
        RecordBoundaryRule::BetweenRecords,
        base.limits(),
    );
    assert_ne!(
        committed,
        zero_salted.commitment(),
        "the seed kind moves the commitment"
    );
}

#[test]
fn a_public_salt_is_committed_in_the_clear()
{
    let ascending: [u8; 32] =
        core::array::from_fn(|index| u8::try_from(index).expect("a salt index fits u8"));
    let mut descending = ascending;
    descending.reverse();
    let salted = |salt: [u8; 32]| {
        ChunkerParams::new(
            GearTableVersion::V1,
            SeedPolicy::PublicSalt(SeedSalt::from(salt)),
            NormalizationPolicy::PreserveBytes,
            RecordBoundaryRule::BetweenRecords,
            ChunkLimits::default_fastcdc(),
        )
        .commitment()
    };

    assert_eq!(salted(ascending), salted(ascending));
    assert_ne!(salted(ascending), salted(descending));
    assert!(
        salted(ascending)
            .as_ref()
            .windows(ascending.len())
            .any(|window| window == ascending.as_slice()),
        "the salt bytes appear verbatim in the commitment"
    );
}

#[test]
fn raw_discriminators_round_trip_and_refuse_by_field()
{
    for raw in 0_u16 ..= u16::MAX {
        let algorithm = match raw {
            | 1 => Ok(AlgorithmVersion::FastCdc2020),
            | 2 => Ok(AlgorithmVersion::TypedCdc),
            | _ => Err(unsupported(ProfileField::Algorithm, RawDiscriminator(raw))),
        };
        assert_eq!(AlgorithmVersion::try_from(raw), algorithm);
        let gear = if raw == 1 {
            Ok(GearTableVersion::V1)
        }
        else {
            Err(unsupported(ProfileField::GearTable, RawDiscriminator(raw)))
        };
        assert_eq!(GearTableVersion::try_from(raw), gear);
    }
    for raw in 0_u8 ..= u8::MAX {
        let normalization = if raw == 0 {
            Ok(NormalizationPolicy::PreserveBytes)
        }
        else {
            Err(unsupported(
                ProfileField::Normalization,
                RawDiscriminator::from(raw),
            ))
        };
        assert_eq!(NormalizationPolicy::try_from(raw), normalization);
        let rule = if raw == 0 {
            Ok(RecordBoundaryRule::BetweenRecords)
        }
        else {
            Err(unsupported(
                ProfileField::RecordBoundaryRule,
                RawDiscriminator::from(raw),
            ))
        };
        assert_eq!(RecordBoundaryRule::try_from(raw), rule);
    }
}
