//! Fixed framing, width and readback witnesses.

use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;

use super::*;

/// The golden v1 field set.
///
/// # Specification
/// trivial.
fn golden_identity() -> TransportStepId
{
    let mut encoder = StepIdEncoder::begin();
    encoder.put_u64(CanonicalU64::from(0x2a_u64));
    encoder.put_bytes(CanonicalBytes::try_from(&b"gandr"[..]).expect("length fits"));
    encoder.finish()
}

#[test]
fn the_v1_golden_vector_is_stable()
{
    assert_eq!(
        golden_identity().to_string(),
        "3c1a90f328af3242f3a06c85f20f4b613137b32bde84e13c2a8983e8f2f5943e"
    );
}

#[test]
fn the_identity_is_blake3_of_the_framed_preimage()
{
    let mut bytes = Vec::from(TRANSPORT_STEP_MAGIC);
    bytes.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 42]);
    bytes.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 5]);
    bytes.extend_from_slice(b"gandr");
    assert_eq!(golden_identity().as_ref(), blake3::hash(&bytes).as_bytes());
    let mut split = StepIdEncoder::begin();
    split.put_u64(CanonicalU64::from(0x2a_u64));
    for field in [&b"gan"[..], &b"dr"[..]] {
        split.put_bytes(CanonicalBytes::try_from(field).expect("length fits"));
    }
    assert_ne!(golden_identity(), split.finish());
}

#[test]
fn ingest_refuses_anything_but_the_fixed_width()
{
    for found in [0_usize, 16, 31, 33] {
        let image = vec![0_u8; found];
        assert_eq!(
            TransportStepId::try_from(image.as_slice()),
            Err(StepIdError::ImageLength {
                found,
                expected: TRANSPORT_STEP_ID_LEN,
            })
        );
    }
}

#[test]
fn an_identity_round_trips_through_its_byte_image()
{
    let id = golden_identity();
    assert_eq!(TransportStepId::try_from(id.as_ref()), Ok(id));
}

#[cfg(target_pointer_width = "64")]
#[test]
fn the_checked_widening_encodes_past_the_32_bit_ceiling()
{
    let wide = usize::try_from(0x1_0000_0000_u64).expect("64-bit target");
    let count = CanonicalU64::try_from(wide).expect("fits u64");
    assert_eq!(u64::from(count), 0x1_0000_0000);
    let mut encoder = StepIdEncoder::begin();
    encoder.put_u64(count);
    let mut bytes = Vec::from(TRANSPORT_STEP_MAGIC);
    bytes.extend_from_slice(&[0, 0, 0, 1, 0, 0, 0, 0]);
    assert_eq!(encoder.finish().as_ref(), blake3::hash(&bytes).as_bytes());
}

#[test]
fn the_checked_widening_refuses_past_the_32_bit_ceiling()
{
    assert!(u32::try_from(0x1_0000_0000_u64).is_err());
    let ceiling = usize::try_from(u64::from(u32::MAX)).expect("32-bit ceiling fits");
    let count = CanonicalU64::try_from(ceiling).expect("fits u64");
    let mut encoder = StepIdEncoder::begin();
    encoder.put_u64(count);
    let mut bytes = Vec::from(TRANSPORT_STEP_MAGIC);
    bytes.extend_from_slice(&[0, 0, 0, 0, 255, 255, 255, 255]);
    assert_eq!(encoder.finish().as_ref(), blake3::hash(&bytes).as_bytes());
}

/// A recorded factor in an issued cell store.
///
/// # Specification
/// trivial.
fn factor(
    store: &mut CellStore,
    name: &gandr_theory_cell_complexes::Sym,
) -> PrimCert
{
    PrimCert(gandr_theory_coherent_resolutions::CellApp {
        cell: store.insert(gandr_theory_cell_complexes::frame_defining_cell(name)),
        at: Pos::root(),
    })
}

#[test]
fn a_shared_identity_with_distinct_content_is_refused()
{
    let mut store = CellStore::new();
    let held = factor(&mut store, &gandr_theory_cell_complexes::Sym::new("Succ"));
    let offered = factor(&mut store, &gandr_theory_cell_complexes::Sym::new("Pred"));
    let id = TransportStepId::from([7_u8; 32]);
    let mut index = TransportStepIndex::default();
    index
        .insert(id, held.clone(), PrimMultiplicity::from(1_u32))
        .expect("vacant");
    let before = index.clone();
    assert_eq!(
        index.insert(id, offered.clone(), PrimMultiplicity::from(2_u32)),
        Err(TransportStepObstruction::ContentAddressCollision {
            address: id,
            held: Box::new(held),
            offered: Box::new(offered),
        })
    );
    assert_eq!(index, before);
}

#[test]
fn a_shared_identity_with_equal_content_sums_the_grading()
{
    let mut store = CellStore::new();
    let cert = factor(&mut store, &gandr_theory_cell_complexes::Sym::new("Succ"));
    let id = TransportStepId::from([9_u8; 32]);
    let mut index = TransportStepIndex::default();
    index
        .insert(id, cert.clone(), PrimMultiplicity::from(1_u32))
        .expect("vacant");
    index
        .insert(id, cert.clone(), PrimMultiplicity::from(2_u32))
        .expect("equal");
    assert_eq!(
        index.entries().get(&id),
        Some(&(cert.clone(), PrimMultiplicity::from(3_u32)))
    );
    index
        .insert(id, cert.clone(), PrimMultiplicity::from(u32::MAX))
        .expect("saturates");
    assert_eq!(
        index.entries().get(&id),
        Some(&(cert, PrimMultiplicity::from(u32::MAX)))
    );
}
