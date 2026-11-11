use alloc::collections::BTreeSet;
use alloc::sync::Arc;

use gandr_kernel_core::Environment;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::NoVerdicts;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_kernel_core::verdict::VerdictSource as _;
use gandr_kernel_term::LevelSignature;
use quenchant_shape::shape::Maybe;

use super::Bounds;
use super::HeldVerdicts;

/// The receipt `signer` gives over a cold admission of two unit
/// definitions.
///
/// # Specification
/// trivial.
fn receipt(signer: &KernelSigner) -> StoredReceipt
{
    let mut environment = Environment::recalling(
        TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
        Arc::new(NoVerdicts),
    );
    for _ in 0_u8 .. 2 {
        let staged = {
            let mut staging = environment.stage();
            let declared = staging.arena().value_type_unit();
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        };
        let _admitted = environment
            .add_decl(staged)
            .expect("a unit definition admits");
    }
    let Maybe::Present(receipt) = environment.receipt(signer)
    else {
        panic!("a cold admission under keys gives a receipt");
    };
    receipt
}

#[test]
fn a_kept_receipt_is_answered_by_the_next_snapshot_alone()
{
    let held = HeldVerdicts::default();
    let receipt = receipt(&KernelSigner::from([3_u8; 32]));
    let before = held.snapshot();
    held.keep(receipt.clone());
    let after = held.snapshot();
    let answered = [Arc::new(receipt.clone())];
    for record in receipt.records() {
        assert!(
            before.receipts(record.key()).is_empty(),
            "a snapshot taken before the keep answers nothing new"
        );
        assert_eq!(
            after.receipts(record.key()),
            answered,
            "every key the receipt holds answers it"
        );
    }
}

#[test]
fn past_the_bound_the_oldest_receipt_goes()
{
    let older = receipt(&KernelSigner::from([3_u8; 32]));
    let newer = receipt(&KernelSigner::from([5_u8; 32]));
    // Every keep merges, and the large index holds one receipt's records.
    let held = HeldVerdicts::bounded(Bounds {
        held: newer.records().len(),
        recent: 0,
    });
    held.keep(older);
    held.keep(newer.clone());
    let snapshot = held.snapshot();
    let answered = [Arc::new(newer.clone())];
    for record in newer.records() {
        assert_eq!(
            snapshot.receipts(record.key()),
            answered,
            "past the bound, a key answers the newer receipt alone"
        );
    }
    assert_eq!(snapshot.large.records, newer.records().len());
    assert_eq!(snapshot.large.order.len(), 1_usize);
    assert_eq!(snapshot.small.records, 0_usize);
}
