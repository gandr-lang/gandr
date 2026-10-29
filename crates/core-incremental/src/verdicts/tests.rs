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

use super::FileVerdictStore;
use crate::fixture::Label;
use crate::fixture::Scratch;

/// The receipt `signer` gives over a cold admission of two unit definitions.
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
fn a_kept_receipt_is_answered_after_reopening()
{
    let scratch = Scratch::new(Label("verdicts-reopened"));
    let receipt = receipt(&KernelSigner::from([3_u8; 32]));
    let store = FileVerdictStore::open(scratch.path()).expect("the directory opens");
    store.keep(&receipt).expect("the receipt is written");
    let first = receipt
        .records()
        .first()
        .expect("the receipt holds records")
        .key();
    assert!(
        store.receipts(first).is_empty(),
        "a store answers only what it read at open"
    );
    let reopened = FileVerdictStore::open(scratch.path()).expect("the directory reopens");
    let held = [Arc::new(receipt.clone())];
    for record in receipt.records() {
        assert_eq!(
            reopened.receipts(record.key()),
            held,
            "every key the receipt holds answers it"
        );
    }
    assert_eq!(usize::from(reopened.damaged()), 0);
}

#[test]
fn every_receipt_kept_for_a_key_is_answered()
{
    let scratch = Scratch::new(Label("verdicts-two-signers"));
    let ours = receipt(&KernelSigner::from([3_u8; 32]));
    let theirs = receipt(&KernelSigner::from([4_u8; 32]));
    let store = FileVerdictStore::open(scratch.path()).expect("the directory opens");
    store.keep(&ours).expect("our receipt is written");
    store.keep(&theirs).expect("theirs is written");
    let reopened = FileVerdictStore::open(scratch.path()).expect("the directory reopens");
    let (ours_held, theirs_held) = (Arc::new(ours.clone()), Arc::new(theirs));
    for record in ours.records() {
        let answered = reopened.receipts(record.key());
        assert_eq!(answered.len(), 2, "both signers' receipts hold the key");
        assert!(
            answered.contains(&ours_held) && answered.contains(&theirs_held),
            "neither receipt hides the other"
        );
    }
}

#[test]
fn a_damaged_file_is_passed_over()
{
    let scratch = Scratch::new(Label("verdicts-damaged"));
    let receipt = receipt(&KernelSigner::from([3_u8; 32]));
    let store = FileVerdictStore::open(scratch.path()).expect("the directory opens");
    store.keep(&receipt).expect("the receipt is written");
    let written = std::fs::read_dir(scratch.path())
        .expect("the directory lists")
        .map(|entry| entry.expect("an entry reads").path())
        .next()
        .expect("the receipt was written");
    let bytes = std::fs::read(&written).expect("the receipt reads");
    let truncated = bytes.get(.. bytes.len() - 1).expect("in range").to_vec();
    let mut changed = bytes;
    if let Some(last) = changed.last_mut() {
        *last ^= 0x01_u8;
    }
    for (damaged, what) in [
        (truncated, "a truncated receipt"),
        (changed, "a changed verdict byte"),
    ] {
        std::fs::write(&written, &damaged).expect("the damage is written");
        let reopened = FileVerdictStore::open(scratch.path()).expect("the directory reopens");
        assert_eq!(usize::from(reopened.damaged()), 1, "{what}");
        for record in receipt.records() {
            assert!(reopened.receipts(record.key()).is_empty(), "{what}");
        }
    }
}
