//! A recorded verdict is recalled only under its own key, only on a receipt
//! a trusted signer gave over the records as recorded, and never under the
//! recheck policy.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_kernel_core::Admission;
use gandr_kernel_core::Environment;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::NoVerdicts;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_kernel_core::verdict::VerdictImage;
use gandr_kernel_core::verdict::VerdictKey;
use gandr_kernel_core::verdict::VerdictRecord;
use gandr_kernel_core::verdict::VerdictSource;
use gandr_kernel_core::verdict::stored;
use gandr_kernel_core::verdict::verdict_image;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::LevelSignature;
use quenchant_shape::shape::Maybe;

/// A store holding receipts, each answered for every key it attests.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
#[repr(transparent)]
struct Store(BTreeMap<VerdictKey, Vec<Arc<StoredReceipt>>>);

impl Store
{
    /// The store holding each of `stored`, answered in that order for each
    /// of its records' keys.
    ///
    /// # Specification
    /// trivial.
    fn holding(stored: &[&StoredReceipt]) -> Arc<Self>
    {
        let mut index: BTreeMap<VerdictKey, Vec<Arc<StoredReceipt>>> = BTreeMap::new();
        for &receipt in stored {
            let receipt = Arc::new(receipt.clone());
            for record in receipt.records() {
                index
                    .entry(record.key())
                    .or_default()
                    .push(Arc::clone(&receipt));
            }
        }
        Arc::new(Self(index))
    }
}

impl VerdictSource for Store
{
    /// The receipts kept for `key`.
    ///
    /// # Specification
    /// trivial.
    fn receipts(
        &self,
        key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        self.0.get(&key).map_or(&[], Vec::as_slice)
    }
}

/// Admit a unit definition whose body is the unit, or names the constant
/// `body` holds; answer how it was admitted.
///
/// # Specification
/// trivial.
fn admit_one(
    environment: &mut Environment,
    body: Option<ConstantIndex>,
) -> Admission
{
    let staged = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = match body {
            Some(constant) => staging.arena().value_constant(constant),
            None => staging.arena().value_unit(),
        };
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    let admitted = environment
        .add_decl(staged)
        .expect("a unit definition admits");
    environment
        .entries()
        .get(usize::from(admitted.position()))
        .expect("it was appended")
        .admission()
}

/// Admit two unit definitions, then a unit whose body names the constant at
/// `named`; answer how each was admitted.
///
/// # Specification
/// trivial.
fn admit(
    environment: &mut Environment,
    named: ConstantIndex,
) -> Vec<Admission>
{
    [None, None, Some(named)]
        .into_iter()
        .map(|body| admit_one(environment, body))
        .collect()
}

/// The policy trusting `signer` alone.
///
/// # Specification
/// trivial.
fn trusting(signer: &KernelSigner) -> TrustPolicy
{
    TrustPolicy::Trusted(BTreeSet::from([signer.identity()]))
}

/// The receipt `signer` gave over a cold run of the program naming the
/// constant at `named`.
///
/// # Specification
/// trivial.
fn recorded(
    signer: &KernelSigner,
    named: ConstantIndex,
) -> StoredReceipt
{
    let mut first = Environment::recalling(trusting(signer), Arc::new(NoVerdicts));
    assert_eq!(
        admit(&mut first, named),
        [Admission::Checked; 3],
        "a cold run checks every declaration"
    );
    let Maybe::Present(receipt) = first.receipt(signer)
    else {
        panic!("a run that checked declarations under keys gives a receipt");
    };
    receipt
}

#[test]
fn a_verdict_is_recalled_only_under_its_own_key()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let first_unit = ConstantIndex::from(0_usize);
    let receipt = recorded(&signer, first_unit);
    assert_eq!(
        receipt.records().len(),
        3,
        "the receipt holds every checked verdict"
    );

    let mut again = Environment::recalling(trusting(&signer), Store::holding(&[&receipt]));
    assert_eq!(
        admit(&mut again, first_unit),
        [Admission::Recalled; 3],
        "the same input recalls every verdict"
    );
    assert_eq!(usize::from(again.recalls()), 3);
    assert!(
        matches!(
            again.receipt(&signer),
            Maybe::Absent(stored::Absent::Unrecorded)
        ),
        "a recalled verdict is never signed again"
    );

    let mut renamed = Environment::recalling(trusting(&signer), Store::holding(&[&receipt]));
    assert_eq!(
        admit(&mut renamed, ConstantIndex::from(1_usize)),
        [Admission::Recalled, Admission::Recalled, Admission::Checked],
        "naming the second unit instead of the first is another input for the last \
         declaration alone"
    );
}

#[test]
fn an_unlisted_signer_recalls_nothing()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let other = KernelSigner::from([9_u8; 32]);
    let named = ConstantIndex::from(0_usize);
    let receipt = recorded(&signer, named);
    let mut environment = Environment::recalling(trusting(&other), Store::holding(&[&receipt]));
    assert_eq!(
        admit(&mut environment, named),
        [Admission::Checked; 3],
        "a receipt whose signer the policy does not list is not believed"
    );
    assert_eq!(usize::from(environment.recalls()), 0);
}

#[test]
fn a_tampered_record_recalls_nothing()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let named = ConstantIndex::from(0_usize);
    let receipt = recorded(&signer, named);
    let mut records = receipt.records().to_vec();
    let first = records.first().expect("the receipt holds records").clone();
    let mut bytes = first.encoded().as_ref().to_vec();
    let stratification = bytes
        .get_mut(1)
        .expect("a verdict records its stratification");
    *stratification ^= 1;
    let Maybe::Present(tampered) =
        VerdictRecord::decode(first.key(), VerdictImage::from(bytes.as_slice()))
    else {
        panic!("the other stratification is a well-formed verdict");
    };
    assert_ne!(tampered, first);
    *records.first_mut().expect("the receipt holds records") = tampered;
    let altered = StoredReceipt::new(receipt.receipt(), records);
    let mut environment = Environment::recalling(trusting(&signer), Store::holding(&[&altered]));
    assert_eq!(
        admit(&mut environment, named),
        [Admission::Checked; 3],
        "a receipt whose records were altered after signing verifies over none of them"
    );
}

/// A receipt a foreign signer gave over the same records as a trusted one
/// hides nothing: in whichever order the store answers them, the trusted one
/// is found and every verdict recalled.
#[test]
fn a_trusted_receipt_is_found_beside_a_foreign_one()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let foreign = KernelSigner::from([9_u8; 32]);
    let named = ConstantIndex::from(0_usize);
    let trusted = recorded(&signer, named);
    let other = recorded(&foreign, named);
    for store in [
        Store::holding(&[&other, &trusted]),
        Store::holding(&[&trusted, &other]),
    ] {
        let mut environment = Environment::recalling(trusting(&signer), store);
        assert_eq!(
            admit(&mut environment, named),
            [Admission::Recalled; 3],
            "the trusted receipt answers whichever comes first"
        );
    }
}

#[test]
fn a_rechecking_environment_recalls_nothing()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let named = ConstantIndex::from(0_usize);
    let receipt = recorded(&signer, named);
    let mut environment = Environment::recalling(TrustPolicy::Recheck, Store::holding(&[&receipt]));
    assert_eq!(
        admit(&mut environment, named),
        [Admission::Checked; 3],
        "the recheck policy replays every declaration"
    );
    assert!(
        matches!(
            environment.receipt(&signer),
            Maybe::Absent(stored::Absent::Unrecorded)
        ),
        "and keys none, so it records none"
    );
}

#[test]
fn a_record_reads_back_and_a_damaged_one_is_refused()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let receipt = recorded(&signer, ConstantIndex::from(0_usize));
    for record in receipt.records() {
        let encoded = record.encoded();
        assert_eq!(
            VerdictRecord::decode(record.key(), VerdictImage::from(encoded.as_ref())),
            Maybe::Present(record.clone()),
            "a record reads back from its bytes"
        );
    }
    let record = receipt
        .records()
        .first()
        .expect("the receipt records a verdict");
    let bytes = record.encoded().as_ref().to_vec();
    let mut versioned = bytes.clone();
    *versioned
        .first_mut()
        .expect("a verdict leads with its version") = 2;
    let mut trailing = bytes.clone();
    trailing.push(0);
    let short = bytes.split_last().expect("a verdict is not empty").1;
    for damaged in [versioned.as_slice(), trailing.as_slice(), short] {
        assert_eq!(
            VerdictRecord::decode(record.key(), VerdictImage::from(damaged)),
            Maybe::Absent(verdict_image::Absent::Malformed),
            "{damaged:?}"
        );
    }
}

#[test]
fn a_handed_on_environment_keys_on_and_signs_only_its_own()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let named = Some(ConstantIndex::from(0_usize));
    let mut whole = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
    let _first = admit_one(&mut whole, None);
    let _second = admit_one(&mut whole, None);
    let mut handed = whole.handed_on();
    assert!(
        matches!(
            handed.receipt(&signer),
            Maybe::Absent(stored::Absent::Unrecorded)
        ),
        "the copy signs none of what the run before it checked"
    );
    let _third = admit_one(&mut whole, named);
    let _again = admit_one(&mut handed, named);
    let (Maybe::Present(whole), Maybe::Present(handed)) =
        (whole.receipt(&signer), handed.receipt(&signer))
    else {
        panic!("each run checked a declaration under keys");
    };
    assert_eq!(whole.records().len(), 3);
    let [ref own] = *handed.records()
    else {
        panic!("the copy signs its one declaration alone");
    };
    assert!(
        whole.records().contains(own),
        "the copy keys its declaration as the run would have"
    );

    let mut recalling = Environment::recalling(trusting(&signer), Store::holding(&[&whole]));
    let _recalled = admit_one(&mut recalling, None);
    let _recalled = admit_one(&mut recalling, None);
    assert_eq!(usize::from(recalling.recalls()), 2);
    let mut handed = recalling.handed_on();
    assert_eq!(
        usize::from(handed.recalls()),
        0,
        "the run's recalls stay its own"
    );
    assert_eq!(admit_one(&mut handed, named), Admission::Recalled);
    assert_eq!(usize::from(handed.recalls()), 1);
}
