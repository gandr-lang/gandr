//! A recorded verdict is recalled only under its own key, only on a receipt
//! a trusted signer gave over the records as recorded, and never under the
//! recheck policy.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_kernel_core::Admission;
use gandr_kernel_core::Environment;
use gandr_kernel_core::ExpansionCensus;
use gandr_kernel_core::KernelError;
use gandr_kernel_core::verdict::Attestation;
use gandr_kernel_core::verdict::KernelSigner;
use gandr_kernel_core::verdict::NoVerdicts;
use gandr_kernel_core::verdict::Receipt;
use gandr_kernel_core::verdict::ReceiptSignature;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::StratumBytes;
use gandr_kernel_core::verdict::StratumKey;
use gandr_kernel_core::verdict::TrustPolicy;
use gandr_kernel_core::verdict::VerdictImage;
use gandr_kernel_core::verdict::VerdictKey;
use gandr_kernel_core::verdict::VerdictRecord;
use gandr_kernel_core::verdict::VerdictSource;
use gandr_kernel_core::verdict::stored;
use gandr_kernel_core::verdict::verdict_image;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::FreeCell;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::SealScope;
use gandr_kernel_term::SourceRank;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;
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

/// Admit a unit definition, a second that names the first, then a unit whose
/// body names the constant at `named`; answer how each was admitted.
///
/// # Specification
/// trivial.
fn admit(
    environment: &mut Environment,
    named: ConstantIndex,
) -> Vec<Admission>
{
    [None, Some(ConstantIndex::from(0_usize)), Some(named)]
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
        2,
        "the receipt holds every checked verdict under its entry key, and the two definitions \
         with one content under one entry key"
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
    assert_eq!(
        whole.records().len(),
        2,
        "the two equal units share one entry key, and the third takes its own"
    );
    assert_eq!(
        handed.records().len(),
        1,
        "the copy signs its one declaration alone, under its entry key"
    );
    // A receipt holds its records in key order, so each is found by key.
    for own in handed.records() {
        assert!(
            whole
                .records()
                .binary_search_by_key(&own.key(), VerdictRecord::key)
                .is_ok_and(|found| whole.records().get(found) == Some(own)),
            "the copy keys its declaration as the run would have"
        );
    }

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

/// #6566: a copy handed on reads the source its own run reads. Over the
/// receipt of the run it was copied from, it recalls the declaration that run
/// checked after the copy; over the source it was copied with, it checks it.
#[test]
fn a_resumed_environment_recalls_from_the_source_it_reads_6566()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let named = Some(ConstantIndex::from(0_usize));
    let mut whole = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
    let _first = admit_one(&mut whole, None);
    let _second = admit_one(&mut whole, None);
    let mut reading = whole.handed_on();
    let mut unread = whole.handed_on();
    let _third = admit_one(&mut whole, named);
    let Maybe::Present(receipt) = whole.receipt(&signer)
    else {
        panic!("the run checked declarations under keys");
    };
    reading.reading(Store::holding(&[&receipt]));
    assert_eq!(
        admit_one(&mut reading, named),
        Admission::Recalled,
        "the copy reads the receipt its run's source holds now"
    );
    assert_eq!(
        admit_one(&mut unread, named),
        Admission::Checked,
        "the copy that reads the source it was made with finds nothing"
    );
}

/// Offer a unit definition whose body names the constant at `missing`, which
/// no declaration holds, so the kernel rejects it.
///
/// # Specification
/// trivial.
fn reject_one(
    environment: &mut Environment,
    missing: ConstantIndex,
)
{
    let staged = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_constant(missing);
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    let rejected = environment.add_decl(staged);
    assert!(
        rejected.is_err(),
        "a body naming no declaration is rejected"
    );
}

/// #6566: a rejected declaration enters no environment, so the declarations
/// after it take the keys that a run that never offered it gives them, and a
/// receipt of either run recalls the other's.
#[test]
fn a_rejected_declaration_leaves_the_keys_as_if_never_offered_6566()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let named = Some(ConstantIndex::from(0_usize));
    let mut offered = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
    let _first = admit_one(&mut offered, None);
    reject_one(&mut offered, ConstantIndex::from(9_usize));
    let _second = admit_one(&mut offered, named);
    let mut never = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
    let _first = admit_one(&mut never, None);
    let _second = admit_one(&mut never, named);
    let (Maybe::Present(offered), Maybe::Present(never)) =
        (offered.receipt(&signer), never.receipt(&signer))
    else {
        panic!("each run checked declarations under keys");
    };
    assert_eq!(
        offered.records(),
        never.records(),
        "the run that offered a rejected declaration keys the rest as one that never did"
    );
    let mut recalling = Environment::recalling(trusting(&signer), Store::holding(&[&never]));
    let first = admit_one(&mut recalling, None);
    reject_one(&mut recalling, ConstantIndex::from(9_usize));
    let second = admit_one(&mut recalling, named);
    assert_eq!(
        [first, second],
        [Admission::Recalled; 2],
        "a rejection between them leaves both recalled from the run that never offered it"
    );
}

/// #7426: a rejection keeps its position as a vacancy. A run that rejects a
/// declaration first admits the unit at position 1, so a declaration whose
/// body names constant 0 names the vacancy. That declaration has no entry key,
/// so the kernel checks it and refuses it, though a receipt holds a
/// declaration of the same segment that named an admitted unit. The export of
/// the run then holds the unit alone, and its replay admits nothing that names
/// the vacancy.
#[test]
fn a_declaration_that_names_the_vacancy_of_a_rejection_is_checked_7426()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let mut offered = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
    let _first = admit_one(&mut offered, None);
    reject_one(&mut offered, ConstantIndex::from(9_usize));
    let _second = admit_one(&mut offered, Some(ConstantIndex::from(0_usize)));
    let Maybe::Present(offered) = offered.receipt(&signer)
    else {
        panic!("the run checked declarations under keys");
    };
    let mut vacated = Environment::recalling(trusting(&signer), Store::holding(&[&offered]));
    reject_one(&mut vacated, ConstantIndex::from(9_usize));
    assert_eq!(
        admit_one(&mut vacated, None),
        Admission::Recalled,
        "the unit recalls at position 1"
    );
    let staged = {
        let mut staging = vacated.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_constant(ConstantIndex::from(0_usize));
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    assert!(
        matches!(
            vacated.add_decl(staged),
            Err(KernelError::UnboundConstant { index }) if index == ConstantIndex::from(0_usize)
        ),
        "the declaration that names the vacancy is checked and refused"
    );
    assert_eq!(
        usize::from(vacated.recalls()),
        1,
        "no receipt recalls the declaration that names the vacancy"
    );
    let marked: Vec<_> = vacated
        .entries()
        .iter()
        .map(|entry| MarkedDeclaration::new(AdmissionMark::Checked, entry.declaration().clone()))
        .collect();
    let artifact = decode(encode(vacated.arena(), &marked).as_image()).expect("the export decodes");
    let replayed = Environment::replay(artifact.arena().clone(), artifact.declarations())
        .expect("the export replays");
    assert_eq!(
        replayed.entries().iter().count(),
        1,
        "the export holds the unit alone, and no declaration that names the vacancy"
    );
}

/// A kind of constant that the content encoding writes by its position, since
/// it has no content key.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Positional
{
    /// A declaration that the bypass admits.
    Bypassed,
    /// An abstract type sealed to the end of its sequence.
    OpenSeal,
    /// A declaration whose admission reads an input with no entry key: a
    /// value of an abstract type sealed to the end of its sequence.
    Unkeyed,
}

/// One of the two runs of a probe.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Run
{
    /// The run that gives the receipt.
    First,
    /// The run that reads it.
    Second,
}

/// Admit a constant of `kind` at the next position of `environment`, and
/// answer its position: of the unit in the first run and of the pair of units
/// in the second, after its abstract type for [`Positional::Unkeyed`].
///
/// # Specification
/// trivial.
fn positional_constant(
    environment: &mut Environment,
    (kind, run): (Positional, Run),
) -> ConstantIndex
{
    let first = ConstantIndex::from(usize::from(environment.entries().len()));
    let mut staging = environment.stage();
    let arena = staging.arena();
    let unit = arena.value_type_unit();
    let held = match run {
        Run::First => unit,
        Run::Second => arena.value_type_product(&[unit, unit]),
    };
    match kind {
        Positional::Bypassed => {
            let staged = staging.axiom(LevelSignature::monomorphic(), held);
            let _bypassed = environment
                .add_decl_unchecked(staged)
                .expect("the bypass admits");
            first
        },
        Positional::OpenSeal | Positional::Unkeyed => {
            let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
            let staged = staging.abstract_type(
                LevelSignature::monomorphic(),
                universe,
                held,
                SealScope::Open,
            );
            let _sealed = environment
                .add_decl(staged)
                .expect("the abstract type admits");
            if matches!(kind, Positional::OpenSeal) {
                first
            }
            else {
                let mut staging = environment.stage();
                let arena = staging.arena();
                let declared = arena.value_type_abstract(first);
                let point = arena.value_unit();
                let body = match run {
                    Run::First => point,
                    Run::Second => arena.value_tuple(&[point, point]),
                };
                let staged = staging.def(LevelSignature::monomorphic(), declared, body);
                environment
                    .add_decl(staged)
                    .expect("the value of the abstract type admits")
                    .position()
            }
        },
    }
}

/// Offer `b`, which reads the constant of `kind` at `positional` as of the
/// unit, and answer whether `b` admits.
///
/// # Specification
/// trivial.
fn reader_of(
    environment: &mut Environment,
    (kind, positional): (Positional, ConstantIndex),
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let staged = match kind {
        Positional::Bypassed | Positional::Unkeyed => {
            let declared = arena.value_type_unit();
            let body = arena.value_constant(positional);
            staging.def(LevelSignature::monomorphic(), declared, body)
        },
        Positional::OpenSeal => {
            let declared = arena.value_type_abstract(positional);
            let body = arena.value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        },
    };
    environment.add_decl(staged).map(drop)
}

/// #7426: the content encoding writes a position for a constant with no
/// content key: a declaration that the bypass admits, an abstract type sealed
/// to the end of its sequence, and a declaration that reads such a type. Two
/// runs hold two declarations of one such kind at one position, and `b` names
/// that position. The receipt of the first run holds the unit at position 0.
/// `b` has no entry key, since the constant that it names has no content key.
/// So the second run checks `b` and refuses it, where the first run admits it.
/// A run under a policy that rechecks gives no receipt, which
/// `a_rechecking_environment_recalls_nothing` reads.
#[test]
fn a_declaration_that_names_a_constant_with_no_content_key_is_checked_in_each_run_7426()
{
    let signer = KernelSigner::from([7_u8; 32]);
    for kind in [
        Positional::Bypassed,
        Positional::OpenSeal,
        Positional::Unkeyed,
    ] {
        let mut first = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
        let _unit = admit_one(&mut first, None);
        let positional = positional_constant(&mut first, (kind, Run::First));
        assert!(
            reader_of(&mut first, (kind, positional)).is_ok(),
            "{kind:?}: the first run admits `b`"
        );
        let Maybe::Present(receipt) = first.receipt(&signer)
        else {
            panic!("{kind:?}: the first run checked the unit under its key");
        };
        let mut second = Environment::recalling(trusting(&signer), Store::holding(&[&receipt]));
        assert_eq!(
            admit_one(&mut second, None),
            Admission::Recalled,
            "{kind:?}: the unit recalls at position 0"
        );
        let positional = positional_constant(&mut second, (kind, Run::Second));
        assert!(
            reader_of(&mut second, (kind, positional)).is_err(),
            "{kind:?}: the second run checks `b` and refuses it"
        );
        assert_eq!(
            usize::from(second.recalls()),
            1,
            "{kind:?}: no receipt recalls `b`"
        );
    }
}

/// #4034: a stratum receipt is believed over its own key and image under a
/// policy listing its signer. A changed image, another key, an unlisted signer
/// and the recheck policy believe nothing, and a stratum receipt beside an
/// admission's records recalls none of them.
#[test]
fn a_stratum_receipt_is_believed_only_as_signed_4034()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let key = StratumKey::from([3_u8; 32]);
    let held = [1_u8, 2, 3];
    let image = StratumBytes::from(held.as_slice());
    let receipt = signer.sign_stratum(key, image);
    let policy = trusting(&signer);
    assert_eq!(
        policy.believes_stratum(&receipt, key, image),
        Attestation::Attested
    );
    assert_eq!(
        policy.believes_stratum(&receipt, key, StratumBytes::from([1_u8, 2, 4].as_slice())),
        Attestation::Refused,
        "another image"
    );
    assert_eq!(
        policy.believes_stratum(&receipt, StratumKey::from([4_u8; 32]), image),
        Attestation::Refused,
        "another key"
    );
    let other = KernelSigner::from([8_u8; 32]);
    assert_eq!(
        trusting(&other).believes_stratum(&receipt, key, image),
        Attestation::Refused,
        "an unlisted signer"
    );
    assert_eq!(
        TrustPolicy::Recheck.believes_stratum(&receipt, key, image),
        Attestation::Refused,
        "the recheck policy"
    );

    let named = ConstantIndex::from(0_usize);
    let admitted = recorded(&signer, named);
    let borrowed = StoredReceipt::new(receipt, admitted.records().to_vec());
    let mut again = Environment::recalling(policy, Store::holding(&[&borrowed]));
    assert_eq!(
        admit(&mut again, named),
        [Admission::Checked; 3],
        "a stratum receipt attests no admission"
    );
}

/// How many units a product in these tests holds.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Width(usize);

/// Which form of the tree and forest block a program offers.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Forest
{
    /// A tree is a forest; a forest is empty or a tree and a forest.
    AsWritten,
    /// A forest is also a tree alone.
    Edited,
}

/// One declaration a program in these tests offers.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Offered
{
    /// An axiom of the product of so many units.
    Axiom(Width),
    /// A definition of the product of so many units, as their tuple.
    Value(Width),
    /// A definition of the product of so many units, as the constant at the
    /// position.
    Naming(Width, ConstantIndex),
    /// A definition of the pair of an axiom of two units and one of three,
    /// as the constants at the two positions.
    Pair(ConstantIndex, ConstantIndex),
    /// A unit definition whose body is the unit.
    Unit,
    /// An abstract type represented by the unit, manifest for the next so
    /// many declarations.
    Sealed(Width),
    /// A sort of one point.
    Sort,
    /// The words of one loop at the point of the sort at the position.
    Words(ConstantIndex),
    /// An axiom of the data type at the position.
    Of(ConstantIndex),
    /// The tree and forest block, the tree first.
    Block(Forest),
}

/// Offer `offered` to `environment`; answer how it was admitted, the block's
/// members as one.
///
/// # Specification
/// trivial.
fn offer(
    environment: &mut Environment,
    offered: Offered,
) -> Admission
{
    offer_ranked(environment, offered, None)
}

/// Offer `offered` to `environment` ranked at `rank`, or at its position
/// when `rank` is none; answer how it was admitted, the block's members as
/// one and at their positions.
///
/// # Specification
/// trivial.
fn offer_ranked(
    environment: &mut Environment,
    offered: Offered,
    rank: Option<SourceRank>,
) -> Admission
{
    let next = ConstantIndex::from(usize::from(environment.entries().len()));
    let mut staging = environment.stage();
    let arena = staging.arena();
    let unit = arena.value_type_unit();
    let point = arena.value_unit();
    let product =
        |arena: &mut TermArena, width: Width| arena.value_type_product(&alloc::vec![unit; width.0]);
    let monomorphic = LevelSignature::monomorphic;
    let staged = match offered {
        Offered::Axiom(width) => {
            let declared = product(arena, width);
            staging.axiom(monomorphic(), declared)
        },
        Offered::Value(width) => {
            let declared = product(arena, width);
            let body = arena.value_tuple(&alloc::vec![point; width.0]);
            staging.def(monomorphic(), declared, body)
        },
        Offered::Naming(width, constant) => {
            let declared = product(arena, width);
            let body = arena.value_constant(constant);
            staging.def(monomorphic(), declared, body)
        },
        Offered::Pair(left, right) => {
            let two = product(arena, Width(2));
            let three = product(arena, Width(3));
            let declared = arena.value_type_product(&[two, three]);
            let left = arena.value_constant(left);
            let right = arena.value_constant(right);
            let body = arena.value_tuple(&[left, right]);
            staging.def(monomorphic(), declared, body)
        },
        Offered::Unit => staging.def(monomorphic(), unit, point),
        Offered::Sealed(width) => {
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            staging.abstract_type(
                monomorphic(),
                kind,
                unit,
                SealScope::Closed(SealExtent::from(width.0)),
            )
        },
        Offered::Sort => {
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            staging.data(
                monomorphic(),
                alloc::vec![],
                alloc::vec![alloc::vec![]],
                kind,
            )
        },
        Offered::Words(sort) => {
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let own = arena.value_type_data(next, alloc::vec![]);
            let base = || -> Box<[RuleNode]> {
                [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
            };
            let cells = FreeCells::new(sort, alloc::vec![FreeCell::new(base(), base())]);
            staging
                .data(
                    monomorphic(),
                    alloc::vec![],
                    alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                    kind,
                )
                .presented(Presentation::words(cells))
        },
        Offered::Of(family) => {
            let declared = arena.value_type_data(family, alloc::vec![]);
            staging.axiom(monomorphic(), declared)
        },
        Offered::Block(form) => {
            let forest = ConstantIndex::from(usize::from(next).saturating_add(1));
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let forests = arena.value_type_data(forest, alloc::vec![]);
            let tree = staging.data(
                monomorphic(),
                alloc::vec![],
                alloc::vec![alloc::vec![forests]],
                kind,
            );
            let mut staging = environment.stage();
            let arena = staging.arena();
            let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
            let trees = arena.value_type_data(next, alloc::vec![]);
            let forests = arena.value_type_data(forest, alloc::vec![]);
            let mut constructors = alloc::vec![alloc::vec![], alloc::vec![trees, forests]];
            if matches!(form, Forest::Edited) {
                constructors.push(alloc::vec![trees]);
            }
            let list = staging.data(monomorphic(), alloc::vec![], constructors, kind);
            let _block = environment
                .add_block(alloc::vec![tree, list])
                .expect("the block admits");
            return Admission::Checked;
        },
    };
    let staged = match rank {
        Some(rank) => staged.ranked(rank),
        None => staged,
    };
    let admitted = environment
        .add_decl(staged)
        .expect("each declaration of these programs admits");
    environment
        .entries()
        .get(usize::from(admitted.position()))
        .expect("it was appended")
        .admission()
}

/// Offer a definition of the point of the sort at `sort`; answer its check's
/// census.
///
/// # Specification
/// trivial.
fn point_of(
    environment: &mut Environment,
    sort: ConstantIndex,
) -> ExpansionCensus
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let declared = arena.value_type_data(sort, alloc::vec![]);
    let body =
        arena.value_constructor(sort, declared, ConstructorTag::from(0_usize), alloc::vec![]);
    let staged = staging.def(LevelSignature::monomorphic(), declared, body);
    let admitted = environment
        .add_decl(staged)
        .expect("the point of a sort admits");
    match environment
        .entries()
        .get(usize::from(admitted.position()))
        .expect("it was appended")
        .census()
    {
        Maybe::Present(census) => census,
        Maybe::Absent(absent) => panic!("the point is checked here: {absent:?}"),
    }
}

/// #7341: a plain definition that reads a data type keeps the names of its
/// goals when an edit moves the data type. The edit retires the sort and its
/// point, admits a unit definition before them, and admits them again two
/// positions later. The session names the sort by its content key at both
/// positions, so the outcomes that the first check of the point kept answer
/// the second.
#[test]
fn the_point_of_a_moved_sort_stands_on_the_outcomes_of_its_first_check_7341()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let mut environment = Environment::recalling(trusting(&signer), Arc::new(NoVerdicts));
    let sort = ConstantIndex::from(0_usize);
    assert_eq!(offer(&mut environment, Offered::Sort), Admission::Checked);
    let first = point_of(&mut environment, sort);
    environment
        .retire(&[sort, ConstantIndex::from(1_usize)])
        .expect("the sort and its point retire");
    assert_eq!(offer(&mut environment, Offered::Unit), Admission::Checked);
    assert_eq!(offer(&mut environment, Offered::Sort), Admission::Checked);
    let moved = point_of(&mut environment, ConstantIndex::from(3_usize));
    assert!(
        u64::from(first.expansions()) > 0,
        "the first check of the point expands its goals: {first:?}"
    );
    assert!(
        u64::from(moved.kept()) > 0,
        "the point of the moved sort reads the outcomes that the first check kept: {moved:?}"
    );
    assert!(
        u64::from(moved.expansions()) < u64::from(first.expansions()),
        "the point of the moved sort expands fewer goals than its first check: {moved:?} \
         against {first:?}"
    );
}

/// The receipt `signer` gave over a cold run of `program`.
///
/// # Specification
/// trivial.
fn recorded_program(
    signer: &KernelSigner,
    program: &[Offered],
) -> StoredReceipt
{
    let mut cold = Environment::recalling(trusting(signer), Arc::new(NoVerdicts));
    for &offered in program {
        assert_eq!(
            offer(&mut cold, offered),
            Admission::Checked,
            "a cold run checks every declaration"
        );
    }
    let Maybe::Present(receipt) = cold.receipt(signer)
    else {
        panic!("a run that checked declarations under keys gives a receipt");
    };
    receipt
}

/// How each declaration of `program` is admitted in a run that trusts
/// `signer` and reads `receipt`.
///
/// # Specification
/// trivial.
fn rerun(
    signer: &KernelSigner,
    receipt: &StoredReceipt,
    program: &[Offered],
) -> Vec<Admission>
{
    let mut environment = Environment::recalling(trusting(signer), Store::holding(&[receipt]));
    program
        .iter()
        .map(|&offered| offer(&mut environment, offered))
        .collect()
}

/// #6568: an edit re-keys the declarations that read the edited one and no
/// other, and a declaration keeps its key at a new position. A run that
/// offers a new axiom first and edits the first axiom recalls each
/// declaration but the new one, the edited one and the one that reads it.
#[test]
fn an_edit_re_keys_only_what_reads_it_6568()
{
    use Admission::Checked;
    use Admission::Recalled;
    let signer = KernelSigner::from([7_u8; 32]);
    let at = ConstantIndex::from;
    let receipt = recorded_program(&signer, &[
        Offered::Axiom(Width(2)),
        Offered::Axiom(Width(3)),
        Offered::Naming(Width(2), at(0_usize)),
        Offered::Naming(Width(3), at(1_usize)),
    ]);
    assert_eq!(
        rerun(&signer, &receipt, &[
            Offered::Axiom(Width(4)),
            Offered::Value(Width(2)),
            Offered::Axiom(Width(3)),
            Offered::Naming(Width(2), at(1_usize)),
            Offered::Naming(Width(3), at(2_usize)),
        ]),
        [Checked, Checked, Recalled, Checked, Recalled],
        "the new axiom, the edited one and its reader are checked, and the rest keep their keys"
    );
}

/// #6568, narrowed by #6621: the key of a declaration that carries no
/// operation rules reads no admission order. A definition naming two axioms
/// is recalled when the two are admitted, and ranked, in the other order.
/// The key of a ruled definition reads the rank order of the operations its
/// rules name, because the path order compares them. Its twin,
/// `ruled::tests::a_ruled_definition_is_keyed_by_the_rank_order_of_what_it_names_6621`,
/// checks such a definition again when two of those operations swap ranks.
#[test]
fn a_key_reads_no_admission_order_6568()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let at = ConstantIndex::from;
    let receipt = recorded_program(&signer, &[
        Offered::Axiom(Width(2)),
        Offered::Axiom(Width(3)),
        Offered::Pair(at(0_usize), at(1_usize)),
    ]);
    assert_eq!(
        rerun(&signer, &receipt, &[
            Offered::Axiom(Width(3)),
            Offered::Axiom(Width(2)),
            Offered::Pair(at(1_usize), at(0_usize)),
        ]),
        [Admission::Recalled; 3]
    );
}

/// #6568: two axioms of one type are two constants, so they take two keys. A
/// definition naming the first is not recalled from the record of one naming
/// the second.
#[test]
fn two_axioms_of_one_type_take_two_keys_6568()
{
    use Admission::Checked;
    use Admission::Recalled;
    let signer = KernelSigner::from([7_u8; 32]);
    let at = ConstantIndex::from;
    let twice = |named: ConstantIndex| {
        [
            Offered::Axiom(Width(2)),
            Offered::Axiom(Width(2)),
            Offered::Naming(Width(2), named),
        ]
    };
    let receipt = recorded_program(&signer, &twice(at(1_usize)));
    assert_eq!(
        rerun(&signer, &receipt, &twice(at(0_usize))),
        [Recalled, Recalled, Checked],
        "the first axiom is not the second"
    );
    assert_eq!(rerun(&signer, &receipt, &twice(at(1_usize))), [Recalled; 3]);
}

/// #6568: a declaration in an atom's scope reads the atom as its
/// representation, so it takes another key than the same declaration outside
/// the scope.
#[test]
fn an_atom_manifest_at_a_declaration_keys_it_6568()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let receipt = recorded_program(&signer, &[Offered::Sealed(Width(1)), Offered::Unit]);
    assert_eq!(
        rerun(&signer, &receipt, &[
            Offered::Sealed(Width(1)),
            Offered::Unit,
            Offered::Unit
        ]),
        [Admission::Recalled, Admission::Recalled, Admission::Checked],
        "the second unit is outside the atom's scope"
    );
}

/// #6568: a type of words over a sort a declaration reaches re-keys the
/// declaration, and one over another sort does not.
#[test]
fn words_over_a_reached_sort_re_key_a_declaration_6568()
{
    use Admission::Checked;
    use Admission::Recalled;
    let signer = KernelSigner::from([7_u8; 32]);
    let at = ConstantIndex::from;
    let receipt = recorded_program(&signer, &[
        Offered::Sort,
        Offered::Sort,
        Offered::Of(at(0_usize)),
    ]);
    let after = |sort: ConstantIndex| {
        [
            Offered::Sort,
            Offered::Sort,
            Offered::Words(sort),
            Offered::Of(at(0_usize)),
        ]
    };
    assert_eq!(
        rerun(&signer, &receipt, &after(at(1_usize))),
        [Recalled, Recalled, Checked, Recalled],
        "words over the other sort"
    );
    assert_eq!(
        rerun(&signer, &receipt, &after(at(0_usize))),
        [Recalled, Recalled, Checked, Checked],
        "words over the sort the axiom reads"
    );
}

/// #6621: a key reads only the types of words ranked below the declaration.
/// Words over the sort an axiom reads, admitted before the axiom but ranked
/// above it, leave the axiom's key as a run without them keys it; ranked
/// below it, they re-key it.
#[test]
fn words_ranked_above_a_declaration_do_not_re_key_it_6621()
{
    use Admission::Checked;
    use Admission::Recalled;
    let signer = KernelSigner::from([7_u8; 32]);
    let at = ConstantIndex::from;
    let rank = |place: usize| Some(SourceRank::from(place));
    let receipt = recorded_program(&signer, &[Offered::Sort, Offered::Of(at(0_usize))]);
    let ranked = |words: usize| {
        let mut environment =
            Environment::recalling(trusting(&signer), Store::holding(&[&receipt]));
        [
            offer_ranked(&mut environment, Offered::Sort, rank(0_usize)),
            offer_ranked(&mut environment, Offered::Words(at(0_usize)), rank(words)),
            offer_ranked(&mut environment, Offered::Of(at(0_usize)), rank(2_usize)),
        ]
    };
    assert_eq!(
        ranked(3_usize),
        [Recalled, Checked, Recalled],
        "words ranked above the axiom"
    );
    assert_eq!(
        ranked(1_usize),
        [Recalled, Checked, Checked],
        "words ranked below the axiom"
    );
}

/// #6568: a mutual block is keyed whole, and each member by its place in it.
/// A declaration that reads a member keeps its key when the block moves, and
/// an edit of the other member re-keys it.
#[test]
fn a_block_member_is_keyed_by_its_whole_block_6568()
{
    use Admission::Checked;
    use Admission::Recalled;
    let signer = KernelSigner::from([7_u8; 32]);
    let at = ConstantIndex::from;
    let receipt = recorded_program(&signer, &[
        Offered::Block(Forest::AsWritten),
        Offered::Of(at(0_usize)),
    ]);
    assert_eq!(
        rerun(&signer, &receipt, &[
            Offered::Axiom(Width(2)),
            Offered::Block(Forest::AsWritten),
            Offered::Of(at(1_usize)),
        ]),
        [Checked, Checked, Recalled],
        "a block is checked, and the axiom of its tree keeps its key"
    );
    assert_eq!(
        rerun(&signer, &receipt, &[
            Offered::Block(Forest::Edited),
            Offered::Of(at(0_usize)),
        ]),
        [Checked, Checked],
        "an edit of the forest re-keys the tree"
    );
}

/// The receipt that `landing` gave at `48e710d73`, before #6621, over a cold
/// run of the program [`admit`] offers naming the first unit, under the key
/// of the seed `[7; 32]`: its signature, then the key and the bytes of each
/// record.
const BEFORE_THE_RANK: (&str, [(&str, &str); 5]) = (
    "1e19147ddf0163c90bb47cea5c3eacce80d6771a80156f222be7075deca440ed4e3ea764fc6ec435b7f4c6f198f9bbbdc41f5b6a5b91c5312a5230d1ef80cf0a",
    [
        (
            "53185b618dd2bf08da575ec9625a3e4d87071118bfd8b6840c6b9761b39db1f6",
            "0101000000000000000000",
        ),
        (
            "90c9993f5dd27504ade47b1a6f0286d105d2cab21bb949a87d8c3558796dc0e1",
            "0101000000000000000000",
        ),
        (
            "afe7287a3cb3d32a9cad07dee150936ee3222466e003c061b2dd4f4001b65ba0",
            "0101000000000000000000",
        ),
        (
            "d653946cdc1c2847bc69d3c330275a5b2da70dddb4465ed274fc5c11e7d7eb56",
            "0101000000000000000000",
        ),
        (
            "fb4a16c4caa9e5907aaedbd196652f71886aa36d1b17131f23966c7fb2aaa435",
            "0101000000000000000000",
        ),
    ],
);

/// #6621: a store that a kernel without ranks wrote reads a miss. No key of
/// its receipt is a key this kernel computes for the same program, so a run
/// that reads the store recalls nothing and checks each declaration, as a
/// fresh run does.
#[test]
fn a_store_written_before_the_rank_reads_a_miss_6621()
{
    let signer = KernelSigner::from([7_u8; 32]);
    let named = ConstantIndex::from(0_usize);
    // The bytes the hexadecimal digits spell, two digits a byte.
    let spelled = |digits: &str| -> Vec<u8> {
        digits
            .as_bytes()
            .chunks(2)
            .map(|pair| {
                core::str::from_utf8(pair)
                    .ok()
                    .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                    .expect("the fixture spells bytes in hexadecimal")
            })
            .collect()
    };
    let (signature, records) = BEFORE_THE_RANK;
    let signature: [u8; 64] = spelled(signature)
        .try_into()
        .expect("a signature is 64 bytes");
    let records = records
        .iter()
        .map(|&(key, image)| {
            let key: [u8; 32] = spelled(key).try_into().expect("a key is 32 bytes");
            let image = spelled(image);
            let Maybe::Present(record) =
                VerdictRecord::decode(VerdictKey::from(key), VerdictImage::from(image.as_slice()))
            else {
                panic!("the fixture holds records this kernel reads");
            };
            record
        })
        .collect();
    let before = StoredReceipt::new(
        Receipt::new(signer.identity(), ReceiptSignature::from(signature)),
        records,
    );
    let keys = |receipt: &StoredReceipt| {
        receipt
            .records()
            .iter()
            .map(VerdictRecord::key)
            .collect::<BTreeSet<_>>()
    };
    assert!(
        keys(&before).is_disjoint(&keys(&recorded(&signer, named))),
        "no key of the old store is a key of this kernel"
    );
    let mut environment = Environment::recalling(trusting(&signer), Store::holding(&[&before]));
    assert_eq!(
        admit(&mut environment, named),
        [Admission::Checked; 3],
        "a run over the old store checks each declaration"
    );
    assert_eq!(usize::from(environment.recalls()), 0, "and recalls nothing");
}
