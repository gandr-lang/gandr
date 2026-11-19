//! Membership: every key of a tree proves, and every way of altering a proof
//! is refused with the variant that names the alteration.

use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::MembershipProof;
use gandr_storage_records::ProofEnvelope;
use gandr_storage_records::ProofKind;
use gandr_storage_records::ProofNode;
use gandr_storage_records::Record;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::RecordValue;
use proptest::prelude::ProptestConfig;
use proptest::proptest;

use crate::common::Corpus;
use crate::common::CorpusSize;
use crate::common::capped_params;
use crate::common::tree;
use crate::common::tree_with;

#[test]
fn a_valid_proof_verifies()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let proof = built.prove_membership(key).expect("the key is present");

    assert_eq!(proof.verify(&built.root(), key, value), Ok(()));
    assert_eq!(proof.envelope().kind(), ProofKind::Membership);
}

#[test]
fn every_key_of_a_tree_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);

    for record in corpus.entries() {
        let key = record.key();
        let value = record.value();
        let proof = built.prove_membership(key).expect("the key is present");

        assert_eq!(proof.verify(&built.root(), key, value), Ok(()));
        assert!(proof.nodes().len() <= 2);
    }
}

#[test]
fn a_key_of_a_single_leaf_tree_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(5));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is not zero")),
    );
    let key = RecordKey::from(b"key-00000002");
    let value = RecordValue::from(b"value-00000002");
    let proof = built.prove_membership(key).expect("the key is present");

    assert_eq!(proof.nodes().len(), 1);
    assert_eq!(proof.verify(&built.root(), key, value), Ok(()));
}

#[test]
fn an_absent_key_has_no_membership_proof()
{
    let corpus = Corpus::of_size(CorpusSize::from(20));
    let built = tree(&corpus);

    assert!(matches!(
        built.prove_membership(RecordKey::from(b"key-99999999")),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_foreign_root_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let other = tree(&Corpus::of_size(CorpusSize::from(201)));
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let proof = built.prove_membership(key).expect("the key is present");

    assert!(matches!(
        proof.verify(&other.root(), key, value),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_wrong_kind_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let proof = built.prove_membership(key).expect("the key is present");
    let mislabelled = MembershipProof::new(
        ProofEnvelope::new(built.root(), ProofKind::Range),
        proof.root_node_hash(),
        proof.key(),
        proof.value(),
        proof.nodes().to_vec(),
    );

    assert!(matches!(
        mislabelled.verify(&built.root(), key, value),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_different_query_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let proof = built.prove_membership(key).expect("the key is present");

    assert!(matches!(
        proof.verify(&built.root(), RecordKey::from(b"key-00000124"), value),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_wrong_value_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let proof = built.prove_membership(key).expect("the key is present");

    assert!(matches!(
        proof.verify(&built.root(), key, RecordValue::from(b"not the value")),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_forged_binding_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let honest = built.prove_membership(key).expect("the key is present");
    let forged = MembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        RecordValue::from(b"forged"),
        honest.nodes().to_vec(),
    );

    assert!(matches!(
        forged.verify(&built.root(), key, RecordValue::from(b"forged")),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_tampered_node_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let honest = built.prove_membership(key).expect("the key is present");

    let mut nodes = honest.nodes().to_vec();
    let last = nodes.len().saturating_sub(1);
    let claimed = nodes[last].identity();
    let mut bytes = nodes[last].bytes().as_ref().to_vec();
    let end = bytes.len().saturating_sub(1);
    bytes[end] ^= 0x01;
    nodes[last] = ProofNode::new(claimed, bytes);

    let tampered = MembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        honest.value(),
        nodes,
    );

    assert!(matches!(
        tampered.verify(&built.root(), key, value),
        Err(RecordTreeError::HashMismatch { .. })
    ));
}

#[test]
fn an_extra_node_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let honest = built.prove_membership(key).expect("the key is present");

    let mut nodes = honest.nodes().to_vec();
    let all = built.nodes();
    nodes.push(all.last().expect("the tree has nodes").clone());

    let padded = MembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        honest.value(),
        nodes,
    );

    assert!(matches!(
        padded.verify(&built.root(), key, value),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_substituted_leaf_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let honest = built.prove_membership(key).expect("the key is present");
    let all = built.nodes();

    // Every leaf other than the one the key selects, offered in its place.
    let selected = honest.nodes()[1].identity();
    let substitute = all
        .iter()
        .skip(1)
        .find(|node| node.identity() != selected)
        .expect("the tree has more than one leaf");

    let swapped = MembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        honest.value(),
        vec![honest.nodes()[0].clone(), substitute.clone()],
    );

    assert!(matches!(
        swapped.verify(&built.root(), key, value),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_root_node_swapped_for_a_leaf_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123");
    let value = RecordValue::from(b"value-00000123");
    let honest = built.prove_membership(key).expect("the key is present");

    let swapped = MembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        honest.value(),
        vec![honest.nodes()[1].clone(), honest.nodes()[1].clone()],
    );

    assert!(matches!(
        swapped.verify(&built.root(), key, value),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_wrong_manifest_count_is_refused()
{
    for (size, wrong_count) in [(5_usize, 6_u64), (200_usize, 201_u64)] {
        let corpus = Corpus::of_size(CorpusSize::from(size));
        let built = tree_with(
            &corpus,
            capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is not zero")),
        );
        let key = RecordKey::from(b"key-00000002");
        let value = RecordValue::from(b"value-00000002");
        let honest = built.prove_membership(key).expect("the key is present");
        let wrong_root = gandr_storage_records::TreeRoot::seal(
            built.root().params(),
            gandr_storage_records::RecordCount::from(wrong_count),
            honest.root_node_hash(),
        )
        .expect("the manifest parameters are supported");
        let forged = MembershipProof::new(
            ProofEnvelope::new(wrong_root, ProofKind::Membership),
            honest.root_node_hash(),
            key,
            value,
            honest.nodes().to_vec(),
        );
        assert!(matches!(
            forged.verify(&wrong_root, key, value),
            Err(RecordTreeError::InvalidProofShape { .. })
        ));
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn generated_corpora_prove_every_key(sizes in proptest::collection::vec(0_usize ..= 6_usize, 1 ..= 60)) {
        let entries: Vec<Record> = sizes
            .iter()
            .enumerate()
            .map(|(index, width)| {
                Record::new(
                    format!("k{index:06}").into_bytes(),
                    vec![b'v'; *width],
                )
            })
            .collect();
        let corpus = Corpus::of_pairs(entries);
        let built = tree(&corpus);

        for record in corpus.entries() {
            let key = record.key();
            let value = record.value();
            let proof = built.prove_membership(key).expect("the key is present");

            assert_eq!(proof.verify(&built.root(), key, value), Ok(()));
        }
    }
}
