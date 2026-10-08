//! Absence: keys below, between and above a tree's records prove, and forged
//! or mis-shaped absence material is refused.

use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::NonMembershipEvidence;
use gandr_storage_records::NonMembershipProof;
use gandr_storage_records::OwnedRecordKey;
use gandr_storage_records::Record;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordTreeError;

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
    let key = RecordKey::from(b"key-00000123x");
    let proof = built.prove_non_membership(key).expect("the key is absent");
    let evidence = proof
        .verify(&built.root(), key)
        .expect("the proof is honest");

    assert_eq!(
        evidence
            .predecessor()
            .map(Record::key)
            .map(|key| key.as_ref().to_vec()),
        Some(b"key-00000123".to_vec())
    );
    assert_eq!(
        evidence
            .successor()
            .map(Record::key)
            .map(|key| key.as_ref().to_vec()),
        Some(b"key-00000124".to_vec())
    );
}

#[test]
fn absent_keys_everywhere_prove()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);

    let below = RecordKey::from(b"aaa");
    let above = RecordKey::from(b"zzz");
    let mut queries = vec![below, above];
    let interleaved: Vec<OwnedRecordKey> = corpus
        .keys()
        .into_iter()
        .map(|key| {
            let mut probe = key.as_ref().to_vec();
            probe.push(b'~');
            OwnedRecordKey::from(probe)
        })
        .collect();
    for probe in &interleaved {
        queries.push(probe.as_borrowed());
    }

    for key in queries {
        let proof = built
            .prove_non_membership(key)
            .expect("the probe keys are absent");
        let evidence = proof
            .verify(&built.root(), key)
            .expect("the proof is honest");

        if let Some(predecessor) = evidence.predecessor() {
            assert!(predecessor.key() < key);
        }
        if let Some(successor) = evidence.successor() {
            assert!(successor.key() > key);
        }
    }
}

#[test]
fn a_key_below_every_record_has_no_predecessor()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let key = RecordKey::from(b"aaa");
    let proof = built.prove_non_membership(key).expect("the key is absent");
    let evidence = proof
        .verify(&built.root(), key)
        .expect("the proof is honest");

    assert_eq!(evidence.predecessor(), None);
    assert_eq!(
        evidence
            .successor()
            .map(Record::key)
            .map(|key| key.as_ref().to_vec()),
        Some(b"key-00000000".to_vec())
    );
}

#[test]
fn a_key_past_the_last_record_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let key = RecordKey::from(b"zzz");
    let proof = built.prove_non_membership(key).expect("the key is absent");
    let evidence = proof
        .verify(&built.root(), key)
        .expect("the proof is honest");

    assert_eq!(evidence.successor(), None);
    assert_eq!(
        evidence
            .predecessor()
            .map(Record::key)
            .map(|key| key.as_ref().to_vec()),
        Some(b"key-00000299".to_vec())
    );
}

#[test]
fn a_key_absent_from_a_single_leaf_tree_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(5));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is not zero")),
    );
    let key = RecordKey::from(b"key-00000002x");
    let proof = built.prove_non_membership(key).expect("the key is absent");

    assert_eq!(proof.nodes().len(), 1);
    assert!(proof.verify(&built.root(), key).is_ok());
}

#[test]
fn a_present_key_has_no_absence_proof()
{
    let corpus = Corpus::of_size(CorpusSize::from(20));
    let built = tree(&corpus);

    assert_eq!(
        built.prove_non_membership(RecordKey::from(b"key-00000003")),
        Err(RecordTreeError::InvalidProofShape {
            context: "the key an absence proof was asked for is present".into(),
        })
    );
}

#[test]
fn forged_evidence_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000123x");
    let honest = built.prove_non_membership(key).expect("the key is absent");
    let forged = NonMembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        NonMembershipEvidence::new(None, None),
        honest.nodes().to_vec(),
    );

    assert_eq!(
        forged.verify(&built.root(), key),
        Err(RecordTreeError::InvalidProofShape {
            context: "the claimed neighbours are not the authenticated ones".into(),
        })
    );
}

#[test]
fn a_missing_successor_leaf_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let key = key_needing_a_successor_leaf(&built, &corpus);
    let honest = built
        .prove_non_membership(key.as_borrowed())
        .expect("the key is absent");
    assert_eq!(honest.nodes().len(), 3);

    let truncated = NonMembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        honest.evidence().clone(),
        honest.nodes()[.. 2].to_vec(),
    );

    assert_eq!(
        truncated.verify(&built.root(), key.as_borrowed()),
        Err(RecordTreeError::InvalidProofShape {
            context: "absence needing the next leaf".into(),
        })
    );
}

#[test]
fn an_unnecessary_successor_leaf_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let key = RecordKey::from(b"key-00000000x");
    let honest = built.prove_non_membership(key).expect("the key is absent");
    assert_eq!(honest.nodes().len(), 2);

    let all = built.nodes();
    let mut nodes = honest.nodes().to_vec();
    nodes.push(all.last().expect("the tree has nodes").clone());
    let padded = NonMembershipProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.key(),
        honest.evidence().clone(),
        nodes,
    );

    assert_eq!(
        padded.verify(&built.root(), key),
        Err(RecordTreeError::InvalidProofShape {
            context: "absence not needing the next leaf".into(),
        })
    );
}

#[test]
fn a_foreign_root_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let other = tree(&Corpus::of_size(CorpusSize::from(199)));
    let key = RecordKey::from(b"key-00000123x");
    let proof = built.prove_non_membership(key).expect("the key is absent");

    assert_eq!(
        proof.verify(&other.root(), key),
        Err(RecordTreeError::InvalidProofShape {
            context: "the proof names a different root".into(),
        })
    );
}

/// Returns an absent key just above some leaf's last record, so the proof needs
/// the following leaf to exhibit a successor.
///
/// # Specification
/// - requires: `built` was built from `corpus`, and the corpus spans more than
///   one leaf, so some leaf's last record has a record after it.
/// - ensures: a key absent from the tree whose absence proof carries three
///   nodes — the root, the selected leaf, and the following leaf the successor
///   comes from.
/// - provides: the one input state the successor-leaf arm of absence is
///   reachable from, found by probing rather than by assuming a leaf boundary
///   position.
/// - panics: when no probed key produces a three-node proof, so a corpus that
///   stopped spanning leaves fails loudly rather than asserting the wrong arm.
fn key_needing_a_successor_leaf(
    built: &gandr_storage_records::RecordTree,
    corpus: &Corpus,
) -> OwnedRecordKey
{
    for record in corpus.entries() {
        let mut probe = record.key().as_ref().to_vec();
        probe.push(b'~');

        if let Ok(proof) = built.prove_non_membership(RecordKey::from(probe.as_slice()))
            && proof.nodes().len() == 3
        {
            return OwnedRecordKey::from(probe);
        }
    }

    panic!("the corpus should contain a leaf-final key");
}
