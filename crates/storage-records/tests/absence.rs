//! Absence: keys below, between and above a tree's records prove, and forged
//! or mis-shaped absence material is refused.

use anodized::spec;
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

    assert_eq!(evidence.predecessor(), corpus.entries().get(123));
    assert_eq!(evidence.successor(), corpus.entries().get(124));
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

        assert_eq!(
            evidence.predecessor(),
            corpus.entries().iter().rfind(|record| record.key() < key)
        );
        assert_eq!(
            evidence.successor(),
            corpus.entries().iter().find(|record| key < record.key())
        );
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
    assert_eq!(evidence.successor(), corpus.entries().first());
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
    assert_eq!(evidence.predecessor(), corpus.entries().last());
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
    let evidence = proof
        .verify(&built.root(), key)
        .expect("the proof is honest");
    assert_eq!(evidence.predecessor(), corpus.entries().get(2));
    assert_eq!(evidence.successor(), corpus.entries().get(3));
}

#[test]
fn a_present_key_has_no_absence_proof()
{
    let corpus = Corpus::of_size(CorpusSize::from(20));
    let built = tree(&corpus);

    assert!(matches!(
        built.prove_non_membership(RecordKey::from(b"key-00000003")),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
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

    assert!(matches!(
        forged.verify(&built.root(), key),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
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

    assert!(matches!(
        truncated.verify(&built.root(), key.as_borrowed()),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
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

    assert!(matches!(
        padded.verify(&built.root(), key),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_foreign_root_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let built = tree(&corpus);
    let other = tree(&Corpus::of_size(CorpusSize::from(199)));
    let key = RecordKey::from(b"key-00000123x");
    let proof = built.prove_non_membership(key).expect("the key is absent");

    assert!(matches!(
        proof.verify(&other.root(), key),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn an_empty_tree_proves_absence()
{
    let built = tree(&Corpus::of_size(CorpusSize::from(0)));
    let key = RecordKey::from(b"missing");
    let proof = built
        .prove_non_membership(key)
        .expect("the empty tree has no key");
    let evidence = proof
        .verify(&built.root(), key)
        .expect("the empty-tree proof is honest");
    assert_eq!(evidence.predecessor(), None);
    assert_eq!(evidence.successor(), None);

    let forged = NonMembershipProof::new(
        proof.envelope(),
        proof.root_node_hash(),
        key,
        NonMembershipEvidence::new(Some(Record::new(b"a", b"invented")), None),
        proof.nodes().to_vec(),
    );
    assert!(matches!(
        forged.verify(&built.root(), key),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_present_key_is_refused_by_verification()
{
    for size in [5_usize, 200_usize] {
        let corpus = Corpus::of_size(CorpusSize::from(size));
        let built = tree_with(
            &corpus,
            capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is not zero")),
        );
        let honest = built
            .prove_non_membership(RecordKey::from(b"key-00000002x"))
            .expect("the query is absent");
        let mut nodes = honest.nodes().to_vec();
        nodes.truncate(2);
        let present = RecordKey::from(b"key-00000002");
        let forged = NonMembershipProof::new(
            honest.envelope(),
            honest.root_node_hash(),
            present,
            honest.evidence().clone(),
            nodes,
        );
        assert!(matches!(
            forged.verify(&built.root(), present),
            Err(RecordTreeError::InvalidProofShape { .. })
        ));
    }
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
///
/// # Adequacy
/// - hypothesis: L3 queries in the 300-record corpus yield a three-node absence
///   proof whose successor leaf is necessary. Removing it is refused,
///   distinguishing a probe that accidentally selects a two-node layout.
/// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
#[spec(ensures: |ret| built.lookup(ret.as_borrowed()).is_none()
    && built.prove_non_membership(ret.as_borrowed()).is_ok_and(|proof| proof.nodes().len() == 3_usize))]
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
