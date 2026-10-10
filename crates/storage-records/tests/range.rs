//! Ranges: a proof returns exactly the range's records, and neither an omitted
//! record nor an invented one survives verification.

use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::KeyBound;
use gandr_storage_records::KeyRange;
use gandr_storage_records::RangeProof;
use gandr_storage_records::Record;
use gandr_storage_records::RecordTreeError;
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
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let range = KeyRange::new(
        KeyBound::included(b"key-00000100"),
        KeyBound::included(b"key-00000149"),
    )
    .expect("the bounds are ordered");
    let proof = built.prove_range(range).expect("the tree can answer");
    let records = proof
        .verify(&built.root(), range)
        .expect("the proof is honest");

    assert_eq!(
        records.as_ref(),
        corpus
            .entries()
            .get(100 .. 150)
            .expect("the requested interval is in the corpus")
    );
}

#[test]
fn the_unbounded_range_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let range = KeyRange::all();
    let proof = built.prove_range(range).expect("the tree can answer");
    let records = proof
        .verify(&built.root(), range)
        .expect("the proof is honest");

    assert_eq!(records.as_ref(), corpus.entries());
    assert_eq!(proof.nodes().len(), built.nodes().len());
}

#[test]
fn an_empty_range_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let range = KeyRange::new(
        KeyBound::included(b"key-00000100"),
        KeyBound::excluded(b"key-00000100"),
    )
    .expect("the bounds are ordered");
    let proof = built.prove_range(range).expect("the tree can answer");
    let records = proof
        .verify(&built.root(), range)
        .expect("the proof is honest");

    assert_eq!(records.as_ref(), [].as_slice());
}

#[test]
fn a_span_past_the_node_budget_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(0x1000));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(1_u32).expect("the cap is not zero")),
    );

    assert!(matches!(
        built.prove_range(KeyRange::all()),
        Err(RecordTreeError::BudgetExceeded { .. })
    ));
}

#[test]
fn the_node_budget_ceiling_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(0x0FFF));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(1_u32).expect("the cap is not zero")),
    );
    let range = KeyRange::all();
    let proof = built
        .prove_range(range)
        .expect("the span fits the node budget");
    let records = proof
        .verify(&built.root(), range)
        .expect("the proof is honest");

    assert_eq!(records.as_ref(), corpus.entries());
}

#[test]
fn a_range_over_a_single_leaf_tree_proves()
{
    let corpus = Corpus::of_size(CorpusSize::from(6));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is not zero")),
    );
    let range = KeyRange::new(
        KeyBound::included(b"key-00000001"),
        KeyBound::included(b"key-00000003"),
    )
    .expect("the bounds are ordered");
    let proof = built.prove_range(range).expect("the tree can answer");

    assert_eq!(proof.nodes().len(), 1);
    assert_eq!(
        proof
            .verify(&built.root(), range)
            .expect("the proof is honest")
            .as_ref(),
        corpus
            .entries()
            .get(1 .. 4)
            .expect("the requested interval is in the corpus")
    );
}

#[test]
fn a_different_range_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let asked = KeyRange::new(
        KeyBound::included(b"key-00000100"),
        KeyBound::included(b"key-00000149"),
    )
    .expect("the bounds are ordered");
    let other = KeyRange::new(
        KeyBound::included(b"key-00000100"),
        KeyBound::included(b"key-00000150"),
    )
    .expect("the bounds are ordered");
    let proof = built.prove_range(asked).expect("the tree can answer");

    assert!(matches!(
        proof.verify(&built.root(), other),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_dropped_record_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let range = KeyRange::new(
        KeyBound::included(b"key-00000100"),
        KeyBound::included(b"key-00000149"),
    )
    .expect("the bounds are ordered");
    let honest = built.prove_range(range).expect("the tree can answer");
    let mut records = honest.records().to_vec();
    let _dropped = records.remove(10);

    let thinned = RangeProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.range().clone(),
        records,
        honest.nodes().to_vec(),
    );

    assert!(matches!(
        thinned.verify(&built.root(), range),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn an_invented_record_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree(&corpus);
    let range = KeyRange::new(
        KeyBound::included(b"key-00000100"),
        KeyBound::included(b"key-00000149"),
    )
    .expect("the bounds are ordered");
    let honest = built.prove_range(range).expect("the tree can answer");
    let mut records = honest.records().to_vec();
    records.push(Record::new(b"key-00000149z", b"invented"));

    let padded = RangeProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.range().clone(),
        records,
        honest.nodes().to_vec(),
    );

    assert!(matches!(
        padded.verify(&built.root(), range),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_short_leaf_run_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(8_u32).expect("the cap is not zero")),
    );
    let range = KeyRange::new(
        KeyBound::included(b"key-00000010"),
        KeyBound::included(b"key-00000099"),
    )
    .expect("the bounds are ordered");
    let honest = built.prove_range(range).expect("the tree can answer");
    assert!(honest.nodes().len() > 3);

    let mut nodes = honest.nodes().to_vec();
    let _dropped = nodes.pop();
    let truncated = RangeProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.range().clone(),
        honest.records().to_vec(),
        nodes,
    );

    assert!(matches!(
        truncated.verify(&built.root(), range),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

#[test]
fn a_reordered_leaf_run_is_refused()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(8_u32).expect("the cap is not zero")),
    );
    let range = KeyRange::new(
        KeyBound::included(b"key-00000010"),
        KeyBound::included(b"key-00000099"),
    )
    .expect("the bounds are ordered");
    let honest = built.prove_range(range).expect("the tree can answer");

    let mut nodes = honest.nodes().to_vec();
    nodes.swap(1, 2);
    let shuffled = RangeProof::new(
        honest.envelope(),
        honest.root_node_hash(),
        honest.range().clone(),
        honest.records().to_vec(),
        nodes,
    );

    assert!(matches!(
        shuffled.verify(&built.root(), range),
        Err(RecordTreeError::InvalidProofShape { .. })
    ));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn generated_ranges_prove_and_verify(
        low in 0_usize .. 300_usize,
        span in 0_usize .. 60_usize,
        inclusive in proptest::bool::ANY,
    ) {
        let corpus = Corpus::of_size(CorpusSize::from(300));
        let built = tree(&corpus);
        let high = low.saturating_add(span).min(320);
        let low_key = format!("key-{low:08}").into_bytes();
        let high_key = format!("key-{high:08}").into_bytes();
        let end = if inclusive {
            KeyBound::included(high_key.as_slice())
        } else {
            KeyBound::excluded(high_key.as_slice())
        };
        let range = KeyRange::new(KeyBound::included(low_key.as_slice()), end)
            .expect("the bounds are ordered");

        let proof = built.prove_range(range).expect("the tree can answer");
        let verified = proof
            .verify(&built.root(), range)
            .expect("the proof is honest");

        let width = high.checked_sub(low)
            .and_then(|difference| difference.checked_add(usize::from(inclusive)))
            .expect("the generated interval length fits the host width");
        assert!(verified.iter().eq(corpus.entries().iter().skip(low).take(width)));
    }
}
