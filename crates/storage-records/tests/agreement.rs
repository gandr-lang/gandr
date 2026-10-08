//! Agreement: the digest is the fast path for disagreement and never the
//! decision, so the answer must equal the direct record comparison.

use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::RecordAgreement;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordValue;

use crate::common::Corpus;
use crate::common::CorpusSize;
use crate::common::capped_params;
use crate::common::tree;
use crate::common::tree_with;

#[test]
fn equal_trees_agree()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let left = tree(&corpus);
    let right = tree(&corpus);

    assert_eq!(left.root(), right.root());
    assert_eq!(left.agrees_with(&right), RecordAgreement::Agree);
}

#[test]
fn trees_differing_in_one_value_disagree()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let edited = corpus.with_value_at(
        RecordIndex::from(100),
        RecordValue::from(b"a different value"),
    );
    let left = tree(&corpus);
    let right = tree(&edited);

    assert_ne!(left.root(), right.root());
    assert_eq!(left.agrees_with(&right), RecordAgreement::Disagree);
}

#[test]
fn trees_differing_in_one_record_disagree()
{
    let corpus = Corpus::of_size(CorpusSize::from(200));
    let shorter = corpus.without(RecordIndex::from(100));
    let left = tree(&corpus);
    let right = tree(&shorter);

    assert_eq!(left.agrees_with(&right), RecordAgreement::Disagree);
}

#[test]
fn the_answer_is_the_direct_comparison()
{
    let corpus = Corpus::of_size(CorpusSize::from(120));
    let candidates = [
        tree(&corpus),
        tree(&corpus.with_value_at(RecordIndex::from(0), RecordValue::from(b"x"))),
        tree(&corpus.with_value_at(RecordIndex::from(119), RecordValue::from(b"x"))),
        tree(&corpus.without(RecordIndex::from(60))),
        tree(&Corpus::of_size(CorpusSize::from(0))),
        tree(&Corpus::of_size(CorpusSize::from(1))),
    ];

    for left in &candidates {
        for right in &candidates {
            // The direct comparison, with no digest in it at all: this is the
            // oracle the fast path must not change.
            let direct = if left.records() == right.records() {
                RecordAgreement::Agree
            }
            else {
                RecordAgreement::Disagree
            };

            assert_eq!(left.agrees_with(right), direct);
        }
    }
}

#[test]
fn trees_under_different_parameters_are_settled_by_the_records()
{
    let corpus = Corpus::of_size(CorpusSize::from(600));
    let left = tree(&corpus);
    let right = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(8_u32).expect("the cap is not zero")),
    );

    assert_eq!(left.agrees_with(&right), RecordAgreement::Agree);

    let edited = corpus.with_value_at(
        RecordIndex::from(300),
        RecordValue::from(b"a different value"),
    );
    let shifted = tree_with(
        &edited,
        capped_params(BoundaryRecordCap::try_from(8_u32).expect("the cap is not zero")),
    );
    assert_eq!(right.agrees_with(&shifted), RecordAgreement::Disagree);
}
