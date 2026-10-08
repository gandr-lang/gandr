//! Building: what a root is a function of, what the two shapes are, and what a
//! malformed input is refused with.

use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::OwnedRecordKey;
use gandr_storage_records::OwnedRecordValue;
use gandr_storage_records::Record;
use gandr_storage_records::RecordCount;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::TreeParams;

use crate::common::Corpus;
use crate::common::CorpusSize;
use crate::common::capped_params;
use crate::common::tree;
use crate::common::tree_with;

/// The crate `README.md`'s worked example, kept runnable so the document
/// cannot drift from the API it shows.
#[test]
fn the_readme_example_runs()
{
    fn example() -> Result<(), RecordTreeError>
    {
        let records = [
            RecordRef::new(b"alpha", b"1"),
            RecordRef::new(b"beta", b"2"),
            RecordRef::new(b"gamma", b"3"),
        ];
        let tree = RecordTree::build(records.as_slice(), TreeParams::current())?;

        let mut store = InMemoryBlockStore::new();
        tree.write_to(&mut store)?;

        let key = RecordKey::from(b"beta");
        let proof = tree.prove_membership(key)?;
        proof.verify(
            &tree.root(),
            key,
            gandr_storage_records::RecordValue::from(b"2"),
        )?;

        Ok(())
    }

    assert_eq!(example(), Ok(()));
}

#[test]
fn the_root_is_a_function_of_the_records()
{
    let corpus = Corpus::of_size(CorpusSize::from(300));
    let direct = tree(&corpus);

    // The same record set assembled through an ordered map rather than by
    // construction order: the root must not distinguish the two.
    let mut ordered = alloc::collections::BTreeMap::<OwnedRecordKey, OwnedRecordValue>::new();
    for record in corpus.entries().iter().rev() {
        let _replaced = ordered.insert(record.key().into(), record.value().into());
    }
    let reassembled = Corpus::of_pairs(
        ordered
            .into_iter()
            .map(|(key, value)| Record::new(key, value))
            .collect(),
    );
    let indirect = tree(&reassembled);

    assert_eq!(direct.root(), indirect.root());
    assert_eq!(direct.leaf_hashes(), indirect.leaf_hashes());
}

#[test]
fn an_empty_tree_is_one_empty_leaf()
{
    let built = RecordTree::build(&[], TreeParams::current()).expect("nothing is ordered");

    assert_eq!(built.root().record_count(), RecordCount::ZERO);
    assert_eq!(built.records(), [].as_slice());
    assert_eq!(built.nodes().len(), 1);
    assert_eq!(built.leaf_hashes().len(), 1);
    assert_eq!(built.lookup(RecordKey::from(b"anything")), None);
}

#[test]
fn a_small_tree_is_a_single_leaf()
{
    let corpus = Corpus::of_size(CorpusSize::from(9));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is not zero")),
    );

    assert_eq!(built.nodes().len(), 1);
    assert_eq!(built.leaf_hashes().len(), 1);
    assert_eq!(built.root().record_count(), RecordCount::from(9));
}

#[test]
fn a_large_tree_has_an_internal_root()
{
    let corpus = Corpus::of_size(CorpusSize::from(20));
    let built = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(4_u32).expect("the cap is not zero")),
    );

    assert_eq!(built.leaf_hashes().len(), 5);
    assert_eq!(built.nodes().len(), 6);
    assert_eq!(built.root().record_count(), RecordCount::from(20));
}

#[test]
fn the_default_rule_cuts_a_corpus_into_many_leaves()
{
    let corpus = Corpus::of_size(CorpusSize::from(1000));
    let built = tree(&corpus);

    assert!(
        built.leaf_hashes().len() > 20,
        "the default mask should cut a thousand records into many leaves"
    );
}

#[test]
fn unsorted_input_is_refused()
{
    let records = [RecordRef::new(b"b", b"2"), RecordRef::new(b"a", b"1")];

    assert_eq!(
        RecordTree::build(records.as_slice(), TreeParams::current()),
        Err(RecordTreeError::UnsortedInput {
            previous: RecordIndex::from(0),
            current: RecordIndex::from(1),
        })
    );
}

#[test]
fn duplicate_keys_are_refused()
{
    let records = [RecordRef::new(b"a", b"1"), RecordRef::new(b"a", b"2")];

    assert_eq!(
        RecordTree::build(records.as_slice(), TreeParams::current()),
        Err(RecordTreeError::DuplicateKeys {
            first: RecordIndex::from(0),
            second: RecordIndex::from(1),
        })
    );
}

#[test]
fn lookup_and_range_answer_from_the_built_tree()
{
    let corpus = Corpus::of_size(CorpusSize::from(50));
    let built = tree(&corpus);

    for record in corpus.entries() {
        assert_eq!(
            built
                .lookup(record.key())
                .map(|found| found.as_ref().to_vec()),
            Some(record.value().as_ref().to_vec())
        );
    }

    assert_eq!(built.lookup(RecordKey::from(b"key-99999999")), None);
    assert_eq!(
        built.range(gandr_storage_records::KeyRange::all()).len(),
        50
    );
}
