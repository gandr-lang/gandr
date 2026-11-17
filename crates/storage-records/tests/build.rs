//! Building: what a root is a function of, what the two shapes are, and what a
//! malformed input is refused with.

use gandr_storage_records::BoundaryRecordCap;
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
    assert_eq!(
        built.leaf_hashes().as_ref(),
        [built.root_node_hash()].as_slice()
    );
    let nodes = built.nodes();
    let root = nodes.first().expect("the root is carried");
    assert_eq!(root.identity(), built.root_node_hash());
    let decoded = gandr_storage_records::decode_node(
        root.bytes(),
        &mut gandr_storage_records::DecodeWork::new(),
    )
    .expect("the root is canonical");
    assert_eq!(
        decoded.as_leaf().expect("empty leaf shape").records(),
        [].as_slice()
    );
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
    assert_eq!(built.records(), corpus.entries());
    assert_eq!(
        built.leaf_hashes().as_ref(),
        [built.root_node_hash()].as_slice()
    );
    let nodes = built.nodes();
    let root = nodes.first().expect("the root is carried");
    assert_eq!(root.identity(), built.root_node_hash());
    let decoded = gandr_storage_records::decode_node(
        root.bytes(),
        &mut gandr_storage_records::DecodeWork::new(),
    )
    .expect("the root is canonical");
    assert_eq!(
        decoded.as_leaf().expect("single leaf shape").records(),
        corpus.entries()
    );
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
    assert_eq!(built.records(), corpus.entries());
    let nodes = built.nodes();
    let root = nodes.first().expect("the root is first");
    assert_eq!(root.identity(), built.root_node_hash());
    assert!(
        nodes
            .iter()
            .skip(1_usize)
            .map(gandr_storage_records::ProofNode::identity)
            .eq(built.leaf_hashes().iter().copied())
    );
    let decoded = gandr_storage_records::decode_node(
        root.bytes(),
        &mut gandr_storage_records::DecodeWork::new(),
    )
    .expect("the root is canonical");
    let gandr_storage_records::DecodedNode::Internal(internal) = decoded
    else {
        panic!("five leaves need an internal root");
    };
    assert!(
        internal
            .children()
            .iter()
            .map(gandr_storage_records::ChildRef::identity)
            .eq(built.leaf_hashes().iter().copied())
    );
    for (leaf, expected) in nodes
        .iter()
        .skip(1_usize)
        .zip(corpus.entries().chunks(4_usize))
    {
        let decoded = gandr_storage_records::decode_node(
            leaf.bytes(),
            &mut gandr_storage_records::DecodeWork::new(),
        )
        .expect("the child is canonical");
        assert_eq!(
            decoded.as_leaf().expect("child leaf shape").records(),
            expected
        );
    }
}

#[test]
fn unsorted_input_is_refused()
{
    let corpus = Corpus::of_pairs(vec![Record::new(b"b", b"2"), Record::new(b"a", b"1")]);
    let records = corpus.records();

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
    let corpus = Corpus::of_pairs(vec![Record::new(b"a", b"1"), Record::new(b"a", b"2")]);
    let records = corpus.records();

    assert_eq!(
        RecordTree::build(records.as_slice(), TreeParams::current()),
        Err(RecordTreeError::DuplicateKeys {
            first: RecordIndex::from(0),
            second: RecordIndex::from(1),
        })
    );
}

#[test]
fn unsupported_parameters_are_refused()
{
    let current = TreeParams::current();
    let params = TreeParams::new(
        current.kind(),
        gandr_storage_records::EncodingVersion::V1,
        current.hash_algorithm(),
        current.separator_convention(),
        current.boundary(),
    );
    assert_eq!(
        RecordTree::build(&[RecordRef::new(b"a", b"1")], params),
        Err(RecordTreeError::UnsupportedVersion {
            version: gandr_storage_records::WireVersion::from(1_u16)
        })
    );
}

#[test]
fn lookup_and_range_answer_from_the_built_tree()
{
    let corpus = Corpus::of_size(CorpusSize::from(50));
    let built = tree(&corpus);

    for record in corpus.entries() {
        assert_eq!(built.lookup(record.key()), Some(record.value()));
    }

    assert_eq!(built.lookup(RecordKey::from(b"key-99999999")), None);
    assert_eq!(built.lookup(RecordKey::from(b"aaa")), None);
    assert_eq!(built.lookup(RecordKey::from(b"key-00000023x")), None);
    assert_eq!(
        built.range(gandr_storage_records::KeyRange::all()).as_ref(),
        corpus.entries()
    );
    let bounded = gandr_storage_records::KeyRange::new(
        gandr_storage_records::KeyBound::included(b"key-00000010"),
        gandr_storage_records::KeyBound::excluded(b"key-00000020"),
    )
    .expect("the bounds are ordered");
    assert_eq!(
        built.range(bounded).as_ref(),
        &corpus.entries()[10_usize .. 20_usize]
    );
    let empty = gandr_storage_records::KeyRange::new(
        gandr_storage_records::KeyBound::included(b"key-00000010"),
        gandr_storage_records::KeyBound::excluded(b"key-00000010"),
    )
    .expect("equal bounds are admitted");
    assert_eq!(built.range(empty).as_ref(), [].as_slice());
    let outside = gandr_storage_records::KeyRange::new(
        gandr_storage_records::KeyBound::included(b"zzz"),
        gandr_storage_records::KeyBound::Unbounded,
    )
    .expect("an unbounded end is ordered");
    assert_eq!(built.range(outside).as_ref(), [].as_slice());
}
