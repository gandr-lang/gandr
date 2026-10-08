//! The store boundary: a written tree loads back, and a root opens only when
//! its own node is there.

use gandr_storage_records::BlockStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::RecordValue;
use gandr_storage_records::StoreOccupancy;
use gandr_storage_records::StoredNodeCount;
use gandr_storage_records::StoredRoot;
use gandr_storage_records::TreeParams;

use crate::common::Corpus;
use crate::common::CorpusSize;
use crate::common::HashSeed;
use crate::common::foreign_hash;
use crate::common::tree;

#[test]
fn every_node_of_a_tree_loads_back()
{
    let corpus = Corpus::of_size(CorpusSize::from(400));
    let built = tree(&corpus);
    let mut store = InMemoryBlockStore::new();

    assert_eq!(built.write_to(&mut store), Ok(()));

    let nodes = built.nodes();
    assert_eq!(store.len(), StoredNodeCount::from(nodes.len()));

    for node in nodes.as_ref() {
        let loaded = BlockStore::load(&store, node.identity()).expect("the node was written");

        assert_eq!(loaded.identity(), node.identity());
        assert_eq!(loaded.bytes().as_ref(), node.bytes().as_ref());
    }
}

#[test]
fn a_written_root_opens()
{
    let corpus = Corpus::of_size(CorpusSize::from(400));
    let built = tree(&corpus);
    let mut store = InMemoryBlockStore::new();
    built.write_to(&mut store).expect("the tree writes");

    let opened = StoredRoot::open(built.root(), built.root_node_hash(), &store)
        .expect("the root node was written");

    assert_eq!(opened.root(), built.root());
    assert_eq!(opened.root_node_hash(), built.root_node_hash());
    assert_eq!(opened.recheck(&store), Ok(()));
}

#[test]
fn an_unwritten_root_does_not_open()
{
    let corpus = Corpus::of_size(CorpusSize::from(400));
    let built = tree(&corpus);
    let store = InMemoryBlockStore::new();

    assert_eq!(store.is_empty(), StoreOccupancy::Empty);
    assert_eq!(
        StoredRoot::open(built.root(), built.root_node_hash(), &store),
        Err(RecordTreeError::UnknownNode {
            hash: built.root_node_hash(),
        })
    );
}

#[test]
fn a_root_bound_elsewhere_does_not_open()
{
    let corpus = Corpus::of_size(CorpusSize::from(400));
    let built = tree(&corpus);
    let mut store = InMemoryBlockStore::new();
    built.write_to(&mut store).expect("the tree writes");

    assert!(matches!(
        StoredRoot::open(built.root(), foreign_hash(HashSeed::from(0x5a_u8)), &store),
        Err(RecordTreeError::HashMismatch { .. })
    ));
}

#[test]
fn two_trees_sharing_leaves_share_stored_nodes()
{
    let corpus = Corpus::of_size(CorpusSize::from(400));
    let edited = corpus.with_value_at(
        RecordIndex::from(200),
        RecordValue::from(b"a different value"),
    );
    let first = tree(&corpus);
    let second = tree(&edited);

    let mut store = InMemoryBlockStore::new();
    first.write_to(&mut store).expect("the first tree writes");
    let after_first = usize::from(store.len());
    second.write_to(&mut store).expect("the second tree writes");
    let after_both = usize::from(store.len());

    let added = after_both.saturating_sub(after_first);
    assert!(
        added <= 0x03_usize,
        "an edit to one record should add at most its own leaf, a neighbouring leaf when the content-defined cut shifts, and the root; added {added}"
    );
}

#[test]
fn a_store_path_on_the_host_separator_round_trips()
{
    // Cross-OS lane witness: a record key is an opaque byte string, and
    // the host's own path separator is one byte among them. Two store
    // paths, one per separator byte — the host's and the foreign one —
    // are built, written to and read back from the store, and then
    // looked up and proved, and every byte of every key comes back.
    // Handling that treats a separator byte specially, or assumes a key
    // never carries the host separator, fails this on the lane where
    // the assumption breaks.
    let host_separator =
        u8::try_from(std::path::MAIN_SEPARATOR).expect("the host separator fits in a byte");
    let foreign_separator = if host_separator == b'/' { b'\\' } else { b'/' };
    let mut records = [
        Record::new(
            [b'a', host_separator, b'b', host_separator, b'c'].to_vec(),
            b"one",
        ),
        Record::new(
            [b'a', foreign_separator, b'b', foreign_separator, b'c'].to_vec(),
            b"two",
        ),
    ];
    records.sort();
    let borrowed = records
        .iter()
        .map(Record::as_record_ref)
        .collect::<Vec<_>>();
    let built = RecordTree::build(borrowed.as_slice(), TreeParams::current())
        .expect("the keys are ordered");

    // The store's write and load paths.
    let mut store = InMemoryBlockStore::new();
    built.write_to(&mut store).expect("the tree writes");
    let opened = StoredRoot::open(built.root(), built.root_node_hash(), &store)
        .expect("the root node was written");
    assert_eq!(opened.recheck(&store), Ok(()));

    // The round trip itself: every key and value comes back byte-for-byte.
    for (record, stored) in records.iter().zip(built.records().iter()) {
        assert_eq!(stored.key(), record.key());
        assert_eq!(stored.value(), record.value());
    }

    // The lookup and proof paths.
    for record in &records {
        let key = record.key();
        let value = record.value();
        assert_eq!(built.lookup(key), Some(value));
        let proof = built.prove_membership(key).expect("the key is present");
        assert_eq!(proof.verify(&built.root(), key, value), Ok(()));
    }
}
