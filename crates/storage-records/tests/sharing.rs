//! Leaf-content identity reuse across bounded record edits.
//!
//! The fixtures compare changed leaf identities for edits to 600 records and
//! disjoint corpora of 200 records. They observe content identity, not memory
//! aliasing, allocation counts or a universal bound on edit locality.

use anodized::spec;
use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordValue;

use crate::common::Corpus;
use crate::common::CorpusSize;
use crate::common::capped_params;
use crate::common::tree;
use crate::common::tree_with;

/// Counts the leaf identities of `after` that do not occur in `before`.
///
/// # Specification
/// - requires: nothing; the two trees need not share parameters or records.
/// - ensures: how many of `after`'s leaf identities do not occur among
///   `before`'s, counting a repeated identity once per occurrence in `after`.
/// - provides: the differential the sharing claim is measured by, since a leaf
///   that survives an edit keeps its identity exactly.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact fresh-leaf counts and bounded edit counts over
///   600-record edits, disjoint 200-record corpora, and empty/single-record
///   roots distinguish lost or inverted identity membership, omitted root
///   leaves, and confusion between node content and manifest identity. These
///   fixtures do not establish locality for arbitrary edits or hashes.
/// - witness: `tests::sharing::changing_one_value_rebuilds_one_leaf`
/// - witness: `tests::sharing::removing_one_record_rebuilds_a_bounded_neighbourhood`
/// - witness: `tests::sharing::inserting_at_the_front_leaves_later_leaves_alone`
/// - witness: `tests::sharing::appending_at_the_end_leaves_earlier_leaves_alone`
/// - witness: `tests::sharing::an_unrelated_corpus_shares_nothing`
/// - witness: `tests::sharing::root_leaves_share_by_content_not_manifest`
#[spec(ensures: |ret| {
    let old = before.leaf_hashes();
    ret.0 == after.leaf_hashes().iter().filter(|hash| !old.contains(hash)).count()
})]
fn fresh_leaves(
    before: &RecordTree,
    after: &RecordTree,
) -> FreshLeafCount
{
    let old: Vec<NodeHash> = before.leaf_hashes().into_vec();

    after
        .leaf_hashes()
        .iter()
        .filter(|hash| !old.contains(hash))
        .count()
        .into()
}

/// The number of leaf identities one tree shows that another lacks.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FreshLeafCount(usize);

impl From<usize> for FreshLeafCount
{
    /// Reads a `usize` as a fresh-leaf count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

#[test]
fn changing_one_value_rebuilds_one_leaf()
{
    let corpus = Corpus::of_size(CorpusSize::from(600));
    let before = tree(&corpus);
    let after = tree(&corpus.with_value_at(
        RecordIndex::from(300),
        RecordValue::from(b"a different value"),
    ));

    assert_eq!(fresh_leaves(&before, &after), FreshLeafCount(1));
}

#[test]
fn removing_one_record_rebuilds_a_bounded_neighbourhood()
{
    let corpus = Corpus::of_size(CorpusSize::from(600));
    let before = tree(&corpus);
    let after = tree(&corpus.without(RecordIndex::from(300)));

    let fresh = fresh_leaves(&before, &after);
    assert!(
        fresh <= FreshLeafCount(2),
        "removing one record should disturb at most the leaf it falls in and \
         the one that absorbs its boundary, disturbed {fresh:?}"
    );
}

#[test]
fn inserting_at_the_front_leaves_later_leaves_alone()
{
    let corpus = Corpus::of_size(CorpusSize::from(600));
    let inserted = {
        let mut entries = corpus.entries().to_vec();
        entries.insert(0, Record::new(b"aaa", b"first"));
        Corpus::of_pairs(entries)
    };
    let before = tree(&corpus);
    let after = tree(&inserted);

    // A fixed-position cut would renumber every leaf and rebuild all of them;
    // the content-defined cut rebuilds a bounded prefix.
    let fresh = fresh_leaves(&before, &after);
    let total = after.leaf_hashes().len();
    assert!(
        fresh <= FreshLeafCount(2),
        "inserting one record at the front should disturb a bounded \
         neighbourhood of {total} leaves, disturbed {fresh:?}"
    );
}

#[test]
fn appending_at_the_end_leaves_earlier_leaves_alone()
{
    let corpus = Corpus::of_size(CorpusSize::from(600));
    let appended = {
        let mut entries = corpus.entries().to_vec();
        entries.push(Record::new(b"zzz", b"last"));
        Corpus::of_pairs(entries)
    };
    let before = tree(&corpus);
    let after = tree(&appended);

    assert!(fresh_leaves(&before, &after) <= FreshLeafCount(2));
}

#[test]
fn an_unrelated_corpus_shares_nothing()
{
    let left = tree(&Corpus::of_size(CorpusSize::from(200)));
    let right = {
        let entries: Vec<Record> = (0_usize .. 200_usize)
            .map(|index| {
                Record::new(
                    format!("other-{index:08}").into_bytes(),
                    format!("other-{index:08}").into_bytes(),
                )
            })
            .collect();
        tree(&Corpus::of_pairs(entries))
    };

    assert_eq!(
        fresh_leaves(&left, &right),
        FreshLeafCount(right.leaf_hashes().len()),
        "no leaf of one corpus should occur in an unrelated one"
    );
}

#[test]
fn root_leaves_share_by_content_not_manifest()
{
    let empty = tree(&Corpus::of_size(CorpusSize::from(0)));
    let corpus = Corpus::of_size(CorpusSize::from(1));
    let single = tree(&corpus);
    let same_content = tree_with(
        &corpus,
        capped_params(BoundaryRecordCap::try_from(64_u32).expect("the cap is positive")),
    );
    let changed = tree(&corpus.with_value_at(RecordIndex::from(0), RecordValue::from(b"changed")));

    assert_eq!(fresh_leaves(&empty, &single), FreshLeafCount(1));
    assert_eq!(fresh_leaves(&single, &empty), FreshLeafCount(1));
    assert_ne!(single.root(), same_content.root());
    assert_eq!(fresh_leaves(&single, &same_content), FreshLeafCount(0));
    assert_eq!(fresh_leaves(&single, &changed), FreshLeafCount(1));
}
