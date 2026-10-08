//! Sharing: what the content-defined boundary buys, measured rather than
//! asserted.
//!
//! The claim the tree shape exists for is that an edit perturbs the leaf it
//! falls in and leaves its neighbours identical. A fixed-position cut would not
//! do that under an insertion, because every later leaf would be renumbered.
//! These are differentials against the leaf identities themselves, which is the
//! only observation that can tell the two apart.

use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordValue;

use crate::common::Corpus;
use crate::common::CorpusSize;
use crate::common::tree;

/// Counts the leaf identities of `after` that do not occur in `before`.
///
/// # Specification
/// - requires: nothing; the two trees need not share parameters or records.
/// - ensures: how many of `after`'s leaf identities do not occur among
///   `before`'s, counting a repeated identity once per occurrence in `after`.
/// - provides: the differential the sharing claim is measured by, since a leaf
///   that survives an edit keeps its identity exactly.
/// - panics: none.
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

impl core::fmt::Display for FreshLeafCount
{
    /// Writes the count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried count through the `usize` rendering, so
    ///   the width and fill options the caller set apply to it.
    /// - provides: the count an assertion message names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.fmt(f)
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
         the one that absorbs its boundary, disturbed {fresh}"
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
         neighbourhood of {total} leaves, disturbed {fresh}"
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
