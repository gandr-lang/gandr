//! Corpora and constructors the area suites share.

use gandr_storage_records::BoundaryMaskBits;
use gandr_storage_records::BoundaryParams;
use gandr_storage_records::BoundaryProfile;
use gandr_storage_records::BoundaryRecordCap;
use gandr_storage_records::NodeHash;
use gandr_storage_records::OwnedRecordKey;
use gandr_storage_records::OwnedRecordValue;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordKey;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordValue;
use gandr_storage_records::TreeParams;

/// The number of records a generated corpus holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CorpusSize(usize);

impl From<usize> for CorpusSize
{
    /// Reads a `usize` as a corpus size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

/// A seed byte for a node identity no tree in these suites produces.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HashSeed(u8);

impl From<u8> for HashSeed
{
    /// Reads a byte as an identity seed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(seed: u8) -> Self
    {
        Self(seed)
    }
}

/// A record corpus held as owned records, so borrowed records can point into
/// it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Corpus
{
    /// The records, in key order.
    entries: Vec<Record>,
}

impl Corpus
{
    /// Builds a corpus of `count` records with ordered, fixed-width keys.
    ///
    /// # Specification
    /// - requires: nothing; a size of zero yields no record.
    /// - ensures: exactly `count` records whose keys are the zero-padded
    ///   decimal positions, so they are distinct, fixed-width, and already in
    ///   key order.
    /// - provides: the corpus every suite builds a tree from, ordered so no
    ///   test depends on the build's own sorting.
    /// - panics: none.
    pub fn of_size(count: CorpusSize) -> Self
    {
        let entries = (0_usize .. count.0)
            .map(|index| {
                Record::new(
                    format!("key-{index:08}").into_bytes(),
                    format!("value-{index:08}").into_bytes(),
                )
            })
            .collect();

        Self { entries }
    }

    /// Builds a corpus from explicit records, which must be ordered.
    ///
    /// # Specification
    /// - requires: `records` is strictly increasing in key order; an unordered
    ///   corpus is what the refusal suites offer to `RecordTree::build`
    ///   deliberately.
    /// - ensures: the corpus holds exactly those records, in the order given
    ///   and unsorted.
    /// - provides: the hand-written corpus a suite uses when the record
    ///   sequence itself is the fixture.
    /// - panics: none.
    pub fn of_pairs(records: Vec<Record>) -> Self
    {
        Self { entries: records }
    }

    /// Borrows the corpus as records.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly one borrowed reference per corpus entry, in the
    ///   corpus's own order, so nothing is dropped, added, or permuted.
    /// - provides: the reference sequence a build takes, matching the corpus
    ///   position for position.
    /// - fails: never.
    /// - panics: none.
    pub fn records(&self) -> Vec<RecordRef<'_>>
    {
        self.entries.iter().map(Record::as_record_ref).collect()
    }

    /// Returns the corpus's keys.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly one borrowed key per corpus entry, in the corpus's
    ///   own order, so nothing is dropped, added, or permuted.
    /// - provides: the query sequence a suite reads the corpus back by,
    ///   matching the corpus position for position.
    /// - fails: never.
    /// - panics: none.
    pub fn keys(&self) -> Vec<RecordKey<'_>>
    {
        self.entries.iter().map(|record| record.key()).collect()
    }

    /// Returns the corpus's records.
    ///
    /// # Specification
    /// trivial.
    pub fn entries(&self) -> &[Record]
    {
        self.entries.as_slice()
    }

    /// Returns the corpus with one record's value replaced.
    ///
    /// # Specification
    /// - requires: `position` is inside the corpus.
    /// - ensures: a corpus equal to this one except that the record at
    ///   `position` keeps its key and carries `value`, so the key order is
    ///   unchanged and only the value differs.
    /// - provides: the one-value perturbation the agreement and proof suites
    ///   compare against, which changes a digest without changing a key set.
    /// - panics: when `position` is outside the corpus, which the expectation
    ///   names, so a fixture that outgrew its corpus fails loudly.
    pub fn with_value_at(
        &self,
        position: RecordIndex,
        value: RecordValue<'_>,
    ) -> Self
    {
        let mut entries = self.entries.clone();
        let position = usize::from(position);
        let key = OwnedRecordKey::from(
            entries
                .get(position)
                .expect("the position is inside the corpus")
                .key(),
        );

        entries[position] = Record::new(key, OwnedRecordValue::from(value));

        Self { entries }
    }

    /// Returns the corpus with one record removed.
    ///
    /// # Specification
    /// - requires: `position` is inside the corpus.
    /// - ensures: a corpus equal to this one without the record at `position`,
    ///   the remaining records keeping their order.
    /// - provides: the one-record perturbation the absence and disagreement
    ///   suites compare against.
    /// - panics: when `position` is outside the corpus, which the expectation
    ///   names.
    pub fn without(
        &self,
        position: RecordIndex,
    ) -> Self
    {
        let mut entries = self.entries.clone();
        let position = usize::from(position);
        let _removed = entries
            .get(position)
            .cloned()
            .expect("the position is inside the corpus");

        entries.remove(position);

        Self { entries }
    }
}

/// Parameters whose digest rule never cuts, so the cap alone decides leaves and
/// a test can name the leaf count it wants.
///
/// # Specification
/// - requires: `cap` was minted through its own fallible conversion, which is
///   the only way to obtain one.
/// - ensures: the current parameters with the widest admissible mask and `cap`,
///   so the digest rule cuts no leaf and the cap alone decides where leaves
///   end.
/// - provides: the deterministic leaf count a layout test names, instead of the
///   digest-driven count the default rule gives.
/// - panics: none.
pub fn capped_params(cap: BoundaryRecordCap) -> TreeParams
{
    let current = TreeParams::current();

    TreeParams::new(
        current.kind(),
        current.encoding_version(),
        current.hash_algorithm(),
        current.separator_convention(),
        BoundaryParams::new(BoundaryProfile::CURRENT, BoundaryMaskBits::MAX, cap),
    )
}

/// Builds a tree from a corpus under the default parameters.
///
/// # Specification
/// - requires: `corpus` is in key order, which every constructor above that
///   generates one establishes.
/// - ensures: the tree the build produces over the corpus's records under the
///   current parameters.
/// - provides: the one-line tree a suite reads without restating the build
///   call.
/// - panics: when the build refuses, which the expectation names; an unordered
///   corpus is offered to the build directly by the suites that are about
///   refusal.
pub fn tree(corpus: &Corpus) -> RecordTree
{
    let records = corpus.records();

    RecordTree::build(records.as_slice(), TreeParams::current()).expect("the corpus is ordered")
}

/// Builds a tree from a corpus under explicit parameters.
///
/// # Specification
/// - requires: `corpus` is in key order, and `params` is a set this build
///   honours.
/// - ensures: the tree the build produces over the corpus's records under
///   `params`.
/// - provides: the tree a layout or parameter test builds under a rule other
///   than the default.
/// - panics: when the build refuses, which the expectation names.
pub fn tree_with(
    corpus: &Corpus,
    params: TreeParams,
) -> RecordTree
{
    let records = corpus.records();

    RecordTree::build(records.as_slice(), params).expect("the corpus is ordered")
}

/// Returns a node identity that no tree in these suites produces.
///
/// # Specification
/// - requires: nothing; every seed is admissible.
/// - ensures: an identity whose first byte is the seed, whose last byte is set,
///   and whose remaining bytes are zero, so distinct seeds give distinct
///   identities.
/// - provides: an identity no tree in these suites seals or encodes, which is
///   what the unknown-node and mismatch fixtures need.
/// - panics: none.
pub fn foreign_hash(seed: HashSeed) -> NodeHash
{
    let mut bytes = [0_u8; 32];
    bytes[0] = seed.0;
    bytes[31] = 0xff;

    NodeHash::from(bytes)
}
