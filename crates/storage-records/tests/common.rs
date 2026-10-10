//! Corpora and constructors the area suites share.

use anodized::spec;
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

/// A seed byte for a reproducible synthetic node identity.
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
    /// The records in input order, including deliberately malformed fixtures.
    entries: Vec<Record>,
}

impl Corpus
{
    /// Builds a corpus with decimal position keys padded to at least eight
    /// digits.
    ///
    /// # Specification
    /// - requires: nothing; a size of zero yields no record.
    /// - ensures: exactly `count` records with `key-` and `value-` prefixes
    ///   followed by the same decimal position, padded to at least eight
    ///   digits. Keys are strictly increasing while all positions fit eight
    ///   digits.
    /// - provides: ordered fixed-width fixtures at the sizes these suites use.
    /// - panics: if the requested vector capacity is not representable;
    ///   allocation exhaustion follows the allocator's behavior.
    ///
    /// # Adequacy
    /// - hypothesis: L3 empty and 9-/20-record layouts, fixed membership
    ///   queries in 200 records, and the 4095/4096-record proof boundary
    ///   observe cardinality and position-derived keys and values. The
    ///   predicate parses positions without repeating formatting; allocation
    ///   failure is outside these runs.
    /// - witness: `tests::agreement::the_answer_is_the_direct_comparison`
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    /// - witness: `tests::membership::a_valid_proof_verifies`
    /// - witness: `tests::range::the_node_budget_ceiling_proves`
    /// - witness: `tests::range::a_span_past_the_node_budget_is_refused`
    #[spec(ensures: |ret| ret.entries.len() == count.0
        && ret.entries.iter().enumerate().all(|(index, record)| {
            record.key().as_ref().strip_prefix(b"key-").is_some_and(|digits| {
                digits.len() >= 8_usize
                    && (digits.len() == 8_usize || digits.first() != Some(&b'0'))
                    && digits.iter().all(u8::is_ascii_digit)
                    && core::str::from_utf8(digits).is_ok_and(|text| text.parse::<usize>() == Ok(index))
                    && record.value().as_ref().strip_prefix(b"value-") == Some(digits)
            })
        }))]
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

    /// Builds a corpus from explicit records without repairing their order.
    ///
    /// # Specification
    /// - requires: nothing; decreasing or duplicate keys are retained so the
    ///   refusal suites can offer those malformed inputs to the builder.
    /// - ensures: the corpus holds exactly those records, in the order given
    ///   and unsorted.
    /// - provides: the hand-written corpus a suite uses when the record
    ///   sequence itself is the fixture.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 ordered-map reconstruction of 300 records agrees with
    ///   the original tree. L3 two-record decreasing and duplicate fixtures
    ///   still produce their exact refusal variants, detecting sorting or
    ///   deduplication. The capture checks cardinality without cloning the
    ///   moved records.
    /// - witness: `tests::build::the_root_is_a_function_of_the_records`
    /// - witness: `tests::build::unsorted_input_is_refused`
    /// - witness: `tests::build::duplicate_keys_are_refused`
    #[spec(captures: count = records.len(), ensures: |ret| ret.entries.len() == count)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 single-leaf and five-leaf fixtures compare complete
    ///   decoded records with their source corpus, while malformed two-record
    ///   inputs preserve the offending positions. The predicate compares every
    ///   borrowed key and value in sequence rather than just the vector length.
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    /// - witness: `tests::build::unsorted_input_is_refused`
    /// - witness: `tests::build::duplicate_keys_are_refused`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.entries.iter().map(Record::as_record_ref)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 absence queries derived from the fixed 300-record
    ///   corpus compare complete neighbours with an independent full-corpus
    ///   scan. The predicate additionally checks the query-source sequence
    ///   positionally, detecting a lost, repeated or permuted key.
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.entries.iter().map(Record::key)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 the 200-record replacement fixture observes the new
    ///   value at position 100 and all unaffected records, and agreement
    ///   refuses the changed tree. The fixed 120-record comparison matrix also
    ///   exercises replacement at its first and last positions.
    /// - witness: `tests::agreement::trees_differing_in_one_value_disagree`
    /// - witness: `tests::agreement::the_answer_is_the_direct_comparison`
    #[spec(
        requires: usize::from(position) < self.entries.len(),
        ensures: |ret| ret.entries.len() == self.entries.len()
            && ret.entries.iter().zip(self.entries.iter()).enumerate().all(|(index, (actual, original))| {
                actual.key() == original.key() && actual.value() == if index == usize::from(position) {
                    value
                } else {
                    original.value()
                }
            }),
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 removing position 100 from 200 records agrees with the
    ///   original prefix followed by its suffix, and the resulting tree
    ///   disagrees with the original. L3 the 600-record case observes the
    ///   changed leaf set. These witnesses do not claim to exercise an invalid
    ///   position.
    /// - witness: `tests::agreement::trees_differing_in_one_record_disagree`
    /// - witness: `tests::sharing::removing_one_record_rebuilds_a_bounded_neighbourhood`
    #[spec(
        requires: usize::from(position) < self.entries.len(),
        ensures: |ret| ret.entries.iter().eq(self.entries.iter().enumerate()
            .filter(|&(index, _record)| index != usize::from(position))
            .map(|(_index, record)| record)),
    )]
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

/// Parameters with the widest digest mask and the supplied record cap.
///
/// # Specification
/// - requires: nothing beyond the validated cap type.
/// - ensures: the current selectors and boundary profile, with the widest
///   admissible digest mask and exactly `cap` as the record cap.
/// - provides: cap-driven layouts for the fixed corpora below; the widest mask
///   does not disable digest-driven cuts for arbitrary records.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 nine records at cap 64 form one leaf, twenty at cap 4 form
///   five leaves, and caps of one reach the proof-node budget boundary. These
///   finite layouts distinguish ignoring the supplied cap; they do not prove
///   that the digest rule never cuts for another corpus.
/// - witness: `tests::build::a_small_tree_is_a_single_leaf`
/// - witness: `tests::build::a_large_tree_has_an_internal_root`
/// - witness: `tests::range::the_node_budget_ceiling_proves`
/// - witness: `tests::range::a_span_past_the_node_budget_is_refused`
#[spec(ensures: |ret| {
    let current = TreeParams::current();
    ret.kind() == current.kind() && ret.encoding_version() == current.encoding_version()
        && ret.hash_algorithm() == current.hash_algorithm()
        && ret.separator_convention() == current.separator_convention()
        && ret.boundary() == BoundaryParams::new(BoundaryProfile::CURRENT, BoundaryMaskBits::MAX, cap)
})]
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
/// - requires: the corpus is in strictly increasing key order.
/// - ensures: the tree the build produces over the corpus's records under the
///   current parameters.
/// - provides: the one-line tree a suite reads without restating the build
///   call.
/// - panics: when the build refuses, which the expectation names; an unordered
///   corpus is offered to the build directly by the suites that are about
///   refusal.
///
/// # Adequacy
/// - hypothesis: L3 fixed membership values and full unbounded-range answers
///   observe the records produced from the source corpus. The predicate binds
///   the returned tree to those records and the current parameter set, catching
///   omitted records or a different build profile.
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::range::the_unbounded_range_proves`
#[spec(
    requires: corpus.entries.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key()),
    ensures: |ret| ret.records() == corpus.entries() && ret.root().params() == TreeParams::current(),
)]
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
///
/// # Adequacy
/// - hypothesis: L3 nine records at cap 64 and twenty at cap 4 compare complete
///   source records and the resulting leaf layouts. These observations
///   distinguish ignoring the requested profile or dropping input records.
/// - witness: `tests::build::a_small_tree_is_a_single_leaf`
/// - witness: `tests::build::a_large_tree_has_an_internal_root`
#[spec(
    requires: corpus.entries.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key())
        && params.ensure_supported().is_ok(),
    ensures: |ret| ret.records() == corpus.entries() && ret.root().params() == params,
)]
pub fn tree_with(
    corpus: &Corpus,
    params: TreeParams,
) -> RecordTree
{
    let records = corpus.records();

    RecordTree::build(records.as_slice(), params).expect("the corpus is ordered")
}

/// Returns a reproducible synthetic identity for a foreign-node fixture.
///
/// # Specification
/// - requires: nothing; every seed is admissible.
/// - ensures: an identity whose first byte is the seed, whose last byte is set,
///   and whose remaining bytes are zero, so distinct seeds give distinct
///   identities.
/// - provides: a candidate identity whose difference from a fixture's committed
///   node is observed by that fixture, not assumed cryptographically.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 the foreign-root fixture uses seed `0x5a` and compares the
///   exact mismatch against a manifest sealed with an independent fixed-byte
///   identity. Changing the seed, zero padding or final marker changes the
///   observed error payload.
/// - witness: `tests::store::a_root_bound_elsewhere_does_not_open`
#[spec(ensures: |ret| ret.as_ref().first() == Some(&seed.0)
    && ret.as_ref().last() == Some(&0xff_u8)
    && ret.as_ref().iter().skip(1_usize).take(30_usize).all(|byte| *byte == 0_u8))]
pub fn foreign_hash(seed: HashSeed) -> NodeHash
{
    let mut bytes = [0_u8; 32];
    bytes[0] = seed.0;
    bytes[31] = 0xff;

    NodeHash::from(bytes)
}
