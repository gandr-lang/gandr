//! The tree itself: how a sorted record sequence becomes nodes and a root, what
//! the tree answers, and what it can prove.
//!
//! # Tree shape
//!
//! A tree is one leaf or one internal root over a run of leaves. Every node
//! and proof enforces this two-level shape. See
//! [tree and proof shapes](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#tree-and-proof-shapes)
//! for the child ceiling and storage boundary.
//!
//! # Building
//!
//! Building sorts nothing: it requires a strictly increasing sequence and
//! refuses anything else, because the order is the tree's index and a builder
//! that quietly sorted would hide a caller's duplicate keys. It cuts the
//! sequence into leaves by the committed boundary rule, encodes each leaf,
//! builds the internal root over their separators when there is more than one,
//! and seals the root manifest over the parameters, the record count and the
//! root node's identity.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::boundary::RecordSpan;
use crate::boundary::leaf_spans;
use crate::bytes::NodeHash;
use crate::bytes::RecordKey;
use crate::bytes::RecordValue;
use crate::error::RecordTreeError;
use crate::node::ChildIndex;
use crate::node::ChildRef;
use crate::node::StoredNode;
use crate::node::encode_internal;
use crate::node::encode_leaf;
use crate::node::hash_node;
use crate::node::select_child;
use crate::params::TreeParams;
use crate::params::TreeRoot;
use crate::proof::MembershipProof;
use crate::proof::NonMembershipProof;
use crate::proof::ProofEnvelope;
use crate::proof::ProofKind;
use crate::proof::ProofNode;
use crate::proof::RangeProof;
use crate::proof::SuccessorLeaf;
use crate::proof::bracket;
use crate::proof::needs_successor;
use crate::proof::range_span;
use crate::record::KeyRange;
use crate::record::OwnedKeyRange;
use crate::record::Record;
use crate::record::RecordCount;
use crate::record::RecordRef;
use crate::record::ensure_strictly_sorted;
use crate::record::find_record;
use crate::record::select_in_range;
use crate::store::BlockStore;
use crate::wire::NodeCount;
use crate::wire::ensure_proof_budget;

/// One leaf of a built tree.
///
/// # Specification
/// - requires: construction from a built leaf and its input span.
/// - ensures: the identity authenticates the stored bytes; the span names the
///   corresponding input run, whose context is retained by the parent tree.
/// - provides: the cached leaf and source coordinates used for proof selection.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on a three-record, one-record-per-leaf tree replaces a
///   payload under its original identity and observes a false refinement; the
///   parent also refuses a substituted source span. These distinguish
///   unauthenticated cached bytes and lost coordinate correlation.
/// - witness: `tree::tests::built_state_refinements_reject_cache_corruption`
#[derive(Clone, Debug, Eq, PartialEq)]
#[spec(maintains: hash_node(self.node.bytes()) == self.node.identity())]
struct LeafEntry
{
    /// The leaf's identity and bytes.
    node: ProofNode,
    /// The run of record positions the leaf holds.
    span: RecordSpan,
}

/// A built ordered-record tree.
///
/// The tree holds its records, its encoded nodes and its root manifest, so
/// answering a query or building a proof needs no store and no decoding of the
/// tree's own bytes.
///
/// # Specification
/// - requires: nothing, once built.
/// - ensures: the root manifest binds the parameters, the record count and the
///   root node; every leaf's identity appears in the root's child references
///   when the root is internal; and the record sequence is strictly increasing.
/// - provides: lookup, range, proof construction and the store write.
/// - fails: only at construction and proof construction, as those state.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 on empty, nine-record and twenty-record capped trees
///   observes complete records, decoded shape and ordered node identities.
///   Reassembly of 300 records observes equal roots and leaves, distinguishing
///   input-order leakage and loss of the link between roots and leaves. L3
///   privately changes cached count, key order, child order, span or payload in
///   a three-record tree and observes false refinements. These observations
///   cover cached consistency, not every possible payload or hash collision.
/// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
/// - witness: `tests::build::a_small_tree_is_a_single_leaf`
/// - witness: `tests::build::a_large_tree_has_an_internal_root`
/// - witness: `tests::build::the_root_is_a_function_of_the_records`
/// - witness: `tree::tests::built_state_refinements_reject_cache_corruption`
#[derive(Clone, Debug, Eq, PartialEq)]
#[spec(maintains: {
    if RecordCount::of_slice(self.records.as_ref()) != Ok(self.root.record_count())
        || !self.records.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key())
        || self.children.len() != self.leaves.len()
        || self.root.ensure_binds(self.root_node.identity()).is_err()
        || hash_node(self.root_node.bytes()) != self.root_node.identity()
    {
        return false;
    }
    let mut next = 0_usize;
    for (child, leaf) in self.children.iter().zip(self.leaves.iter()) {
        let start = usize::from(leaf.span.start());
        let end = usize::from(leaf.span.end());
        if start != next || child.identity() != leaf.node.identity()
            || !anodized::types::Spec::predicate(leaf)
        {
            return false;
        }
        let Some(run) = self.records.get(start .. end) else {
            return false;
        };
        let Some(first) = run.first() else {
            return false;
        };
        if child.first_key() != first.key()
            || RecordCount::of_slice(run) != Ok(child.record_count())
        {
            return false;
        }
        next = end;
    }
    self.leaves.is_empty() || next == self.records.len()
})]
pub struct RecordTree
{
    /// The root manifest.
    root: TreeRoot,
    /// The root node's identity and bytes.
    root_node: ProofNode,
    /// The root's child references, empty when the root is a leaf.
    children: Box<[ChildRef]>,
    /// The leaves, empty when the root is a leaf.
    leaves: Box<[LeafEntry]>,
    /// The records, strictly increasing in key order.
    records: Box<[Record]>,
}

impl RecordTree
{
    /// Builds a tree from a strictly increasing record sequence.
    ///
    /// # Specification
    /// - requires: none; ordering and parameter support are checked.
    /// - ensures: success retains exactly the records and parameters, seals the
    ///   root over their count and the root node, and pairs every carried leaf
    ///   with its child identity. Equal inputs determine equal roots; an empty
    ///   sequence gives one empty leaf.
    /// - provides: the only constructor of a validated tree.
    /// - fails: [`RecordTreeError::UnsortedInput`] and
    ///   [`RecordTreeError::DuplicateKeys`] for an input that is not strictly
    ///   increasing; [`RecordTreeError::UnsupportedVersion`] and
    ///   [`RecordTreeError::IncompatibleParameters`] for parameters this build
    ///   does not implement; [`RecordTreeError::BudgetExceeded`] when the
    ///   sequence needs more leaves than one internal root can address or an
    ///   encoded node exceeds the node byte budget;
    ///   [`RecordTreeError::ArithmeticOverflow`] when a count or length exceeds
    ///   its width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::UnsortedInput`] — the input is not increasing.
    /// [`RecordTreeError::DuplicateKeys`] — the input repeats a key.
    /// [`RecordTreeError::UnsupportedVersion`] — unsupported encoding version.
    /// [`RecordTreeError::IncompatibleParameters`] — unsupported parameter.
    /// [`RecordTreeError::BudgetExceeded`] — the sequence needs more leaves
    /// than one internal root can address, or an encoded node exceeds the
    /// node byte budget.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count or length exceeds its
    /// width.
    /// [`RecordTreeError::InvalidProofShape`] — a leaf run was empty, which the
    /// boundary rule does not produce.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares direct and map-reassembled builds of 300
    ///   records. Empty, nine-record and twenty-record capped inputs observe
    ///   exact records, decoded shape and child/leaf correspondence. L3 checks
    ///   reversed keys, duplicates and the unsupported encoding version. These
    ///   cases distinguish lost payloads, shape confusion and omitted guards.
    /// - witness: `tests::build::the_root_is_a_function_of_the_records`
    /// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    /// - witness: `tests::build::unsorted_input_is_refused`
    /// - witness: `tests::build::duplicate_keys_are_refused`
    /// - witness: `tests::build::unsupported_parameters_are_refused`
    #[inline]
    #[spec(ensures: |ret| {
        match params.ensure_supported().and_then(|()| ensure_strictly_sorted(records.iter().map(RecordRef::key))) {
            | Err(error) => ret.as_ref().is_err_and(|actual| *actual == error),
            | Ok(()) => ret.as_ref().ok().is_none_or(|tree|
                tree.root.params() == params
                    && tree.records.iter().map(Record::as_record_ref).eq(records.iter().copied())
                    && anodized::types::Spec::predicate(tree)),
        }
    })]
    pub fn build(
        records: &[RecordRef<'_>],
        params: TreeParams,
    ) -> Result<Self, RecordTreeError>
    {
        params.ensure_supported()?;
        ensure_strictly_sorted(records.iter().map(RecordRef::key))?;

        let spans = leaf_spans(records, params.boundary())?;
        let mut leaves = Vec::<LeafEntry>::with_capacity(spans.len().max(1_usize));

        if spans.is_empty() {
            let bytes = encode_leaf(&[])?;
            leaves.push(LeafEntry {
                node: ProofNode::new(hash_node(bytes.as_borrowed()), bytes),
                span: RecordSpan::empty(),
            });
        }
        else {
            for span in spans.as_ref() {
                let run = records
                    .get(usize::from(span.start()) .. usize::from(span.end()))
                    .ok_or_else(|| RecordTreeError::InvalidProofShape {
                        context: "a leaf run is outside the record sequence".into(),
                    })?;
                let bytes = encode_leaf(run)?;
                leaves.push(LeafEntry {
                    node: ProofNode::new(hash_node(bytes.as_borrowed()), bytes),
                    span: *span,
                });
            }
        }

        let owned: Vec<Record> = records.iter().map(|record| Record::from(*record)).collect();
        let record_count = RecordCount::of_slice(records)?;

        let (root_node, children, leaves) =
            if leaves.len() == 1_usize {
                let only = leaves.into_iter().next().ok_or_else(|| {
                    RecordTreeError::InvalidProofShape {
                        context: "a one-leaf tree has no leaf".into(),
                    }
                })?;

                (only.node, Vec::<ChildRef>::new(), Vec::<LeafEntry>::new())
            }
            else {
                let mut children = Vec::<ChildRef>::with_capacity(leaves.len());

                for leaf in &leaves {
                    let run = owned
                        .get(usize::from(leaf.span.start()) .. usize::from(leaf.span.end()))
                        .ok_or_else(|| RecordTreeError::InvalidProofShape {
                            context: "a leaf run is outside the record sequence".into(),
                        })?;
                    let first = run
                        .first()
                        .ok_or_else(|| RecordTreeError::InvalidProofShape {
                            context: "a leaf run is empty".into(),
                        })?;
                    children.push(ChildRef::new(
                        first.key(),
                        leaf.node.identity(),
                        RecordCount::of_slice(run)?,
                    ));
                }

                let bytes = encode_internal(children.as_slice())?;
                let node = ProofNode::new(hash_node(bytes.as_borrowed()), bytes);

                (node, children, leaves)
            };

        let root = TreeRoot::seal(params, record_count, root_node.identity())?;

        Ok(Self {
            root,
            root_node,
            children: children.into_boxed_slice(),
            leaves: leaves.into_boxed_slice(),
            records: owned.into_boxed_slice(),
        })
    }

    /// Returns the root manifest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> TreeRoot
    {
        self.root
    }

    /// Returns the root node's identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root_node_hash(&self) -> NodeHash
    {
        self.root_node.identity()
    }

    /// Returns the tree's records in key order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the records in strictly increasing key order, which the build
    ///   refused to establish any other way.
    /// - provides: the sequence the root commits to, so a caller comparing two
    ///   trees reads the same order the digest was folded over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on empty, nine-record and twenty-record trees observes
    ///   the entire original sequence, distinguishing reordered, omitted or
    ///   substituted records.
    /// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.records.as_ref())))]
    pub fn records(&self) -> &[Record]
    {
        self.records.as_ref()
    }

    /// Returns the identities of the tree's leaves in key order.
    ///
    /// A tree whose root is a leaf reports that one leaf, which is its root
    /// node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one identity per leaf in key order, and the root node's own
    ///   identity for a tree whose root is its single leaf.
    /// - provides: the leaf identities a proof layout is checked against, with
    ///   the one-leaf tree answered as the paragraph above states rather than
    ///   as an empty list.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on empty, single-leaf and five-leaf trees compares
    ///   exact leaf identities with decoded root children and ordered node
    ///   enumeration. It distinguishes dropping the single root leaf, reversing
    ///   leaves and including an internal root among them.
    /// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| if self.leaves.is_empty() {
        ret.as_ref() == [self.root_node.identity()].as_slice()
    } else {
        ret.iter().copied().eq(self.leaves.iter().map(|leaf| leaf.node.identity()))
    })]
    pub fn leaf_hashes(&self) -> Box<[NodeHash]>
    {
        if self.leaves.is_empty() {
            return Box::from([self.root_node.identity()].as_slice());
        }

        let mut hashes = Vec::<NodeHash>::with_capacity(self.leaves.len());

        for leaf in self.leaves.as_ref() {
            hashes.push(leaf.node.identity());
        }

        hashes.into_boxed_slice()
    }

    /// Returns every node of the tree, the root first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the root node first, then each leaf in key order; every
    ///   node's identity appears in the root's child references, or is the
    ///   root's own for a single-leaf tree.
    /// - provides: owned copies of the complete ordered node set for storage
    ///   and proofs, including cloned encoded payloads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on empty, one-leaf and five-leaf trees observes the
    ///   root first, decoded records and child identities in order. It
    ///   distinguishes root omission and leaf permutation; these observations
    ///   do not measure allocation counts.
    /// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.iter().eq(core::iter::once(&self.root_node)
        .chain(self.leaves.iter().map(|leaf| &leaf.node))))]
    pub fn nodes(&self) -> Box<[ProofNode]>
    {
        let mut nodes = Vec::<ProofNode>::with_capacity(self.leaves.len().saturating_add(1_usize));
        nodes.push(self.root_node.clone());

        for leaf in self.leaves.as_ref() {
            nodes.push(leaf.node.clone());
        }

        nodes.into_boxed_slice()
    }

    /// Writes every node of the tree to a store.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.is_err() ||
    ///   (store.load(self.root_node.identity()).is_ok() &&
    ///   self.leaves.iter().all(|leaf| store.load(leaf.node.identity())
    ///   .is_ok()))` — on success every node of the tree is loadable from
    ///   `store` under its own identity.
    /// - provides: the tree's only interaction with a store.
    /// - fails: whatever the store's admission check refuses, which for a tree
    ///   this crate built is unreachable and is still not assumed away.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::HashMismatch`] — the store refused a node's identity.
    /// [`RecordTreeError::MalformedNode`] — the store refused a node's bytes.
    /// [`RecordTreeError::UnsupportedVersion`] — the store refused a node's
    /// encoding version.
    /// [`RecordTreeError::BudgetExceeded`] — a node exceeds a decode budget.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a 400-record tree writes every node and loads back
    ///   exact identity/byte pairs, distinguishing omitted nodes and
    ///   substituted encodings. This is a fixed corpus, not generated-tree
    ///   coverage.
    /// - witness: `tests::store::every_node_of_a_tree_loads_back`
    #[inline]
    #[spec(ensures: |ret| ret.is_err()
        || (store.load(self.root_node.identity()).is_ok()
            && self
                .leaves
                .iter()
                .all(|leaf| store.load(leaf.node.identity()).is_ok())))]
    pub fn write_to<S>(
        &self,
        store: &mut S,
    ) -> Result<(), RecordTreeError>
    where
        S: BlockStore + ?Sized,
    {
        store.insert(StoredNode::new(
            self.root_node.identity(),
            self.root_node.bytes(),
        ))?;

        for leaf in self.leaves.as_ref() {
            store.insert(StoredNode::new(leaf.node.identity(), leaf.node.bytes()))?;
        }

        Ok(())
    }

    /// Returns the value bound to a key, when the key is present.
    ///
    /// # Specification
    /// - requires: nothing — a key the tree does not hold is admissible input.
    /// - ensures: the value bound to `key` when the records hold it, and
    ///   nothing otherwise; the lookup reads the key-ordered sequence, so at
    ///   most one record can match.
    /// - provides: the point query a caller makes without building a proof.
    /// - fails: yields nothing for an absent key, which is the non-failure
    ///   absence rather than a refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 over every key of a fifty-record tree and absent keys
    ///   below, between and above it observes exact values or absence. It
    ///   distinguishes wrong neighbours, value substitution and an invented
    ///   match.
    /// - witness: `tests::build::lookup_and_range_answer_from_the_built_tree`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret == self.records.iter().find(|record| record.key() == key).map(Record::value))]
    pub fn lookup(
        &self,
        key: RecordKey<'_>,
    ) -> Option<RecordValue<'_>>
    {
        find_record(self.records.as_ref(), key).map(Record::value)
    }

    /// Returns the records inside a range, in key order.
    ///
    /// # Specification
    /// - requires: nothing — an empty range and a range outside the tree's keys
    ///   are both admissible input.
    /// - ensures: exactly the records whose keys lie in `range`, in key order,
    ///   and an empty slice when none do.
    /// - provides: the interval query a range proof is checked against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 on fifty records observes complete results for
    ///   unbounded, bounded half-open, empty and outside ranges. Exact slices
    ///   distinguish endpoint mistakes, omitted records and permutations.
    /// - witness: `tests::build::lookup_and_range_answer_from_the_built_tree`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.iter().eq(self.records.iter().filter(|record|
        range.contains(record.key()) == crate::record::RangeContainment::Inside)))]
    pub fn range(
        &self,
        range: KeyRange<'_>,
    ) -> Box<[Record]>
    {
        select_in_range(self.records.as_ref(), range)
    }

    /// Decides whether two trees hold the same records.
    ///
    /// # The digest is the fast path, not the decision
    ///
    /// Within one commitment, different roots settle the question: the root is
    /// a function of the parameters and the record sequence, so two roots that
    /// differ come from sequences that differ. Equal roots settle nothing on
    /// their own — reading an equal digest as agreement is a silent false
    /// agreement, which is the one error this comparison must not make — so
    /// an equal-root pair is handed to the deciding comparison over the record
    /// sequences themselves. A pair built under different parameters is not
    /// two versions of one artifact: its commitments differ, and the record
    /// comparison settles that question.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| (ret == RecordAgreement::Agree) == (self.records ==
    ///   other.records)` — the answer is [`RecordAgreement::Agree`] exactly
    ///   when the two record sequences are equal, independently of the digests.
    /// - provides: the agreement question, separated from root identity so that
    ///   a caller cannot answer it by comparing roots.
    /// - fails: never.
    /// - panics: none.
    /// - intension: excluding predicate evaluation, differing roots under equal
    ///   parameters take the fast path; other pairs compare records. The output
    ///   is independent of that optimization.
    ///
    /// # Adequacy
    /// - hypothesis: L1 compares all pairs of six fixed trees, including empty,
    ///   single-record, changed-value and missing-record cases, against direct
    ///   sequence equality. Equal and changed records under different boundary
    ///   parameters distinguish digest-only and parameter-only decisions. The
    ///   answer does not measure whether the fast path ran.
    /// - witness: `tests::agreement::equal_trees_agree`
    /// - witness: `tests::agreement::trees_differing_in_one_value_disagree`
    /// - witness: `tests::agreement::the_answer_is_the_direct_comparison`
    /// - witness: `tests::agreement::trees_under_different_parameters_are_settled_by_the_records`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| (ret == RecordAgreement::Agree) == (self.records == other.records))]
    pub fn agrees_with(
        &self,
        other: &Self,
    ) -> RecordAgreement
    {
        let same_commitment = self.root.params() == other.root.params();

        if same_commitment && self.root.identity() != other.root.identity() {
            return RecordAgreement::Disagree;
        }

        if self.records == other.records {
            RecordAgreement::Agree
        }
        else {
            RecordAgreement::Disagree
        }
    }

    /// Builds a proof that a key is present with the value the tree binds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|proof|
    ///   find_record(self.records.as_ref(), key).is_some_and(|record|
    ///   proof.verify(&self.root, key, record.value()).is_ok()))` — the
    ///   returned proof passes [`MembershipProof::verify`] against this tree's
    ///   root and the queried key and value.
    /// - provides: the membership half of the proving surface.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the key is absent
    ///   or the tree's own structure cannot supply the leaf, which for a tree
    ///   this crate built means only the first.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — the key is absent.
    ///
    /// # Adequacy
    /// - hypothesis: L1 verifies every key of a 300-record tree and a key of a
    ///   five-record single leaf against exact values; node counts distinguish
    ///   the two proof layouts. L3 requires a shape refusal for an absent key,
    ///   separating unconditional success from valid membership evidence.
    /// - witness: `tests::membership::every_key_of_a_tree_proves`
    /// - witness: `tests::membership::an_absent_key_has_no_membership_proof`
    /// - witness: `tests::membership::a_key_of_a_single_leaf_tree_proves`
    #[inline]
    #[spec(ensures: |ret| match find_record(self.records.as_ref(), key) {
        | Some(record) => ret.as_ref().is_ok_and(|proof|
            proof.verify(&self.root, key, record.value()).is_ok()),
        | None => matches!(ret, Err(RecordTreeError::InvalidProofShape { .. })),
    })]
    pub fn prove_membership(
        &self,
        key: RecordKey<'_>,
    ) -> Result<MembershipProof, RecordTreeError>
    {
        let record = find_record(self.records.as_ref(), key).ok_or_else(|| {
            RecordTreeError::InvalidProofShape {
                context: "the key a membership proof was asked for is absent".into(),
            }
        })?;
        let selected = self.selected_leaf(key)?;
        let nodes = match selected {
            | Some(position) => {
                let leaf = self.leaf_node(position)?.clone();

                vec![self.root_node.clone(), leaf]
            },
            | None => vec![self.root_node.clone()],
        };

        Ok(MembershipProof::new(
            ProofEnvelope::new(self.root, ProofKind::Membership),
            self.root_node.identity(),
            record.key(),
            record.value(),
            nodes,
        ))
    }

    /// Builds a proof that a key is absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|proof|
    ///   proof.verify(&self.root, key).is_ok())` — the returned proof passes
    ///   [`NonMembershipProof::verify`] against this tree's root and the
    ///   queried key. That verifier admits the leaf after the selected one
    ///   exactly when the selected leaf holds no key above the queried one and
    ///   a later leaf exists, so one clause carries the whole line.
    /// - provides: the absence half of the proving surface.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the key is present.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — the key is present.
    ///
    /// # Adequacy
    /// - hypothesis: L1 verifies absent keys below, between and above a
    ///   300-record tree and within a five-record single leaf. Exact extreme
    ///   neighbours and required successor layouts distinguish wrong brackets
    ///   and missing leaves; L3 refuses a present key.
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    /// - witness: `tests::absence::a_present_key_has_no_absence_proof`
    /// - witness: `tests::absence::a_key_past_the_last_record_proves`
    /// - witness: `tests::absence::a_key_below_every_record_has_no_predecessor`
    /// - witness: `tests::absence::a_key_absent_from_a_single_leaf_tree_proves`
    #[inline]
    #[spec(ensures: |ret| if find_record(self.records.as_ref(), key).is_some() {
        matches!(ret, Err(RecordTreeError::InvalidProofShape { .. }))
    } else {
        ret.as_ref().is_ok_and(|proof| proof.verify(&self.root, key).is_ok())
    })]
    pub fn prove_non_membership(
        &self,
        key: RecordKey<'_>,
    ) -> Result<NonMembershipProof, RecordTreeError>
    {
        if find_record(self.records.as_ref(), key).is_some() {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the key an absence proof was asked for is present".into(),
            });
        }

        let position = self.selected_leaf(key)?;
        let (nodes, evidence) = if let Some(position) = position {
            let selected = self.leaf_records(position)?;
            let next_position = position.next()?;
            let next = self.leaf_records(next_position).ok();
            let requirement = needs_successor(selected, key)?;
            let leaf = self.leaf_node(position)?.clone();

            match (requirement, next) {
                | (SuccessorLeaf::Required, Some(next_records)) => {
                    let next_leaf = self.leaf_node(next_position)?.clone();
                    let evidence = bracket(selected, Some(next_records), key)?;

                    (vec![self.root_node.clone(), leaf, next_leaf], evidence)
                },
                | (SuccessorLeaf::Required | SuccessorLeaf::NotRequired, _) => {
                    let evidence = bracket(selected, None, key)?;

                    (vec![self.root_node.clone(), leaf], evidence)
                },
            }
        }
        else {
            let evidence = bracket(self.records.as_ref(), None, key)?;

            (vec![self.root_node.clone()], evidence)
        };

        Ok(NonMembershipProof::new(
            ProofEnvelope::new(self.root, ProofKind::NonMembership),
            self.root_node.identity(),
            key,
            evidence,
            nodes,
        ))
    }

    /// Builds a proof of exactly which records a range holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|proof|
    ///   proof.verify(&self.root, range).is_ok())` — the returned proof passes
    ///   [`RangeProof::verify`] against this tree's root and the queried range.
    ///   That verifier re-derives the contiguous leaf run the range selects and
    ///   refuses any other, so one clause carries the whole line.
    /// - provides: the range half of the proving surface.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the tree's own
    ///   structure cannot supply the run, which for a tree this crate built is
    ///   unreachable; [`RecordTreeError::BudgetExceeded`] when the span the
    ///   range selects carries more nodes or materializes more records than the
    ///   proof budgets admit; [`RecordTreeError::ArithmeticOverflow`] when a
    ///   position exceeds its width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — the leaf run is unavailable.
    /// [`RecordTreeError::BudgetExceeded`] — the selected span exceeds a proof
    /// budget.
    /// [`RecordTreeError::ArithmeticOverflow`] — a position exceeds its width.
    ///
    /// # Adequacy
    /// - hypothesis: L1 verifies exact records for 32 generated ranges over 300
    ///   records: lower index 0..300, span 0..60, either upper inclusion. Fixed
    ///   empty, unbounded and single-leaf queries distinguish missing endpoints
    ///   and layouts. L3 checks 4096 carried nodes versus 4097, separating an
    ///   inclusive budget ceiling from its first refusal.
    /// - witness: `tests::range::generated_ranges_prove_and_verify`
    /// - witness: `tests::range::the_unbounded_range_proves`
    /// - witness: `tests::range::an_empty_range_proves`
    /// - witness: `tests::range::a_span_past_the_node_budget_is_refused`
    /// - witness: `tests::range::the_node_budget_ceiling_proves`
    /// - witness: `tests::range::a_range_over_a_single_leaf_tree_proves`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|proof|
        proof.verify(&self.root, range).is_ok_and(|verified|
            verified.iter().eq(self.records.iter().filter(|record|
                range.contains(record.key()) == crate::record::RangeContainment::Inside)))))]
    pub fn prove_range(
        &self,
        range: KeyRange<'_>,
    ) -> Result<RangeProof, RecordTreeError>
    {
        let records = select_in_range(self.records.as_ref(), range);
        let nodes = if self.children.is_empty() {
            vec![self.root_node.clone()]
        }
        else {
            let span = range_span(self.children.as_ref(), range)?;
            let mut nodes = Vec::<ProofNode>::new();
            nodes.push(self.root_node.clone());
            let mut position = span.first();
            let mut records_charged = RecordCount::ZERO;

            loop {
                let child = self.children.get(usize::from(position)).ok_or_else(|| {
                    RecordTreeError::InvalidProofShape {
                        context: "the root names a child it does not carry".into(),
                    }
                })?;
                records_charged = records_charged.plus(child.record_count())?;
                let leaf = self.leaf_node(position)?.clone();
                nodes.push(leaf);

                if position == span.last() {
                    break;
                }

                position = position.next()?;
            }

            let Ok(node_count) = u64::try_from(nodes.len())
            else {
                return Err(RecordTreeError::ArithmeticOverflow {
                    context: "the proof's node count does not fit the wire width".into(),
                });
            };
            let carried = NodeCount::from(node_count);

            ensure_proof_budget(carried, records_charged)?;
            nodes
        };

        Ok(RangeProof::new(
            ProofEnvelope::new(self.root, ProofKind::Range),
            self.root_node.identity(),
            OwnedKeyRange::from_range(range),
            records,
            nodes,
        ))
    }

    /// Returns the leaf a key selects, or nothing when the root is a leaf.
    ///
    /// # Specification
    /// - requires: `key` is arbitrary.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|position| *position ==
    ///   if self.children.is_empty() { None } else {
    ///   select_child(self.children.as_ref(), key) })` — on success the
    ///   position is the leaf the root's separators place `key` in, and `None`
    ///   is the leaf-rooted case.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the root's children
    ///   select no position for the key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 verifies membership for every key of a 300-record tree
    ///   and a five-record single leaf. Absence queries straddling separators
    ///   distinguish a wrong child or confusing the leaf-rooted case with a
    ///   missing leaf.
    /// - witness: `tests::membership::every_key_of_a_tree_proves`
    /// - witness: `tests::membership::a_key_of_a_single_leaf_tree_proves`
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|position| *position
        == if self.children.is_empty() { None } else { select_child(self.children.as_ref(), key) }))]
    fn selected_leaf(
        &self,
        key: RecordKey<'_>,
    ) -> Result<Option<ChildIndex>, RecordTreeError>
    {
        if self.children.is_empty() {
            return Ok(None);
        }

        let position = select_child(self.children.as_ref(), key).ok_or_else(|| {
            RecordTreeError::InvalidProofShape {
                context: "the root selects no child for the key".into(),
            }
        })?;

        Ok(Some(position))
    }

    /// Returns the leaf node at a position.
    ///
    /// # Specification
    /// - requires: nothing; the position may be outside the tree.
    /// - ensures: `|ret| ret.as_ref().ok().copied() ==
    ///   self.leaves.get(usize::from(position)).map(|leaf| &leaf.node)` — on
    ///   success the node is the leaf the tree holds at `position`.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the position is
    ///   outside the tree.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 through every membership key of a 300-record tree
    ///   observes the authenticated selected leaf. Invalid positions are
    ///   unreachable from admitted membership construction; trailing absence
    ///   queries separately exercise the record-view boundary.
    /// - witness: `tests::membership::every_key_of_a_tree_proves`
    #[spec(ensures: |ret| self.leaves.get(usize::from(position)).map_or_else(
        || matches!(ret, Err(RecordTreeError::InvalidProofShape { .. })),
        |leaf| ret.as_ref().is_ok_and(|actual| core::ptr::eq(core::ptr::from_ref(*actual), &raw const leaf.node)),
    ))]
    fn leaf_node(
        &self,
        position: ChildIndex,
    ) -> Result<&ProofNode, RecordTreeError>
    {
        self.leaves
            .get(usize::from(position))
            .map(|leaf| &leaf.node)
            .ok_or_else(|| RecordTreeError::InvalidProofShape {
                context: "the selected leaf position is outside the tree".into(),
            })
    }

    /// Returns the records held by the leaf at a position.
    ///
    /// # Specification
    /// - requires: nothing; the position may be outside the tree.
    /// - ensures: `|ret| ret.as_ref().ok().copied() ==
    ///   self.leaves.get(usize::from(position)).and_then(|leaf|
    ///   self.records.get(usize::from(leaf.span.start()) ..
    ///   usize::from(leaf.span.end())))` — on success the records are exactly
    ///   those the tree holds in the leaf at `position`.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the position is
    ///   outside the tree or its record run is outside the record sequence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 verifies absent queries before, between and after 300
    ///   records, observing exact predecessor/successor records. The last-leaf
    ///   query probes an out-of-range successor and requires no successor,
    ///   distinguishing truncated leaf views and an invented following leaf.
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    /// - witness: `tests::absence::a_key_below_every_record_has_no_predecessor`
    /// - witness: `tests::absence::a_key_past_the_last_record_proves`
    #[spec(ensures: |ret| self.leaves.get(usize::from(position)).and_then(|leaf|
        self.records.get(usize::from(leaf.span.start()) .. usize::from(leaf.span.end())))
        .map_or_else(|| matches!(ret, Err(RecordTreeError::InvalidProofShape { .. })),
            |expected| ret.as_ref().is_ok_and(|actual| core::ptr::eq(core::ptr::from_ref(*actual), core::ptr::from_ref(expected)))))]
    fn leaf_records(
        &self,
        position: ChildIndex,
    ) -> Result<&[Record], RecordTreeError>
    {
        let leaf = self.leaves.get(usize::from(position)).ok_or_else(|| {
            RecordTreeError::InvalidProofShape {
                context: "the selected leaf position is outside the tree".into(),
            }
        })?;

        self.records
            .get(usize::from(leaf.span.start()) .. usize::from(leaf.span.end()))
            .ok_or_else(|| RecordTreeError::InvalidProofShape {
                context: "a leaf run is outside the record sequence".into(),
            })
    }
}

/// Whether two trees hold the same records.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecordAgreement
{
    /// The two trees hold the same records.
    Agree,
    /// The two trees hold different records.
    Disagree,
}

/// A root whose root node was found in a store and verified.
///
/// Verification covers only the root node. The handle does not traverse
/// children or attest that every leaf is present; queries and proof
/// construction require a [`RecordTree`].
///
/// # Specification
/// - requires: construction through `StoredRoot::open`.
/// - ensures: the manifest binds the retained node identity; the node was
///   verified when opened, without a promise of future store availability.
/// - provides: a store handle with a checked manifest-to-node relation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 opens a written three-record tree, then substitutes a leaf
///   identity for the root and observes a false refinement. A 400-record store
///   witness distinguishes present and subsequently absent root material.
/// - witness: `tree::tests::built_state_refinements_reject_cache_corruption`
/// - witness: `tests::store::a_written_root_opens`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[spec(maintains: self.root.ensure_binds(self.root_node_hash).is_ok())]
pub struct StoredRoot
{
    /// The root manifest.
    root: TreeRoot,
    /// The identity of the root node found in the store.
    root_node_hash: NodeHash,
}

impl StoredRoot
{
    /// Finds and verifies a root's node in a store.
    ///
    /// # Specification
    /// - requires: `root` is a manifest the caller accepts on other grounds.
    /// - ensures: `|ret| ret.is_err() ||
    ///   (root.ensure_binds(root_node_hash).is_ok() &&
    ///   store.load(root_node_hash).is_ok())` — on success the store holds a
    ///   node under `root_node_hash` whose bytes recompute to it and decode as
    ///   canonical node material, and the manifest binds that node.
    /// - provides: the store's entry point for a root.
    /// - fails: [`RecordTreeError::UnknownNode`] when the store does not hold
    ///   the node; [`RecordTreeError::HashMismatch`] when the manifest does not
    ///   bind it or the stored bytes do not recompute; plus every node-decoding
    ///   failure.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::UnknownNode`] — the store does not hold the node.
    /// [`RecordTreeError::HashMismatch`] — the manifest does not bind the node,
    /// or the stored bytes do not recompute.
    /// [`RecordTreeError::MalformedNode`] — the stored bytes are not node
    /// material.
    /// [`RecordTreeError::UnsupportedVersion`] — unsupported encoding version.
    /// [`RecordTreeError::IncompatibleParameters`] — unsupported parameter.
    /// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its
    /// ceiling.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surfaces are the store lookup and
    ///   the manifest binding, separated by a written tree, an unwritten one,
    ///   and a manifest bound to a different node.
    /// - witness: `tests::store::a_written_root_opens`
    /// - witness: `tests::store::an_unwritten_root_does_not_open`
    /// - witness: `tests::store::a_root_bound_elsewhere_does_not_open`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|opened|
        opened.root == root && opened.root_node_hash == root_node_hash
            && anodized::types::Spec::predicate(opened) && store.load(root_node_hash).is_ok()))]
    pub fn open<S>(
        root: TreeRoot,
        root_node_hash: NodeHash,
        store: &S,
    ) -> Result<Self, RecordTreeError>
    where
        S: BlockStore + ?Sized,
    {
        root.ensure_binds(root_node_hash)?;
        let _node = store.load(root_node_hash)?;

        Ok(Self {
            root,
            root_node_hash,
        })
    }

    /// Returns the root manifest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> TreeRoot
    {
        self.root
    }

    /// Returns the identity of the root node found in the store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node_hash(&self) -> NodeHash
    {
        self.root_node_hash
    }

    /// Re-checks that the root node is still present and still verifies.
    ///
    /// # Specification
    /// - requires: `self` is a handle one [`StoredRoot::open`] produced.
    /// - ensures: `|ret| ret.is_err() ||
    ///   store.load(self.root_node_hash).is_ok()` — on success the store still
    ///   holds the root node under its identity, and the stored bytes still
    ///   verify against it.
    /// - fails: the [`StoredRoot::open`] failures, re-run against the store's
    ///   present contents.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::UnknownNode`] — the store no longer holds the node.
    /// [`RecordTreeError::HashMismatch`] — the stored bytes no longer
    /// recompute.
    /// [`RecordTreeError::MalformedNode`] — the stored bytes are no longer node
    /// material.
    /// [`RecordTreeError::UnsupportedVersion`] — unsupported encoding version.
    /// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its
    /// ceiling.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on an opened 400-record root checks success in its
    ///   populated store and `UnknownNode` with the exact identity in an empty
    ///   store. This separates a stale unconditional success from a fresh
    ///   availability check.
    /// - witness: `tests::store::a_written_root_opens`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || store.load(self.root_node_hash).is_ok())]
    pub fn recheck<S>(
        &self,
        store: &S,
    ) -> Result<(), RecordTreeError>
    where
        S: BlockStore + ?Sized,
    {
        let _node = store.load(self.root_node_hash)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use super::RecordTree;
    use super::StoredRoot;
    use crate::boundary::BoundaryMaskBits;
    use crate::boundary::BoundaryParams;
    use crate::boundary::BoundaryProfile;
    use crate::boundary::BoundaryRecordCap;
    use crate::params::EncodingVersion;
    use crate::params::HashAlgorithm;
    use crate::params::SeparatorConvention;
    use crate::params::TreeKind;
    use crate::params::TreeParams;
    use crate::params::TreeRoot;
    use crate::proof::ProofNode;
    use crate::record::RecordCount;
    use crate::record::RecordRef;
    use crate::store::InMemoryBlockStore;

    #[test]
    fn built_state_refinements_reject_cache_corruption()
    {
        let boundary = BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::MIN,
            BoundaryRecordCap::try_from(1_u32).expect("one record per leaf is admissible"),
        );
        let params = TreeParams::new(
            TreeKind::CURRENT,
            EncodingVersion::CURRENT,
            HashAlgorithm::CURRENT,
            SeparatorConvention::CURRENT,
            boundary,
        );
        let mut tree = RecordTree::build(
            &[
                RecordRef::new(b"a", b"1"),
                RecordRef::new(b"m", b"2"),
                RecordRef::new(b"z", b"3"),
            ],
            params,
        )
        .expect("the ordered corpus builds");
        assert!(anodized::types::Spec::predicate(&tree));
        let mut store = InMemoryBlockStore::new();
        tree.write_to(&mut store).expect("the built nodes store");
        let mut opened = StoredRoot::open(tree.root(), tree.root_node_hash(), &store)
            .expect("the written root opens");
        assert!(anodized::types::Spec::predicate(&opened));
        assert!(tree.leaves.len() >= 2_usize);
        opened.root_node_hash = tree.leaves[0_usize].node.identity();
        assert!(!anodized::types::Spec::predicate(&opened));

        let root = tree.root;
        tree.root = TreeRoot::seal(params, RecordCount::from(4_u64), tree.root_node.identity())
            .expect("the substituted count has a manifest");
        assert!(!anodized::types::Spec::predicate(&tree));
        tree.root = root;
        tree.records.swap(0_usize, 1_usize);
        assert!(!anodized::types::Spec::predicate(&tree));
        tree.records.swap(0_usize, 1_usize);
        tree.children.swap(0_usize, 1_usize);
        assert!(!anodized::types::Spec::predicate(&tree));
        tree.children.swap(0_usize, 1_usize);
        let span = tree.leaves[0_usize].span;
        tree.leaves[0_usize].span = tree.leaves[1_usize].span;
        assert!(!anodized::types::Spec::predicate(&tree));
        tree.leaves[0_usize].span = span;
        let identity = tree.leaves[0_usize].node.identity();
        let node = core::mem::replace(
            &mut tree.leaves[0_usize].node,
            ProofNode::new(identity, b"corrupt"),
        );
        assert!(!anodized::types::Spec::predicate(&tree.leaves[0_usize]));
        assert!(!anodized::types::Spec::predicate(&tree));
        tree.leaves[0_usize].node = node;
        assert!(anodized::types::Spec::predicate(&tree));
    }
}
