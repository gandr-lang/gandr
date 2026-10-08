//! The tree itself: how a sorted record sequence becomes nodes and a root, what
//! the tree answers, and what it can prove.
//!
//! # Two levels, and why that is the shape today
//!
//! A tree is either one leaf, or one internal root over a run of leaves. Every
//! structure and every proof in this crate is written for that shape and
//! refuses any other, so nothing here silently half-works on a deeper tree.
//!
//! Depth beyond two is the crate's named open work. The record count one
//! internal root can address is bounded by the child ceiling, and past it the
//! root has to become a level of internal nodes over internal nodes. That lift
//! changes the proof shapes — a membership proof becomes a path rather than a
//! pair — and is the keyed plane's half of the storage tier's multi-level
//! question.
//!
//! # What building does
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
#[derive(Clone, Debug, Eq, PartialEq)]
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
/// - provides: lookup, range, proof construction and the store write. The
///   postcondition stays prose: it is an invariant of every value of this type,
///   and a data specification's `maintains` is not evaluated when a value is
///   constructed, so a clause here would be inert.
/// - fails: only at construction and at proof construction, as those state.
/// - panics: none.
#[derive(Clone, Debug, Eq, PartialEq)]
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
    /// - requires: `records` is strictly increasing in key order; `params` is a
    ///   parameter set this build implements.
    /// - ensures: the built tree's root is a function of the record sequence
    ///   and the parameters alone, so two builders that agree on both agree on
    ///   the root. An empty sequence gives a tree of one empty leaf.
    /// - provides: the only constructor. The postcondition stays prose: that
    ///   the root is a function of its inputs is a law over two builds, and one
    ///   call carries one input pair.
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
    /// - hypothesis: L2 agreement — the root is required to be a function of
    ///   the record set, asserted as a differential between a tree built in one
    ///   call and one built from the same records reconstructed differently,
    ///   over generated corpora; plus L3 for each refusal and for the two
    ///   shapes, separated by the empty input, a single-leaf input and a
    ///   multi-leaf input.
    /// - witness: `tests::build::the_root_is_a_function_of_the_records`
    /// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
    /// - witness: `tests::build::a_small_tree_is_a_single_leaf`
    /// - witness: `tests::build::a_large_tree_has_an_internal_root`
    /// - witness: `tests::build::unsorted_input_is_refused`
    /// - witness: `tests::build::duplicate_keys_are_refused`
    #[inline]
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    /// - provides: the whole node set a caller writes to a store or checks a
    ///   proof against, in one pass and one allocation.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
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
    /// - hypothesis: L2 agreement — every written node is required to load back
    ///   byte-identical, asserted over generated trees.
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    /// - intension: the fast path settles disagreement only between roots that
    ///   commit to the same parameters; every other pair runs the record
    ///   comparison, which is what makes the digest a fast path rather than a
    ///   decision. The observation is the answer, which is unchanged by the
    ///   fast path.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surface is the two-stage
    ///   comparison, separated by equal trees, by trees differing in one record
    ///   value, and by the noninterference case: the answer must not change if
    ///   the fast path is removed, asserted by comparing against the direct
    ///   record comparison over generated pairs.
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
    /// - hypothesis: L1 evidence — the proof is the witness and the verifier is
    ///   its validator, so the obligation is that every proof this builds
    ///   verifies, asserted over every key of generated trees; plus L3 for the
    ///   absent-key refusal.
    /// - witness: `tests::membership::every_key_of_a_tree_proves`
    /// - witness: `tests::membership::an_absent_key_has_no_membership_proof`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|proof| {
        find_record(self.records.as_ref(), key)
            .is_some_and(|record| proof.verify(&self.root, key, record.value()).is_ok())
    }))]
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
    /// - hypothesis: L1 evidence — every proof this builds must verify,
    ///   asserted over absent keys spanning below, between and above the tree's
    ///   records; plus L3 for the present-key refusal and for the two carried
    ///   layouts.
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    /// - witness: `tests::absence::a_present_key_has_no_absence_proof`
    /// - witness: `tests::absence::a_key_past_the_last_record_proves`
    #[inline]
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|proof| proof.verify(&self.root, key).is_ok()))]
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
    /// - hypothesis: L1 evidence — every proof this builds must verify and must
    ///   return exactly the range's records, asserted over generated ranges
    ///   including the empty range, one-key ranges and the unbounded range.
    /// - witness: `tests::range::generated_ranges_prove_and_verify`
    /// - witness: `tests::range::the_unbounded_range_proves`
    /// - witness: `tests::range::an_empty_range_proves`
    /// - witness: `tests::range::a_span_past_the_node_budget_is_refused`
    /// - witness: `tests::range::the_node_budget_ceiling_proves`
    #[inline]
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|proof| proof.verify(&self.root, range).is_ok()))]
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
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|position| {
        *position
            == if self.children.is_empty() {
                None
            }
            else {
                select_child(self.children.as_ref(), key)
            }
    }))]
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
    #[spec(ensures: |ret| ret.as_ref().ok().copied()
        == self.leaves.get(usize::from(position)).map(|leaf| &leaf.node))]
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
    #[spec(ensures: |ret| ret.as_ref().ok().copied()
        == self.leaves.get(usize::from(position)).and_then(|leaf| {
            self.records
                .get(usize::from(leaf.span.start()) .. usize::from(leaf.span.end()))
        }))]
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
/// The handle says exactly that and no more. It is not a store-backed tree: it
/// does not walk children, so it does not attest that the tree below the root
/// is present. A store-backed reader is named open work rather than half-built
/// here, because a handle that answered queries from a partially present tree
/// would be the worst of both.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    #[spec(ensures: |ret| ret.is_err()
        || (root.ensure_binds(root_node_hash).is_ok() && store.load(root_node_hash).is_ok()))]
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
