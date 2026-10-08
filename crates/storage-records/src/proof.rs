//! Store-independent proofs: what a prover hands over, and what a verifier
//! re-derives rather than believes.
//!
//! # The verifier trusts one thing
//!
//! A verifier is given a [`TreeRoot`] it already accepts and a proof. Nothing
//! else is trusted: every node identity is recomputed from the carried bytes,
//! the root manifest is recomputed from the parameters and the claimed root
//! node, every child reference is checked against the child it names, and the
//! answer — the value, the adjacent records, the range's records — is derived
//! from the authenticated nodes and then compared against what the proof
//! claimed. A proof that claims a correct answer with material that does not
//! derive it is refused.
//!
//! # One shape per proof kind
//!
//! Each proof kind admits exactly one node layout, checked by position rather
//! than by searching for a node with a wanted identity:
//!
//! - **membership** — the root node, then the leaf the key selects;
//! - **non-membership** — the root node, the leaf the key selects, and the next
//!   leaf when and only when the selected leaf carries no key above the absent
//!   one;
//! - **range** — the root node, then the contiguous run of leaves the range
//!   selects, in separator order.
//!
//! A tree whose root is a leaf carries that one node and nothing else. Refusing
//! every other layout means a verifier has one path per kind, so there is no
//! second path to disagree with the first.
//!
//! # What a digest match does not license
//!
//! Node identities are compared only against identities recomputed from bytes
//! the verifier holds. No comparison here reads an equal digest as an agreement
//! between two things the verifier has not both seen: that direction of error
//! is a silent false agreement, and it is the one failure a proof must not
//! admit.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;

use crate::bytes::EncodedNode;
use crate::bytes::NodeHash;
use crate::bytes::OwnedEncodedNode;
use crate::bytes::OwnedRecordKey;
use crate::bytes::OwnedRecordValue;
use crate::bytes::RecordKey;
use crate::bytes::RecordValue;
use crate::error::FailureContext;
use crate::error::RecordTreeError;
use crate::node::ChildIndex;
use crate::node::ChildRef;
use crate::node::DecodedNode;
use crate::node::InternalNode;
use crate::node::LeafNode;
use crate::node::decode_node;
use crate::node::hash_node;
use crate::node::inspect_node;
use crate::node::select_child;
use crate::params::TreeRoot;
use crate::record::KeyRange;
use crate::record::OwnedKeyRange;
use crate::record::Record;
use crate::record::RecordCount;
use crate::record::find_record;
use crate::record::select_in_range;
use crate::wire::DecodeWork;

/// Which question a proof answers.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ProofKind
{
    /// A key is present, with a stated value.
    Membership,
    /// A key is absent.
    NonMembership,
    /// A range's records are exactly these.
    Range,
}

/// The root a proof is interpreted against, and the question it answers.
///
/// The envelope carries the root itself rather than a copy of the root's
/// parameters beside it. A copy would be a second statement of the same fact
/// that a verifier then has to reconcile with the first, and a reconciliation
/// that can fail is a failure mode with no purpose: the parameters are already
/// inside the root's digest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProofEnvelope
{
    /// The root the proof is interpreted against.
    root: TreeRoot,
    /// The question the proof answers.
    kind: ProofKind,
}

impl ProofEnvelope
{
    /// Builds an envelope.
    ///
    /// # Specification
    /// - requires: `root` is the manifest the proof is to be interpreted
    ///   against, and `kind` the question it answers.
    /// - ensures: the envelope carries exactly that root and that question.
    /// - provides: the root itself rather than a copy of its parameters, for
    ///   the reason the type's own prose states.
    /// - fails: never — a verifier decides whether it accepts the root.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new(
        root: TreeRoot,
        kind: ProofKind,
    ) -> Self
    {
        Self { root, kind }
    }

    /// Returns the root the proof is interpreted against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> TreeRoot
    {
        self.root
    }

    /// Returns the question the proof answers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> ProofKind
    {
        self.kind
    }
}

/// One node a proof carries: its bytes, and the identity claimed for them.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ProofNode
{
    /// The claimed identity.
    hash: NodeHash,
    /// The canonical node encoding.
    bytes: OwnedEncodedNode,
}

impl ProofNode
{
    /// Builds a carried node.
    ///
    /// # Specification
    /// - requires: nothing — bytes that do not hash to `hash` are admissible
    ///   input and are exactly what verification refuses.
    /// - ensures: the node carries exactly the identity and the bytes offered,
    ///   unchecked.
    /// - provides: the carried unit a verifier recomputes an identity from, so
    ///   a proof never states an identity without the bytes behind it.
    /// - fails: never — the pairing is checked at verification.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn new<B>(
        hash: NodeHash,
        bytes: B,
    ) -> Self
    where
        B: Into<OwnedEncodedNode>,
    {
        Self {
            hash,
            bytes: bytes.into(),
        }
    }

    /// Returns the claimed identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn identity(&self) -> NodeHash
    {
        self.hash
    }

    /// Returns the canonical node encoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn bytes(&self) -> EncodedNode<'_>
    {
        self.bytes.as_borrowed()
    }
}

/// The records that bracket an absent key.
///
/// Absence is proved by exhibiting the neighbours: a predecessor below the key
/// and a successor above it, both authenticated, with a missing neighbour
/// meaning the key falls outside the tree's range on that side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NonMembershipEvidence
{
    /// The greatest authenticated record below the absent key.
    predecessor: Option<Record>,
    /// The least authenticated record above the absent key.
    successor: Option<Record>,
}

impl NonMembershipEvidence
{
    /// Builds absence evidence.
    ///
    /// # Specification
    /// - requires: nothing; either neighbour may be absent, which is how a key
    ///   outside the tree's range on that side is stated.
    /// - ensures: the evidence carries exactly the two neighbours offered.
    /// - provides: the bracketing pair absence is proved by exhibiting.
    /// - fails: never — whether the pair really brackets the key is decided at
    ///   verification.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new(
        predecessor: Option<Record>,
        successor: Option<Record>,
    ) -> Self
    {
        Self {
            predecessor,
            successor,
        }
    }

    /// Returns the greatest authenticated record below the absent key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn predecessor(&self) -> Option<&Record>
    {
        self.predecessor.as_ref()
    }

    /// Returns the least authenticated record above the absent key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn successor(&self) -> Option<&Record>
    {
        self.successor.as_ref()
    }
}

/// A proof that a key is present with a stated value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MembershipProof
{
    /// The root and question.
    envelope: ProofEnvelope,
    /// The identity of the tree's root node.
    root_node_hash: NodeHash,
    /// The key the proof answers for.
    key: OwnedRecordKey,
    /// The value the proof claims is bound to the key.
    value: OwnedRecordValue,
    /// The root node, then the leaf the key selects.
    nodes: Box<[ProofNode]>,
}

impl MembershipProof
{
    /// Builds a membership proof from its parts.
    ///
    /// # Specification
    /// - requires: nothing — every part is a claim, and a proof assembled from
    ///   parts that do not agree is admissible input that verification refuses.
    /// - ensures: the proof carries exactly the envelope, root-node identity,
    ///   key, value, and nodes offered, in the order given.
    /// - provides: the wire shape a proof travels in, so a decoder and a
    ///   builder produce the same value.
    /// - fails: never — every check lives in verification.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn new<K, V, N>(
        envelope: ProofEnvelope,
        root_node_hash: NodeHash,
        key: K,
        value: V,
        nodes: N,
    ) -> Self
    where
        K: Into<OwnedRecordKey>,
        V: Into<OwnedRecordValue>,
        N: Into<Box<[ProofNode]>>,
    {
        Self {
            envelope,
            root_node_hash,
            key: key.into(),
            value: value.into(),
            nodes: nodes.into(),
        }
    }

    /// Returns the root and question.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn envelope(&self) -> ProofEnvelope
    {
        self.envelope
    }

    /// Returns the identity of the tree's root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node_hash(&self) -> NodeHash
    {
        self.root_node_hash
    }

    /// Returns the key the proof answers for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(&self) -> RecordKey<'_>
    {
        self.key.as_borrowed()
    }

    /// Returns the value the proof claims is bound to the key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn value(&self) -> RecordValue<'_>
    {
        self.value.as_borrowed()
    }

    /// Returns the carried nodes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the carried nodes in the order the proof was constructed
    ///   with, neither filtered nor reordered; no position is guaranteed to
    ///   hold a root or the selected leaf.
    /// - provides: the material a verifier recomputes identities from;
    ///   [`MembershipProof::verify`] is what interprets the claimed layout and
    ///   refuses a sequence that does not have it.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ProofNode]
    {
        self.nodes.as_ref()
    }

    /// Checks the proof against a root the verifier already accepts and the
    /// query it was asked for.
    ///
    /// # Specification
    /// - requires: `expected_root` is a root the caller accepts on other
    ///   grounds; the proof is arbitrary and possibly hostile.
    /// - ensures: on success the key is bound to the value in the tree named by
    ///   `expected_root`, established from the carried bytes alone.
    /// - provides: the membership half of the crate's verification surface. The
    ///   postcondition stays prose: it names the tree `expected_root` denotes,
    ///   which this call never holds — it holds only the bytes the proof
    ///   carries.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the envelope, the
    ///   query, the node layout or the derived binding disagrees;
    ///   [`RecordTreeError::HashMismatch`] when a carried node or the root
    ///   manifest does not recompute; plus every node-decoding failure.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — envelope, query, layout or
    /// binding disagreement.
    /// [`RecordTreeError::HashMismatch`] — a node or the root manifest does not
    /// recompute.
    /// [`RecordTreeError::MalformedNode`] — a carried node is not canonical.
    /// [`RecordTreeError::UnsupportedVersion`] — a carried node names an
    /// unknown encoding version.
    /// [`RecordTreeError::DuplicateKeys`] — a carried leaf repeats a key.
    /// [`RecordTreeError::BudgetExceeded`] — the proof exceeds a decode budget.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L1 evidence — the proof is the checkable witness and this
    ///   is its validator, so the residue is that each rejection arm has a
    ///   distinguishing input; each is named as its own witness, and the
    ///   accepting case rides the round-trip property over generated trees.
    /// - witness: `tests::membership::a_valid_proof_verifies`
    /// - witness: `tests::membership::a_foreign_root_is_refused`
    /// - witness: `tests::membership::a_wrong_kind_is_refused`
    /// - witness: `tests::membership::a_different_query_is_refused`
    /// - witness: `tests::membership::a_wrong_value_is_refused`
    /// - witness: `tests::membership::a_tampered_node_is_refused`
    /// - witness: `tests::membership::an_extra_node_is_refused`
    /// - witness: `tests::membership::a_substituted_leaf_is_refused`
    #[inline]
    pub fn verify(
        &self,
        expected_root: &TreeRoot,
        expected_key: RecordKey<'_>,
        expected_value: RecordValue<'_>,
    ) -> Result<(), RecordTreeError>
    {
        ensure_envelope(&self.envelope, expected_root, ProofKind::Membership)?;

        if self.key() != expected_key {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the proof answers for a different key".into(),
            });
        }

        if self.value() != expected_value {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the proof claims a different value".into(),
            });
        }

        let mut work = DecodeWork::new();
        let carried = decode_carried(self.nodes.as_ref(), &mut work)?;
        let root = open_root(&carried, expected_root, self.root_node_hash)?;

        let leaf = match root {
            | RootNode::Leaf(leaf) => {
                ensure_node_count(
                    &carried,
                    CarriedCount::ROOT_ONLY,
                    "membership over a leaf root".into(),
                )?;
                ensure_leaf_total(leaf, expected_root.record_count())?;
                leaf
            },
            | RootNode::Internal(internal) => {
                ensure_node_count(
                    &carried,
                    CarriedCount::ROOT_AND_LEAF,
                    "membership over an internal root".into(),
                )?;
                ensure_internal_total(internal, expected_root.record_count())?;
                let position =
                    select_child(internal.children(), expected_key).ok_or_else(|| {
                        RecordTreeError::InvalidProofShape {
                            context: "the root selects no child for the key".into(),
                        }
                    })?;
                let child = child_at(internal, position)?;

                leaf_at(&carried, CarriedIndex::SELECTED_LEAF, child)?
            },
        };

        let record = find_record(leaf.records(), expected_key).ok_or_else(|| {
            RecordTreeError::InvalidProofShape {
                context: "the authenticated leaf does not carry the key".into(),
            }
        })?;

        if record.value() != expected_value {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the authenticated leaf binds the key to another value".into(),
            });
        }

        Ok(())
    }
}

/// A proof that a key is absent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NonMembershipProof
{
    /// The root and question.
    envelope: ProofEnvelope,
    /// The identity of the tree's root node.
    root_node_hash: NodeHash,
    /// The key the proof answers for.
    key: OwnedRecordKey,
    /// The neighbours bracketing the absent key.
    evidence: NonMembershipEvidence,
    /// The root node, the selected leaf, and the next leaf when one is needed.
    nodes: Box<[ProofNode]>,
}

impl NonMembershipProof
{
    /// Builds an absence proof from its parts.
    ///
    /// # Specification
    /// - requires: nothing — every part is a claim, and a proof assembled from
    ///   parts that do not agree is admissible input that verification refuses.
    /// - ensures: the proof carries exactly the envelope, root-node identity,
    ///   key, evidence, and nodes offered, in the order given.
    /// - provides: the wire shape an absence proof travels in.
    /// - fails: never — every check lives in verification.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn new<K, N>(
        envelope: ProofEnvelope,
        root_node_hash: NodeHash,
        key: K,
        evidence: NonMembershipEvidence,
        nodes: N,
    ) -> Self
    where
        K: Into<OwnedRecordKey>,
        N: Into<Box<[ProofNode]>>,
    {
        Self {
            envelope,
            root_node_hash,
            key: key.into(),
            evidence,
            nodes: nodes.into(),
        }
    }

    /// Returns the root and question.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn envelope(&self) -> ProofEnvelope
    {
        self.envelope
    }

    /// Returns the identity of the tree's root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node_hash(&self) -> NodeHash
    {
        self.root_node_hash
    }

    /// Returns the key the proof answers for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn key(&self) -> RecordKey<'_>
    {
        self.key.as_borrowed()
    }

    /// Returns the neighbours the proof claims bracket the absent key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn evidence(&self) -> &NonMembershipEvidence
    {
        &self.evidence
    }

    /// Returns the carried nodes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the carried nodes in the order the proof was constructed
    ///   with, neither filtered nor reordered; no position is guaranteed to
    ///   hold a root, the selected leaf, or a successor leaf.
    /// - provides: the material a verifier recomputes identities from;
    ///   [`NonMembershipProof::verify`] is what interprets the claimed layout
    ///   and refuses a sequence that does not have it.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ProofNode]
    {
        self.nodes.as_ref()
    }

    /// Checks the proof against a root the verifier already accepts and the
    /// query it was asked for.
    ///
    /// # Specification
    /// - requires: `expected_root` is a root the caller accepts on other
    ///   grounds; the proof is arbitrary and possibly hostile.
    /// - ensures: on success the key is absent from the tree named by
    ///   `expected_root`, and the returned evidence is the bracketing pair
    ///   re-derived from the carried bytes rather than the pair the proof
    ///   claimed — the two are required to agree.
    /// - provides: the absence half of the crate's verification surface. The
    ///   postcondition stays prose: its first half names the tree
    ///   `expected_root` denotes, which this call never holds, and a clause for
    ///   the derived-against-claimed half alone would be weaker than the line
    ///   it replaces.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the envelope, the
    ///   query, the node layout, the derived evidence, or the key's presence
    ///   disagrees; [`RecordTreeError::HashMismatch`] when a carried node or
    ///   the root manifest does not recompute; plus every node-decoding
    ///   failure.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — envelope, query, layout,
    /// evidence, or presence disagreement.
    /// [`RecordTreeError::HashMismatch`] — a node or the root manifest does not
    /// recompute.
    /// [`RecordTreeError::MalformedNode`] — a carried node is not canonical.
    /// [`RecordTreeError::UnsupportedVersion`] — a carried node names an
    /// unknown encoding version.
    /// [`RecordTreeError::DuplicateKeys`] — a carried leaf repeats a key.
    /// [`RecordTreeError::BudgetExceeded`] — the proof exceeds a decode budget.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L1 evidence — the derived bracketing pair is the checkable
    ///   witness and is compared against the claim, so a forged claim cannot
    ///   pass; the residue is the layout arms, each named as its own witness,
    ///   and the accepting cases ride the property over generated trees.
    /// - witness: `tests::absence::a_valid_proof_verifies`
    /// - witness: `tests::absence::a_present_key_has_no_absence_proof`
    /// - witness: `tests::absence::forged_evidence_is_refused`
    /// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
    /// - witness: `tests::absence::an_unnecessary_successor_leaf_is_refused`
    #[inline]
    pub fn verify(
        &self,
        expected_root: &TreeRoot,
        expected_key: RecordKey<'_>,
    ) -> Result<NonMembershipEvidence, RecordTreeError>
    {
        ensure_envelope(&self.envelope, expected_root, ProofKind::NonMembership)?;

        if self.key() != expected_key {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the proof answers for a different key".into(),
            });
        }

        let mut work = DecodeWork::new();
        let carried = decode_carried(self.nodes.as_ref(), &mut work)?;
        let root = open_root(&carried, expected_root, self.root_node_hash)?;

        let derived = match root {
            | RootNode::Leaf(leaf) => {
                ensure_node_count(
                    &carried,
                    CarriedCount::ROOT_ONLY,
                    "absence over a leaf root".into(),
                )?;
                ensure_leaf_total(leaf, expected_root.record_count())?;
                bracket(leaf.records(), None, expected_key)?
            },
            | RootNode::Internal(internal) => {
                ensure_internal_total(internal, expected_root.record_count())?;
                let position =
                    select_child(internal.children(), expected_key).ok_or_else(|| {
                        RecordTreeError::InvalidProofShape {
                            context: "the root selects no child for the key".into(),
                        }
                    })?;
                let child = child_at(internal, position)?;
                let leaf = leaf_at(&carried, CarriedIndex::SELECTED_LEAF, child)?;
                let next_position = position.next()?;
                let next = internal.children().get(usize::from(next_position));

                match (needs_successor(leaf.records(), expected_key)?, next) {
                    | (SuccessorLeaf::Required, Some(next_child)) => {
                        ensure_node_count(
                            &carried,
                            CarriedCount::ROOT_AND_TWO_LEAVES,
                            "absence needing the next leaf".into(),
                        )?;
                        let next_leaf =
                            leaf_at(&carried, CarriedIndex::SUCCESSOR_LEAF, next_child)?;
                        bracket(leaf.records(), Some(next_leaf.records()), expected_key)?
                    },
                    | (SuccessorLeaf::Required | SuccessorLeaf::NotRequired, _) => {
                        ensure_node_count(
                            &carried,
                            CarriedCount::ROOT_AND_LEAF,
                            "absence not needing the next leaf".into(),
                        )?;
                        bracket(leaf.records(), None, expected_key)?
                    },
                }
            },
        };

        if derived != self.evidence {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the claimed neighbours are not the authenticated ones".into(),
            });
        }

        Ok(derived)
    }
}

/// A proof that a range's records are exactly the carried ones.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RangeProof
{
    /// The root and question.
    envelope: ProofEnvelope,
    /// The identity of the tree's root node.
    root_node_hash: NodeHash,
    /// The range the proof answers for.
    range: OwnedKeyRange,
    /// The records the proof claims the range holds.
    records: Box<[Record]>,
    /// The root node, then the leaves the range selects.
    nodes: Box<[ProofNode]>,
}

impl RangeProof
{
    /// Builds a range proof from its parts.
    ///
    /// # Specification
    /// - requires: nothing — every part is a claim, and a proof assembled from
    ///   parts that do not agree is admissible input that verification refuses.
    /// - ensures: the proof carries exactly the envelope, root-node identity,
    ///   range, records, and nodes offered, in the order given.
    /// - provides: the wire shape a range proof travels in.
    /// - fails: never — every check lives in verification.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn new<R, N>(
        envelope: ProofEnvelope,
        root_node_hash: NodeHash,
        range: OwnedKeyRange,
        records: R,
        nodes: N,
    ) -> Self
    where
        R: Into<Box<[Record]>>,
        N: Into<Box<[ProofNode]>>,
    {
        Self {
            envelope,
            root_node_hash,
            range,
            records: records.into(),
            nodes: nodes.into(),
        }
    }

    /// Returns the root and question.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn envelope(&self) -> ProofEnvelope
    {
        self.envelope
    }

    /// Returns the identity of the tree's root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node_hash(&self) -> NodeHash
    {
        self.root_node_hash
    }

    /// Returns the range the proof answers for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn range(&self) -> &OwnedKeyRange
    {
        &self.range
    }

    /// Returns the records the proof claims the range holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the records the proof claims, in the order it states them,
    ///   which verification checks is key order inside the committed range.
    /// - provides: the claimed answer a verifier decides on, kept separate from
    ///   the nodes that authenticate it.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn records(&self) -> &[Record]
    {
        self.records.as_ref()
    }

    /// Returns the carried nodes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the carried nodes in the order the proof states them: the
    ///   root node first, then the leaves the range selects, in key order.
    /// - provides: the material a verifier recomputes identities from, in the
    ///   order the layout check reads.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[ProofNode]
    {
        self.nodes.as_ref()
    }

    /// Checks the proof against a root the verifier already accepts and the
    /// query it was asked for.
    ///
    /// # Specification
    /// - requires: `expected_root` is a root the caller accepts on other
    ///   grounds; the proof is arbitrary and possibly hostile.
    /// - ensures: on success the returned records are exactly the records of
    ///   the tree named by `expected_root` that lie in the range — derived from
    ///   the carried bytes and required to equal what the proof claimed, so
    ///   both an omitted record and an invented one are refused.
    /// - provides: the range half of the crate's verification surface. The
    ///   postcondition stays prose: its first half names the tree
    ///   `expected_root` denotes, which this call never holds, and a clause for
    ///   the derived-against-claimed half alone would be weaker than the line
    ///   it replaces.
    /// - fails: [`RecordTreeError::InvalidProofShape`] when the envelope, the
    ///   query, the node layout or the derived records disagree;
    ///   [`RecordTreeError::HashMismatch`] when a carried node or the root
    ///   manifest does not recompute; plus every node-decoding failure.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — envelope, query, layout or
    /// record-set disagreement.
    /// [`RecordTreeError::HashMismatch`] — a node or the root manifest does not
    /// recompute.
    /// [`RecordTreeError::MalformedNode`] — a carried node is not canonical.
    /// [`RecordTreeError::UnsupportedVersion`] — a carried node names an
    /// unknown encoding version.
    /// [`RecordTreeError::DuplicateKeys`] — a carried leaf repeats a key.
    /// [`RecordTreeError::InvalidRange`] — the carried range is reversed.
    /// [`RecordTreeError::BudgetExceeded`] — the proof exceeds a decode budget.
    /// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
    ///
    /// # Adequacy
    /// - hypothesis: L1 evidence — the derived record set is the checkable
    ///   witness and is compared against the claim; the residue is the layout
    ///   and span arms, each named as its own witness, and the accepting cases
    ///   ride the property over generated trees.
    /// - witness: `tests::range::a_valid_proof_verifies`
    /// - witness: `tests::range::a_dropped_record_is_refused`
    /// - witness: `tests::range::an_invented_record_is_refused`
    /// - witness: `tests::range::a_short_leaf_run_is_refused`
    /// - witness: `tests::range::a_reordered_leaf_run_is_refused`
    #[inline]
    pub fn verify(
        &self,
        expected_root: &TreeRoot,
        expected_range: KeyRange<'_>,
    ) -> Result<Box<[Record]>, RecordTreeError>
    {
        ensure_envelope(&self.envelope, expected_root, ProofKind::Range)?;

        if self.range != OwnedKeyRange::from_range(expected_range) {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the proof answers for a different range".into(),
            });
        }

        let mut work = DecodeWork::new();
        let carried = decode_carried(self.nodes.as_ref(), &mut work)?;
        let root = open_root(&carried, expected_root, self.root_node_hash)?;

        let derived = match root {
            | RootNode::Leaf(leaf) => {
                ensure_node_count(
                    &carried,
                    CarriedCount::ROOT_ONLY,
                    "a range over a leaf root".into(),
                )?;
                ensure_leaf_total(leaf, expected_root.record_count())?;
                select_in_range(leaf.records(), expected_range)
            },
            | RootNode::Internal(internal) => {
                ensure_internal_total(internal, expected_root.record_count())?;
                let span = range_span(internal.children(), expected_range)?;
                let selected = internal
                    .children()
                    .get(usize::from(span.first()) ..= usize::from(span.last()))
                    .ok_or_else(|| RecordTreeError::InvalidProofShape {
                        context: "the selected leaf run is outside the root's children".into(),
                    })?;
                let expected_nodes = CarriedCount::from(selected.len()).next()?;
                ensure_node_count(
                    &carried,
                    expected_nodes,
                    "a range over an internal root".into(),
                )?;

                let mut records = Vec::<Record>::new();
                let mut previous: Option<OwnedRecordKey> = None;
                let mut position = CarriedIndex::SELECTED_LEAF;

                for child in selected {
                    let leaf = leaf_at(&carried, position, child)?;
                    position = position.next()?;

                    for record in leaf.records() {
                        if let Some(ref earlier) = previous
                            && earlier.as_ref() >= record.key().as_ref()
                        {
                            return Err(RecordTreeError::InvalidProofShape {
                                context: "the authenticated leaves are not globally sorted".into(),
                            });
                        }

                        previous = Some(OwnedRecordKey::from(record.key()));
                        records.push(record.clone());
                    }
                }

                select_in_range(records.as_slice(), expected_range)
            },
        };

        if derived.as_ref() != self.records.as_ref() {
            return Err(RecordTreeError::InvalidProofShape {
                context: "the claimed records are not the authenticated ones".into(),
            });
        }

        Ok(derived)
    }
}

/// One carried node after its identity was recomputed and its bytes decoded.
struct CarriedNode
{
    /// The recomputed identity, equal to the claimed one.
    hash: NodeHash,
    /// The decoded node.
    node: DecodedNode,
}

/// The tree's root node, opened.
enum RootNode<'carried>
{
    /// The tree is one leaf.
    Leaf(&'carried LeafNode),
    /// The tree has an internal root.
    Internal(&'carried InternalNode),
}

/// Whether absence evidence needs the leaf after the selected one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SuccessorLeaf
{
    /// The selected leaf carries no key above the absent one.
    Required,
    /// The selected leaf already carries a key above the absent one.
    NotRequired,
}

/// A position in a proof's carried node list.
///
/// The list is read positionally rather than searched, so a position is a
/// meaningful coordinate rather than an index into an unordered bag.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CarriedIndex(usize);

impl CarriedIndex
{
    /// The root node's position, which every proof layout puts first.
    pub const ROOT: Self = Self(0_usize);

    /// The selected leaf's position under every layout that carries one.
    pub const SELECTED_LEAF: Self = Self(1_usize);

    /// The successor leaf's position under the layout that carries one.
    pub const SUCCESSOR_LEAF: Self = Self(2_usize);

    /// Returns the position one later than this one.
    ///
    /// # Specification
    /// - requires: nothing; the position is a committed layout coordinate.
    /// - ensures: `|ret| ret.is_ok() == (usize::from(self) < usize::MAX)` — the
    ///   position one later when representable.
    /// - provides: the position advance a proof layout walks its carried slots.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] at the host ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the position was at the
    /// numeric ceiling.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(self) < usize::MAX))]
    pub fn next(self) -> Result<Self, RecordTreeError>
    {
        self.0
            .checked_add(1_usize)
            .map(Self)
            .ok_or_else(|| RecordTreeError::ArithmeticOverflow {
                context: "carried node position".into(),
            })
    }
}

impl From<usize> for CarriedIndex
{
    /// Reads a `usize` as a carried-node position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<CarriedIndex> for usize
{
    /// Reads the carried-node position back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: CarriedIndex) -> Self
    {
        position.0
    }
}

/// How many nodes a proof carries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CarriedCount(usize);

impl CarriedCount
{
    /// The count a leaf-rooted proof carries: the root and nothing else.
    pub const ROOT_ONLY: Self = Self(1_usize);

    /// The count a proof over an internal root carries when one leaf answers.
    pub const ROOT_AND_LEAF: Self = Self(2_usize);

    /// The count an absence proof carries when the next leaf is needed too.
    pub const ROOT_AND_TWO_LEAVES: Self = Self(3_usize);

    /// Returns the count one larger than this one.
    ///
    /// # Specification
    /// - requires: nothing; the count is a committed layout quantity.
    /// - ensures: `|ret| ret.is_ok() == (usize::from(self) < usize::MAX)` — the
    ///   count one larger when representable.
    /// - provides: the count a proof layout advances through its carried slots.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] at the host ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the count was at the numeric
    /// ceiling.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (usize::from(self) < usize::MAX))]
    pub fn next(self) -> Result<Self, RecordTreeError>
    {
        self.0
            .checked_add(1_usize)
            .map(Self)
            .ok_or_else(|| RecordTreeError::ArithmeticOverflow {
                context: "carried node count".into(),
            })
    }
}

impl From<usize> for CarriedCount
{
    /// Reads a `usize` as a carried-node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<CarriedCount> for usize
{
    /// Reads the carried-node count back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: CarriedCount) -> Self
    {
        count.0
    }
}

/// The contiguous run of children a range selects.
pub(crate) struct ChildSpan
{
    /// The first selected position.
    first: ChildIndex,
    /// The last selected position.
    last: ChildIndex,
}

impl ChildSpan
{
    /// Returns the first selected position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn first(&self) -> ChildIndex
    {
        self.first
    }

    /// Returns the last selected position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn last(&self) -> ChildIndex
    {
        self.last
    }
}

/// Refuses an envelope that does not match the verifier's own context.
///
/// # Specification
/// - requires: `envelope` is one the caller holds; `expected_root` and
///   `expected_kind` are the verifier's own.
/// - ensures: `|ret| ret.is_err() || (envelope.kind() == expected_kind &&
///   envelope.root() == *expected_root)` — on success the envelope's root and
///   kind match the verifier's.
/// - fails: [`RecordTreeError::IncompatibleParameters`] or
///   [`RecordTreeError::UnsupportedVersion`] when the envelope's parameters are
///   unsupported; [`RecordTreeError::InvalidProofShape`] when the root or the
///   kind differ.
/// - panics: none.
#[spec(ensures: |ret| ret.is_err()
    || (envelope.kind() == expected_kind && envelope.root() == *expected_root))]
fn ensure_envelope(
    envelope: &ProofEnvelope,
    expected_root: &TreeRoot,
    expected_kind: ProofKind,
) -> Result<(), RecordTreeError>
{
    expected_root.params().ensure_supported()?;

    if envelope.kind() != expected_kind {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the proof answers a different question".into(),
        });
    }

    if envelope.root() != *expected_root {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the proof names a different root".into(),
        });
    }

    Ok(())
}

/// Recomputes each carried node's identity and decodes it.
///
/// # Specification
/// - requires: `nodes` is the proof's carried material; `work` is the proof's
///   accounting accumulator.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|carried| carried.len() ==
///   nodes.len() && carried.iter().zip(nodes.iter()).all(|(entry, node)|
///   entry.hash == node.identity() && entry.hash == hash_node(node.bytes()) &&
///   inspect_node(node.bytes()).is_ok()))` — on success every carried node's
///   bytes hash to its claimed identity under the node domain, and each decodes
///   as a canonical node, one entry per input in order.
/// - fails: [`RecordTreeError::HashMismatch`] on a byte that does not hash to
///   the claimed identity; [`RecordTreeError::InvalidProofShape`] on an empty
///   list; every [`decode_node`] failure.
/// - panics: none.
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|carried| {
    carried.len() == nodes.len()
        && carried.iter().zip(nodes.iter()).all(|(entry, node)| {
            entry.hash == node.identity()
                && entry.hash == hash_node(node.bytes())
                && inspect_node(node.bytes()).is_ok()
        })
}))]
fn decode_carried(
    nodes: &[ProofNode],
    work: &mut DecodeWork,
) -> Result<Vec<CarriedNode>, RecordTreeError>
{
    if nodes.is_empty() {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the proof carries no nodes".into(),
        });
    }

    let mut carried = Vec::<CarriedNode>::with_capacity(nodes.len());

    for node in nodes {
        let actual = hash_node(node.bytes());

        if actual != node.identity() {
            return Err(RecordTreeError::HashMismatch {
                expected: node.identity(),
                actual,
            });
        }

        let decoded = decode_node(node.bytes(), work)?;
        carried.push(CarriedNode {
            hash: actual,
            node: decoded,
        });
    }

    Ok(carried)
}

/// Opens the first carried node as the tree's root, binding it to the manifest.
///
/// # Specification
/// - requires: `carried` is non-empty; `root_node_hash` is the manifest's.
/// - ensures: `|ret| ret.is_err() ||
///   (expected_root.ensure_binds(root_node_hash).is_ok() &&
///   carried.first().is_some_and(|first| first.hash == root_node_hash))` — on
///   success the opened root's node is the first carried node and the manifest
///   binds to that node's identity.
/// - fails: [`RecordTreeError::InvalidProofShape`] when the list is empty or
///   the first node is not the root; [`TreeRoot::ensure_binds`] failures.
/// - panics: none.
#[spec(ensures: |ret| ret.is_err()
    || (expected_root.ensure_binds(root_node_hash).is_ok()
        && carried.first().is_some_and(|first| first.hash == root_node_hash)))]
fn open_root<'carried>(
    carried: &'carried [CarriedNode],
    expected_root: &TreeRoot,
    root_node_hash: NodeHash,
) -> Result<RootNode<'carried>, RecordTreeError>
{
    expected_root.ensure_binds(root_node_hash)?;

    let first = carried
        .first()
        .ok_or_else(|| RecordTreeError::InvalidProofShape {
            context: "the proof carries no nodes".into(),
        })?;

    if first.hash != root_node_hash {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the first carried node is not the root node".into(),
        });
    }

    match first.node {
        | DecodedNode::Leaf(ref leaf) => Ok(RootNode::Leaf(leaf)),
        | DecodedNode::Internal(ref internal) => Ok(RootNode::Internal(internal)),
    }
}

/// Refuses a node list whose length is not the one this layout admits.
///
/// # Specification
/// - requires: nothing; both the list and the expected count are data.
/// - ensures: `|ret| ret.is_ok() == (CarriedCount::from(carried.len()) ==
///   expected)` — on success the list length equals `expected`.
/// - fails: [`RecordTreeError::InvalidProofShape`] naming `context` when they
///   differ.
/// - panics: none.
#[spec(ensures: |ret| ret.is_ok() == (CarriedCount::from(carried.len()) == expected))]
fn ensure_node_count(
    carried: &[CarriedNode],
    expected: CarriedCount,
    context: FailureContext,
) -> Result<(), RecordTreeError>
{
    if CarriedCount::from(carried.len()) == expected {
        return Ok(());
    }

    Err(RecordTreeError::InvalidProofShape { context })
}

/// Refuses a leaf root whose record count is not the root's.
///
/// # Specification
/// - requires: nothing; both sides are committed quantities.
/// - ensures: `|ret| ret.is_ok() == (leaf.record_count() == Ok(expected))` — on
///   success the leaf's count equals the root manifest's.
/// - fails: [`RecordTreeError::InvalidProofShape`] when they differ, plus the
///   count's [`RecordCount`] overflow check.
/// - panics: none.
#[spec(ensures: |ret| ret.is_ok() == (leaf.record_count() == Ok(expected)))]
fn ensure_leaf_total(
    leaf: &LeafNode,
    expected: RecordCount,
) -> Result<(), RecordTreeError>
{
    let count = leaf.record_count()?;

    if count != expected {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the leaf root's record count is not the root's".into(),
        });
    }

    Ok(())
}

/// Refuses an internal root whose record count is not the root's.
///
/// # Specification
/// - requires: nothing; both sides are committed quantities.
/// - ensures: `|ret| ret.is_ok() == (internal.record_count() == expected)` — on
///   success the internal node's total equals the root manifest's.
/// - fails: [`RecordTreeError::InvalidProofShape`] when they differ.
/// - panics: none.
#[spec(ensures: |ret| ret.is_ok() == (internal.record_count() == expected))]
fn ensure_internal_total(
    internal: &InternalNode,
    expected: RecordCount,
) -> Result<(), RecordTreeError>
{
    if internal.record_count() != expected {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the internal root's record count is not the root's".into(),
        });
    }

    Ok(())
}

/// Returns the child reference at a position.
///
/// # Specification
/// - requires: nothing; the position may be outside the root's children.
/// - ensures: `|ret| ret.as_ref().ok().copied() ==
///   internal.children().get(usize::from(position))` — on success the reference
///   is the root's child at `position`.
/// - fails: [`RecordTreeError::InvalidProofShape`] when the position is outside
///   the root's children.
/// - panics: none.
#[spec(ensures: |ret| ret.as_ref().ok().copied()
    == internal.children().get(usize::from(position)))]
fn child_at(
    internal: &InternalNode,
    position: ChildIndex,
) -> Result<&ChildRef, RecordTreeError>
{
    internal
        .children()
        .get(usize::from(position))
        .ok_or_else(|| RecordTreeError::InvalidProofShape {
            context: "the selected child position is outside the root's children".into(),
        })
}

/// Opens the carried node at a position as the leaf a child reference names.
///
/// The reference's three claims — separator, identity, record count — are all
/// checked against the leaf, because a verifier that checked only the identity
/// would accept a leaf reachable somewhere else in the tree.
///
/// # Specification
/// - requires: `position` indexes `carried`, and `child` is a reference of the
///   root the proof opens under.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|leaf|
///   carried.get(usize::from(position)).is_some_and(|node| node.hash ==
///   child.identity()) && leaf.first_key() == Some(child.first_key()) &&
///   leaf.record_count() == Ok(child.record_count()))` — on success the opened
///   leaf's identity, first key and record count all equal the reference's
///   claims.
/// - fails: [`RecordTreeError::InvalidProofShape`] when the leaf is not
///   carried, is empty, or any claim differs; [`DecodedNode::as_leaf`]
///   failures; the leaf's [`RecordCount`] overflow check.
/// - panics: none.
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|leaf| {
    carried
        .get(usize::from(position))
        .is_some_and(|node| node.hash == child.identity())
        && leaf.first_key() == Some(child.first_key())
        && leaf.record_count() == Ok(child.record_count())
}))]
fn leaf_at<'carried>(
    carried: &'carried [CarriedNode],
    position: CarriedIndex,
    child: &ChildRef,
) -> Result<&'carried LeafNode, RecordTreeError>
{
    let node =
        carried
            .get(usize::from(position))
            .ok_or_else(|| RecordTreeError::InvalidProofShape {
                context: "a required leaf is not carried".into(),
            })?;

    if node.hash != child.identity() {
        return Err(RecordTreeError::InvalidProofShape {
            context: "a carried leaf is not the child the root names here".into(),
        });
    }

    let leaf = node.node.as_leaf()?;
    let first_key = leaf
        .first_key()
        .ok_or_else(|| RecordTreeError::InvalidProofShape {
            context: "a carried leaf is empty and cannot be a child".into(),
        })?;

    if first_key != child.first_key() {
        return Err(RecordTreeError::InvalidProofShape {
            context: "a carried leaf's first key is not its separator".into(),
        });
    }

    let count = leaf.record_count()?;

    if count != child.record_count() {
        return Err(RecordTreeError::InvalidProofShape {
            context: "a carried leaf's record count is not the one the root names".into(),
        });
    }

    Ok(leaf)
}

/// Reports whether absence evidence needs the leaf after the selected one.
///
/// A prover and a verifier both call this, so the leaf a proof carries and the
/// leaf a verifier expects cannot be decided by two rules that drift apart.
///
/// # Specification
/// - requires: `records` is sorted by strictly increasing key.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|requirement| (*requirement
///   == SuccessorLeaf::NotRequired) == records.iter().any(|record| key <=
///   record.key()))` — reports `NotRequired` when a record at or past `key`
///   lies in this leaf, and `Required` when the key falls past every record.
/// - fails: [`RecordTreeError::InvalidProofShape`] when `key` is present.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::InvalidProofShape`] — the key is present.
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|requirement| {
    (*requirement == SuccessorLeaf::NotRequired) == records.iter().any(|record| key <= record.key())
}))]
pub(crate) fn needs_successor(
    records: &[Record],
    key: RecordKey<'_>,
) -> Result<SuccessorLeaf, RecordTreeError>
{
    for record in records {
        match record.key().cmp(&key) {
            | Ordering::Less => {},
            | Ordering::Equal => {
                return Err(RecordTreeError::InvalidProofShape {
                    context: "the key an absence proof answers for is present".into(),
                });
            },
            | Ordering::Greater => return Ok(SuccessorLeaf::NotRequired),
        }
    }

    Ok(SuccessorLeaf::Required)
}

/// Derives the neighbours bracketing an absent key from authenticated records.
///
/// A prover and a verifier both call this, so the evidence a proof claims and
/// the evidence a verifier derives cannot be computed by two rules that drift
/// apart — which matters, because the two are then compared for equality and a
/// drift would read as a forgery.
///
/// # Specification
/// - requires: `records` is sorted by strictly increasing key, and `next`
///   carries the successor leaf's records when the selected leaf is not the
///   last.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|evidence|
///   evidence.predecessor() == records.iter().rfind(|record| record.key() <
///   key) && evidence.successor() == records.iter().find(|record| key <
///   record.key()).or_else(|| next.and_then(<[Record]>::first)))` — on success
///   the predecessor is the greatest record below `key` and the successor the
///   least record above it.
/// - fails: [`RecordTreeError::InvalidProofShape`] when the key is present, the
///   successor leaf is empty, or the successor does not advance past the key.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::InvalidProofShape`] — the key is present, the successor
/// run is empty, or the successor run does not advance past the key.
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|evidence| {
    evidence.predecessor() == records.iter().rfind(|record| record.key() < key)
        && evidence.successor()
            == records
                .iter()
                .find(|record| key < record.key())
                .or_else(|| next.and_then(<[Record]>::first))
}))]
pub(crate) fn bracket(
    records: &[Record],
    next: Option<&[Record]>,
    key: RecordKey<'_>,
) -> Result<NonMembershipEvidence, RecordTreeError>
{
    let mut predecessor: Option<Record> = None;

    for record in records {
        match record.key().cmp(&key) {
            | Ordering::Less => predecessor = Some(record.clone()),
            | Ordering::Equal => {
                return Err(RecordTreeError::InvalidProofShape {
                    context: "the key an absence proof answers for is present".into(),
                });
            },
            | Ordering::Greater => {
                return Ok(NonMembershipEvidence::new(
                    predecessor,
                    Some(record.clone()),
                ));
            },
        }
    }

    let successor = match next {
        | Some(next_records) => {
            let record =
                next_records
                    .first()
                    .ok_or_else(|| RecordTreeError::InvalidProofShape {
                        context: "the successor leaf is empty".into(),
                    })?;

            if record.key() <= key {
                return Err(RecordTreeError::InvalidProofShape {
                    context: "the successor leaf does not advance past the key".into(),
                });
            }

            Some(record.clone())
        },
        | None => None,
    };

    Ok(NonMembershipEvidence::new(predecessor, successor))
}

/// Returns the contiguous run of children a range selects.
///
/// A prover and a verifier both call this, so the run a proof carries and the
/// run a verifier expects cannot be computed by two rules that drift apart.
///
/// # Specification
/// - requires: `children` is the root's list and `range` a committed interval.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|span| Some(span.first()) ==
///   range.start().key().map_or_else(|| children.first().map(|_first|
///   ChildIndex::ZERO), |key| select_child(children, key)) && Some(span.last())
///   == range.end().key().map_or_else(||
///   children.len().checked_sub(1).map(ChildIndex::from), |key|
///   select_child(children, key)) && span.first() <= span.last())` — on success
///   the run's first and last children are the range's selected leaves, in
///   order.
/// - fails: [`RecordTreeError::InvalidProofShape`] when the range selects no
///   first or last leaf, or its end precedes its start.
/// - panics: none.
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|span| {
    Some(span.first())
        == range.start().key().map_or_else(
            || children.first().map(|_first| ChildIndex::ZERO),
            |key| select_child(children, key),
        )
        && Some(span.last())
            == range.end().key().map_or_else(
                || children.len().checked_sub(1_usize).map(ChildIndex::from),
                |key| select_child(children, key),
            )
        && span.first() <= span.last()
}))]
pub(crate) fn range_span(
    children: &[ChildRef],
    range: KeyRange<'_>,
) -> Result<ChildSpan, RecordTreeError>
{
    let first = range
        .start()
        .key()
        .map_or_else(
            || children.first().map(|_first| ChildIndex::ZERO),
            |key| select_child(children, key),
        )
        .ok_or_else(|| RecordTreeError::InvalidProofShape {
            context: "the range selects no first leaf".into(),
        })?;
    let last = range
        .end()
        .key()
        .map_or_else(
            || children.len().checked_sub(1_usize).map(ChildIndex::from),
            |key| select_child(children, key),
        )
        .ok_or_else(|| RecordTreeError::InvalidProofShape {
            context: "the range selects no last leaf".into(),
        })?;

    if first > last {
        return Err(RecordTreeError::InvalidProofShape {
            context: "the selected leaf run is inverted".into(),
        });
    }

    Ok(ChildSpan { first, last })
}
