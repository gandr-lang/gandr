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
use crate::node::encode_internal;
use crate::node::encode_leaf;
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
    /// - requires: nothing; the root and question remain claims until verified.
    /// - ensures: the envelope carries exactly that root and that question.
    /// - provides: the root itself rather than a copy of its parameters, for
    ///   the reason the type's own prose states.
    /// - fails: never — a verifier decides whether it accepts the root.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 fixtures over 5-, 200- and 300-record trees observe
    ///   successful verification for each question and reject a foreign root or
    ///   kind. The predicate checks the question and all digest bytes;
    ///   verification also distinguishes changed manifest fields on these
    ///   finite fixtures.
    /// - witness: `tests::membership::a_valid_proof_verifies`
    /// - witness: `tests::membership::a_foreign_root_is_refused`
    /// - witness: `tests::membership::a_wrong_kind_is_refused`
    /// - witness: `tests::absence::a_valid_proof_verifies`
    /// - witness: `tests::range::a_valid_proof_verifies`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| {
        let question_matches = matches!((ret.kind, kind),
            (ProofKind::Membership, ProofKind::Membership)
                | (ProofKind::NonMembership, ProofKind::NonMembership)
                | (ProofKind::Range, ProofKind::Range));
        let actual_hash = ret.root.identity();
        let expected_hash = root.identity();
        let mut actual = actual_hash.byte_view().0.as_slice();
        let mut expected = expected_hash.byte_view().0.as_slice();
        let mut same = true;
        while let (Some((left, left_tail)), Some((right, right_tail))) =
            (actual.split_first(), expected.split_first()) {
            same = same && *left == *right;
            actual = left_tail;
            expected = right_tail;
        }
        question_matches && same
    })]
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
    /// The claimed node encoding, not yet validated.
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
    /// - panics: if the caller-supplied byte conversion panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 membership fixtures retain a carried identity while
    ///   changing a payload byte, and substitute an independently valid leaf.
    ///   Verification distinguishes byte authentication from the selected-child
    ///   relation; generic conversion effects are outside the hash-preservation
    ///   predicate.
    /// - witness: `tests::membership::a_valid_proof_verifies`
    /// - witness: `tests::membership::a_tampered_node_is_refused`
    /// - witness: `tests::membership::a_substituted_leaf_is_refused`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.hash == hash)]
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

    /// Returns the claimed node encoding without authenticating it.
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

/// The records claimed to bracket an absent key.
///
/// Verification authenticates the pair and requires the predecessor to lie
/// below the query and the successor above it. Construction alone makes no
/// such guarantee; a missing neighbour claims that side of the tree is empty.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NonMembershipEvidence
{
    /// The claimed greatest record below the absent key.
    predecessor: Option<Record>,
    /// The claimed least record above the absent key.
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
    /// - executable: none — both owned optional records move into the result;
    ///   no input value survives for a relational postcondition, and constant
    ///   instrumentation does not support pre-state captures.
    ///
    /// # Adequacy
    /// - hypothesis: L2 absence fixtures compare complete authenticated
    ///   neighbours for below, between and above queries, reject missing
    ///   claimed neighbours, and cover the empty tree. These observations
    ///   detect lost, swapped or changed evidence without narrowing the
    ///   constructor's unverified input domain.
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    /// - witness: `tests::absence::forged_evidence_is_refused`
    /// - witness: `tests::absence::an_empty_tree_proves_absence`
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

    /// Returns the claimed greatest record below the absent key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn predecessor(&self) -> Option<&Record>
    {
        self.predecessor.as_ref()
    }

    /// Returns the claimed least record above the absent key.
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

/// Unverified material claiming a key is present with a stated value.
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
    /// The claimed root and selected-leaf sequence, checked by verification.
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
    /// - panics: if a caller-supplied conversion panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 membership fixtures preserve the envelope and root-node
    ///   identity while forging carried content or layout; verification refuses
    ///   the altered claim. The predicate observes the two copied commitments;
    ///   generic conversions are consumed once, not replayed by the predicate.
    /// - witness: `tests::membership::a_valid_proof_verifies`
    /// - witness: `tests::membership::a_forged_binding_is_refused`
    /// - witness: `tests::membership::a_substituted_leaf_is_refused`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.envelope == envelope
        && ret.root_node_hash == root_node_hash)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 forged proofs built from the exposed sequence are
    ///   refused after a targeted content or layout change. Pointer-and-length
    ///   identity additionally detects replacing the view with a subset or
    ///   another buffer.
    /// - witness: `tests::membership::a_substituted_leaf_is_refused`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.nodes.as_ref())))]
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
    /// - provides: membership verification from carried bytes. The predicate
    ///   checks the caller's context and cryptographic commitments; the
    ///   witnesses distinguish a claimed binding from the authenticated leaf's
    ///   binding.
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
    /// - hypothesis: L3 leaf and internal-root fixtures over 5, 200 and 300
    ///   records observe successful authentication and refusal after changing
    ///   the root, kind, query, value, carried bytes, node count or selected
    ///   leaf. This finite mutation set is not a proof of every rejection arm.
    /// - witness: `tests::membership::a_valid_proof_verifies`
    /// - witness: `tests::membership::a_foreign_root_is_refused`
    /// - witness: `tests::membership::a_wrong_kind_is_refused`
    /// - witness: `tests::membership::a_different_query_is_refused`
    /// - witness: `tests::membership::a_wrong_value_is_refused`
    /// - witness: `tests::membership::a_tampered_node_is_refused`
    /// - witness: `tests::membership::an_extra_node_is_refused`
    /// - witness: `tests::membership::a_substituted_leaf_is_refused`
    /// - witness: `tests::membership::a_forged_binding_is_refused`
    /// - witness: `tests::membership::a_key_of_a_single_leaf_tree_proves`
    /// - witness: `tests::membership::every_key_of_a_tree_proves`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || (
        self.envelope.root() == *expected_root
            && self.envelope.kind() == ProofKind::Membership
            && self.key() == expected_key && self.value() == expected_value
            && expected_root.ensure_binds(self.root_node_hash).is_ok()
            && self.nodes.first().is_some_and(|node| node.identity() == self.root_node_hash)
            && self.nodes.iter().all(|node| hash_node(node.bytes()) == node.identity())
    ))]
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

/// Unverified material claiming a key is absent.
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
    /// The claimed root, selected leaf and optional successor sequence.
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
    /// - panics: if a caller-supplied conversion panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 absence fixtures preserve the envelope and root-node
    ///   identity while forging carried content or layout; verification refuses
    ///   the altered claim. The predicate observes the two copied commitments;
    ///   generic conversions are consumed once, not replayed by the predicate.
    /// - witness: `tests::absence::a_valid_proof_verifies`
    /// - witness: `tests::absence::forged_evidence_is_refused`
    /// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.envelope == envelope
        && ret.root_node_hash == root_node_hash)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 forged proofs built from the exposed sequence are
    ///   refused after a targeted content or layout change. Pointer-and-length
    ///   identity additionally detects replacing the view with a subset or
    ///   another buffer.
    /// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.nodes.as_ref())))]
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
    /// - provides: absence verification from carried bytes. The predicate
    ///   checks context, commitments, agreement with the claimed pair and
    ///   strict bracketing; witnesses compare neighbours with the source
    ///   records.
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
    /// - hypothesis: L2 empty, single-leaf and 200-/300-record fixtures observe
    ///   complete neighbours for below, between and above queries. Forged
    ///   evidence, a present query and missing or extra successor leaves
    ///   distinguish the tested authentication and layout decisions.
    /// - witness: `tests::absence::a_valid_proof_verifies`
    /// - witness: `tests::absence::a_present_key_is_refused_by_verification`
    /// - witness: `tests::absence::forged_evidence_is_refused`
    /// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
    /// - witness: `tests::absence::an_unnecessary_successor_leaf_is_refused`
    /// - witness: `tests::absence::absent_keys_everywhere_prove`
    /// - witness: `tests::absence::an_empty_tree_proves_absence`
    /// - witness: `tests::absence::a_key_absent_from_a_single_leaf_tree_proves`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|evidence| {
        self.envelope.root() == *expected_root
            && self.envelope.kind() == ProofKind::NonMembership
            && self.key() == expected_key && *evidence == self.evidence
            && evidence.predecessor().is_none_or(|record| record.key() < expected_key)
            && evidence.successor().is_none_or(|record| expected_key < record.key())
            && expected_root.ensure_binds(self.root_node_hash).is_ok()
            && self.nodes.first().is_some_and(|node| node.identity() == self.root_node_hash)
            && self.nodes.iter().all(|node| hash_node(node.bytes()) == node.identity())
    }))]
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

/// Unverified material claiming a range contains exactly the carried records.
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
    /// The claimed root and ordered leaf run, checked by verification.
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
    /// - panics: if a caller-supplied conversion panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 range fixtures preserve the envelope and root-node
    ///   identity while forging carried content or layout; verification refuses
    ///   the altered claim. The predicate observes the two copied commitments;
    ///   generic conversions are consumed once, not replayed by the predicate.
    /// - witness: `tests::range::a_valid_proof_verifies`
    /// - witness: `tests::range::a_dropped_record_is_refused`
    /// - witness: `tests::range::a_reordered_leaf_run_is_refused`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.envelope == envelope
        && ret.root_node_hash == root_node_hash)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 forged proofs built from the exposed sequence are
    ///   refused after a targeted content or layout change. Pointer-and-length
    ///   identity additionally detects replacing the view with a subset or
    ///   another buffer.
    /// - witness: `tests::range::a_dropped_record_is_refused`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.records.as_ref())))]
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
    /// - ensures: exactly the stored sequence, with neither filtering nor
    ///   reordering; construction does not guarantee root-first or leaf order.
    /// - provides: the claimed material whose positional layout verification
    ///   checks before accepting the answer.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 forged proofs built from the exposed sequence are
    ///   refused after a targeted content or layout change. Pointer-and-length
    ///   identity additionally detects replacing the view with a subset or
    ///   another buffer.
    /// - witness: `tests::range::a_reordered_leaf_run_is_refused`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.nodes.as_ref())))]
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
    /// - provides: range verification from carried bytes. The predicate checks
    ///   context, commitments, claimed-answer agreement, strict ordering and
    ///   containment; witnesses distinguish omitted and invented records.
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
    /// - hypothesis: L2 single-leaf and 300-record fixtures plus 32 generated
    ///   ranges (lower position below 300, span below 60, either upper
    ///   inclusion) compare the returned records with the in-memory answer.
    ///   Dropping or inventing records and shortening or permuting carried
    ///   leaves must fail.
    /// - witness: `tests::range::a_valid_proof_verifies`
    /// - witness: `tests::range::a_dropped_record_is_refused`
    /// - witness: `tests::range::an_invented_record_is_refused`
    /// - witness: `tests::range::a_short_leaf_run_is_refused`
    /// - witness: `tests::range::a_reordered_leaf_run_is_refused`
    /// - witness: `tests::range::generated_ranges_prove_and_verify`
    /// - witness: `tests::range::a_range_over_a_single_leaf_tree_proves`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|records| {
        self.envelope.root() == *expected_root
            && self.envelope.kind() == ProofKind::Range
            && self.range.as_range() == Ok(expected_range)
            && records.as_ref() == self.records.as_ref()
            && records.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key())
            && records.iter().all(|record| expected_range.contains(record.key())
                == crate::record::RangeContainment::Inside)
            && expected_root.ensure_binds(self.root_node_hash).is_ok()
            && self.nodes.first().is_some_and(|node| node.identity() == self.root_node_hash)
            && self.nodes.iter().all(|node| hash_node(node.bytes()) == node.identity())
    }))]
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
///
/// # Specification
/// - requires: construction follows successful identity and canonical-decoding
///   checks in `decode_carried`.
/// - ensures: the identity and decoded node describe the same carried encoding.
/// - provides: authenticated material, without assigning a proof-layout role.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 membership fixtures authenticate honest material and refuse
///   changed payloads. A leaf and an internal node have true refinements, then
///   false ones after their identities are exchanged. These distinguish
///   unchecked decoding and lost decoded-state correlation.
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::membership::a_tampered_node_is_refused`
/// - witness: `proof::tests::carried_refinements_bind_both_decoded_shapes_to_their_identities`
// Reuse the canonical encoders: the decoded value does not retain its bytes,
// and a second serializer in this predicate could drift from the wire format.
#[spec(maintains: match self.node {
    DecodedNode::Leaf(ref leaf) => {
        if !anodized::types::Spec::predicate(leaf) {
            return false;
        }
        let records = leaf.records().iter().map(Record::as_record_ref).collect::<Vec<_>>();
        encode_leaf(records.as_slice())
            .is_ok_and(|bytes| hash_node(bytes.as_borrowed()) == self.hash)
    },
    DecodedNode::Internal(ref internal) => {
        anodized::types::Spec::predicate(internal)
            && encode_internal(internal.children())
                .is_ok_and(|bytes| hash_node(bytes.as_borrowed()) == self.hash)
    },
})]
struct CarriedNode
{
    /// The recomputed identity, equal to the claimed one.
    hash: NodeHash,
    /// The decoded node.
    node: DecodedNode,
}

/// The tree's root node, opened.
///
/// # Specification
/// - requires: construction follows manifest binding and first-node identity
///   checks in `open_root`.
/// - ensures: the borrowed leaf or internal node is the authenticated root.
/// - provides: the root-shape distinction used by all three proof verifiers.
/// - panics: none.
/// - executable: none — the manifest and carried sequence are not stored in
///   this borrowed classification; `open_root` checks their binding relation.
///
/// # Adequacy
/// - hypothesis: L3 single-leaf and internal-root membership fixtures verify;
///   replacing the first carried node with a valid non-root leaf is refused.
///   This observes root identity rather than accepting any decodable node.
/// - witness: `tests::membership::a_key_of_a_single_leaf_tree_proves`
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::membership::a_root_node_swapped_for_a_leaf_is_refused`
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
    /// - ensures: the exact successor below the host ceiling, and overflow at
    ///   the ceiling; no wrapping or saturation is accepted.
    /// - provides: the position advance a proof layout walks its carried slots.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] at the host ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the position was at the
    /// numeric ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observations at zero, `usize::MAX - 1` and `usize::MAX`
    ///   compare exact positions and counts and the overflow variant, detecting
    ///   off-by-one arithmetic, wraparound and saturating substitutes.
    /// - witness: `proof::tests::carried_coordinates_stop_at_the_host_ceiling`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(next) => self.0.checked_add(1_usize) == Some(next.0),
        Err(RecordTreeError::ArithmeticOverflow { .. }) => self.0 == usize::MAX,
        Err(_) => false,
    })]
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
    /// - ensures: the exact successor below the host ceiling, and overflow at
    ///   the ceiling; no wrapping or saturation is accepted.
    /// - provides: the count a proof layout advances through its carried slots.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] at the host ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the count was at the numeric
    /// ceiling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observations at zero, `usize::MAX - 1` and `usize::MAX`
    ///   compare exact positions and counts and the overflow variant, detecting
    ///   off-by-one arithmetic, wraparound and saturating substitutes.
    /// - witness: `proof::tests::carried_coordinates_stop_at_the_host_ceiling`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(next) => self.0.checked_add(1_usize) == Some(next.0),
        Err(RecordTreeError::ArithmeticOverflow { .. }) => self.0 == usize::MAX,
        Err(_) => false,
    })]
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
///
/// # Specification
/// - requires: construction by `range_span` from selected boundary children.
/// - ensures: the first selected coordinate does not exceed the last; bounds
///   against the parent's child table are checked when the run is selected.
/// - provides: an inclusive, non-reversed run for positional proof material.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on three ordered children observes literal endpoints for
///   open, below-first, separator-aligned and above-last queries; equal
///   endpoints have true refinements and a privately reversed pair has a false
///   one. Empty input is refused. Off-by-one selection and inverted runs are
///   distinguished on this table, not on arbitrary malformed child tables.
/// - witness: `proof::tests::child_spans_preserve_order_at_range_boundaries`
#[spec(maintains: self.first <= self.last)]
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
/// - ensures: success exactly when the expected parameters are supported, the
///   question matches, and the complete claimed root equals the expected one.
/// - fails: [`RecordTreeError::IncompatibleParameters`] or
///   [`RecordTreeError::UnsupportedVersion`] when the envelope's parameters are
///   unsupported; [`RecordTreeError::InvalidProofShape`] when the root or the
///   kind differ.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 membership fixtures over 200 records admit the expected
///   envelope and reject a foreign root or wrong question. The biconditional
///   additionally observes parameter admission, without claiming a witness for
///   every future parameter variant.
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::membership::a_foreign_root_is_refused`
/// - witness: `tests::membership::a_wrong_kind_is_refused`
#[spec(ensures: |ret| ret.is_ok() == (expected_root.params().ensure_supported().is_ok()
    && envelope.kind() == expected_kind && envelope.root() == *expected_root))]
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
/// - ensures: on success every carried encoding hashes to its claimed identity
///   and decodes canonically, one entry per input in order. Each decoded entry
///   also satisfies its refinement: canonical re-encoding recomputes the
///   retained identity.
/// - fails: [`RecordTreeError::HashMismatch`] on a byte that does not hash to
///   the claimed identity; [`RecordTreeError::InvalidProofShape`] on an empty
///   list; every [`decode_node`] failure.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 valid membership and range material authenticates in order;
///   a single changed payload byte produces a hash mismatch. The 4096-node
///   proof ceiling is admitted and its successor refused. Exchanging the
///   identities of decoded leaf and internal entries makes both refinements
///   false, distinguishing lost decoded-state correlation. These observations
///   do not measure allocation or prove every malformed encoding is rejected.
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::membership::a_tampered_node_is_refused`
/// - witness: `tests::range::the_node_budget_ceiling_proves`
/// - witness: `tests::range::a_span_past_the_node_budget_is_refused`
/// - witness: `proof::tests::carried_refinements_bind_both_decoded_shapes_to_their_identities`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|carried| {
    carried.len() == nodes.len()
        && carried.iter().zip(nodes.iter()).all(|(entry, node)| {
            entry.hash == node.identity()
                && entry.hash == hash_node(node.bytes())
                && inspect_node(node.bytes()).is_ok()
                && anodized::types::Spec::predicate(entry)
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
/// - requires: nothing; the sequence and root-node identity are claims.
/// - ensures: `|ret| ret.is_err() ||
///   (expected_root.ensure_binds(root_node_hash).is_ok() &&
///   carried.first().is_some_and(|first| first.hash == root_node_hash))` — on
///   success the opened root's node is the first carried node and the manifest
///   binds to that node's identity.
/// - fails: [`RecordTreeError::InvalidProofShape`] when the list is empty or
///   the first node is not the root; [`TreeRoot::ensure_binds`] failures.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 single-leaf and internal-root membership fixtures
///   authenticate the first node; replacing that node with a valid leaf is
///   refused. The pointer relation distinguishes returning some other carried
///   node.
/// - witness: `tests::membership::a_key_of_a_single_leaf_tree_proves`
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::membership::a_root_node_swapped_for_a_leaf_is_refused`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|root| {
    expected_root.ensure_binds(root_node_hash).is_ok()
        && carried.first().is_some_and(|first| first.hash == root_node_hash
            && match *root {
                RootNode::Leaf(leaf) => matches!(first.node,
                    DecodedNode::Leaf(ref actual) if core::ptr::eq(core::ptr::from_ref(leaf), core::ptr::from_ref(actual))),
                RootNode::Internal(internal) => matches!(first.node,
                    DecodedNode::Internal(ref actual) if core::ptr::eq(core::ptr::from_ref(internal), core::ptr::from_ref(actual))),
            })
}))]
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
///
/// # Adequacy
/// - hypothesis: L3 membership, absence and range fixtures admit their exact
///   layouts and reject an extra membership node, missing or unnecessary
///   successor leaf, and shortened range. Counts outside these fixtures are
///   covered by the equality predicate, not an exhaustive enumeration.
/// - witness: `tests::membership::an_extra_node_is_refused`
/// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
/// - witness: `tests::absence::an_unnecessary_successor_leaf_is_refused`
/// - witness: `tests::range::a_short_leaf_run_is_refused`
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
///
/// # Adequacy
/// - hypothesis: L3 single-leaf membership fixtures admit the sealed record
///   total; a separately sealed wrong total is refused by verification. This
///   distinguishes count omission without forging a digest.
/// - witness: `tests::membership::a_key_of_a_single_leaf_tree_proves`
/// - witness: `tests::membership::a_wrong_manifest_count_is_refused`
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
///
/// # Adequacy
/// - hypothesis: L3 internal-root membership fixtures admit the sealed record
///   total and refuse a separately sealed wrong total. The count check is
///   tested independently of an envelope or digest mismatch.
/// - witness: `tests::membership::a_valid_proof_verifies`
/// - witness: `tests::membership::a_wrong_manifest_count_is_refused`
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
///
/// # Adequacy
/// - hypothesis: L3 membership verification for every key in the fixed
///   300-record corpus observes the selected child; substituting another valid
///   leaf is refused. The predicate relates arbitrary positions to slice
///   lookup, beyond the positions these witnesses traverse.
/// - witness: `tests::membership::every_key_of_a_tree_proves`
/// - witness: `tests::membership::a_substituted_leaf_is_refused`
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
/// - requires: nothing; missing positions and mismatched claims are refused.
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
///
/// # Adequacy
/// - hypothesis: L3 membership for all 300 keys and an absence query requiring
///   a successor leaf observe successful child authentication. A different
///   valid leaf in the selected slot is refused. These fixtures distinguish
///   identity substitution, not every separator or count forgery.
/// - witness: `tests::membership::every_key_of_a_tree_proves`
/// - witness: `tests::absence::a_missing_successor_leaf_is_refused`
/// - witness: `tests::membership::a_substituted_leaf_is_refused`
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
///
/// # Adequacy
/// - hypothesis: L3 ordered zero- and two-record fixtures compare requirement
///   states below, between and above keys, and refuse present keys. Omitting
///   the equality branch or reversing the successor decision is observable.
/// - witness: `proof::tests::bracketing_handles_presence_and_successor_boundaries`
#[spec(
    requires: records.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key()),
    ensures: |ret| match ret {
        Ok(requirement) => !records.iter().any(|record| record.key() == key)
            && (requirement == SuccessorLeaf::NotRequired)
                == records.iter().any(|record| key < record.key()),
        Err(RecordTreeError::InvalidProofShape { .. }) => records.iter().any(|record| record.key() == key),
        Err(_) => false,
    },
)]
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
/// - requires: `records` and any supplied successor run are strictly
///   key-ordered. A supplied run may be empty or fail to advance; these
///   candidate errors are refused when its first record is needed.
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
///
/// # Adequacy
/// - hypothesis: L3 ordered empty and two-record fixtures observe complete
///   neighbours below, between and above the run; present queries and empty or
///   non-advancing successor runs are refused. A separate successor run
///   distinguishes losing the cross-leaf neighbour.
/// - witness: `proof::tests::bracketing_handles_presence_and_successor_boundaries`
/// - witness: `tests::absence::absent_keys_everywhere_prove`
#[spec(
    requires: records.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key())
        && next.is_none_or(|run| run.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key())),
    ensures: |ret| ret.as_ref().ok().is_none_or(|evidence| {
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
///
/// # Adequacy
/// - hypothesis: L2 unbounded, empty and generated bounded ranges over a fixed
///   300-record corpus observe the selected run through verified records. A
///   three-child table also distinguishes literal boundary coordinates, equal
///   versus reversed spans and empty-table refusal. Shortened and reordered
///   runs fail verification; these fixtures do not enumerate arbitrary
///   malformed child tables.
/// - witness: `tests::range::the_unbounded_range_proves`
/// - witness: `tests::range::an_empty_range_proves`
/// - witness: `tests::range::generated_ranges_prove_and_verify`
/// - witness: `tests::range::a_short_leaf_run_is_refused`
/// - witness: `tests::range::a_reordered_leaf_run_is_refused`
/// - witness: `proof::tests::child_spans_preserve_order_at_range_boundaries`
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
        && anodized::types::Spec::predicate(span)
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

#[cfg(test)]
mod tests
{
    use super::CarriedCount;
    use super::CarriedIndex;
    use super::ChildSpan;
    use super::ProofNode;
    use super::SuccessorLeaf;
    use super::bracket;
    use super::decode_carried;
    use super::needs_successor;
    use super::range_span;
    use crate::ChildIndex;
    use crate::ChildRef;
    use crate::DecodeWork;
    use crate::KeyBound;
    use crate::KeyRange;
    use crate::Record;
    use crate::RecordCount;
    use crate::RecordKey;
    use crate::RecordRef;
    use crate::RecordTreeError;
    use crate::encode_internal;
    use crate::encode_leaf;
    use crate::hash_node;

    #[test]
    fn carried_coordinates_stop_at_the_host_ceiling()
    {
        for position in [0_usize, usize::MAX - 1_usize] {
            assert_eq!(
                CarriedIndex::from(position).next(),
                Ok(CarriedIndex::from(position + 1_usize))
            );
            assert_eq!(
                CarriedCount::from(position).next(),
                Ok(CarriedCount::from(position + 1_usize))
            );
        }
        assert!(matches!(
            CarriedIndex::from(usize::MAX).next(),
            Err(RecordTreeError::ArithmeticOverflow { .. })
        ));
        assert!(matches!(
            CarriedCount::from(usize::MAX).next(),
            Err(RecordTreeError::ArithmeticOverflow { .. })
        ));
    }

    #[test]
    fn bracketing_handles_presence_and_successor_boundaries()
    {
        let records = [Record::new(b"a", b"1"), Record::new(b"c", b"3")];
        for (key, required, predecessor, successor) in [
            (b"0", SuccessorLeaf::NotRequired, None, Some(&records[0])),
            (
                b"b",
                SuccessorLeaf::NotRequired,
                Some(&records[0]),
                Some(&records[1]),
            ),
            (b"z", SuccessorLeaf::Required, Some(&records[1]), None),
        ] {
            let query = RecordKey::from(key);
            assert_eq!(needs_successor(&records, query), Ok(required));
            let evidence = bracket(&records, None, query).expect("the query is absent");
            assert_eq!(evidence.predecessor(), predecessor);
            assert_eq!(evidence.successor(), successor);
        }
        for present in &records {
            assert!(matches!(
                needs_successor(&records, present.key()),
                Err(RecordTreeError::InvalidProofShape { .. })
            ));
            assert!(matches!(
                bracket(&records, None, present.key()),
                Err(RecordTreeError::InvalidProofShape { .. })
            ));
        }

        let query = RecordKey::from(b"z");
        assert_eq!(needs_successor(&[], query), Ok(SuccessorLeaf::Required));
        let empty = bracket(&[], None, query).expect("the empty run contains no key");
        assert_eq!(empty.predecessor(), None);
        assert_eq!(empty.successor(), None);
        for next in [&[][..], records.as_slice()] {
            assert!(matches!(
                bracket(&records, Some(next), query),
                Err(RecordTreeError::InvalidProofShape { .. })
            ));
        }
        let next = [Record::new(b"zz", b"9")];
        let evidence = bracket(&records, Some(&next), query).expect("the successor advances");
        assert_eq!(evidence.predecessor(), records.last());
        assert_eq!(evidence.successor(), next.first());

        let inside = bracket(&records, Some(&[]), RecordKey::from(b"b"))
            .expect("an unused successor run need not supply a record");
        assert_eq!(inside.predecessor(), records.first());
        assert_eq!(inside.successor(), records.last());
    }

    #[test]
    fn carried_refinements_bind_both_decoded_shapes_to_their_identities()
    {
        let leaf = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let leaf_hash = hash_node(leaf.as_borrowed());
        let internal = encode_internal(&[ChildRef::new(b"a", leaf_hash, RecordCount::from(1_u64))])
            .expect("the internal node encodes");
        let internal_hash = hash_node(internal.as_borrowed());
        let nodes = [
            ProofNode::new(internal_hash, internal),
            ProofNode::new(leaf_hash, leaf),
        ];
        let mut carried = decode_carried(&nodes, &mut DecodeWork::default())
            .expect("both identities authenticate their canonical nodes");
        let (first, rest) = carried
            .split_first_mut()
            .expect("the internal entry is present");
        let second = rest.first_mut().expect("the leaf entry is present");
        assert!(anodized::types::Spec::predicate(first));
        assert!(anodized::types::Spec::predicate(second));
        core::mem::swap(&mut first.hash, &mut second.hash);
        assert!(!anodized::types::Spec::predicate(first));
        assert!(!anodized::types::Spec::predicate(second));
    }

    #[test]
    fn child_spans_preserve_order_at_range_boundaries()
    {
        let children = [
            RecordRef::new(b"a", b"1"),
            RecordRef::new(b"m", b"2"),
            RecordRef::new(b"z", b"3"),
        ]
        .map(|record| {
            let bytes = encode_leaf(core::slice::from_ref(&record)).expect("one record encodes");
            ChildRef::new(
                record.key(),
                hash_node(bytes.as_borrowed()),
                RecordCount::from(1_u64),
            )
        });
        for (start, end, expected) in [
            (KeyBound::Unbounded, KeyBound::Unbounded, (0_usize, 2_usize)),
            (
                KeyBound::included(b""),
                KeyBound::excluded(b"a"),
                (0_usize, 0_usize),
            ),
            (
                KeyBound::included(b"m"),
                KeyBound::excluded(b"z"),
                (1_usize, 2_usize),
            ),
            (
                KeyBound::included(b"zz"),
                KeyBound::Unbounded,
                (2_usize, 2_usize),
            ),
        ] {
            let range = KeyRange::new(start, end).expect("the query is ordered");
            let span = range_span(&children, range).expect("the boundary children exist");
            assert_eq!(
                (usize::from(span.first()), usize::from(span.last())),
                expected
            );
            assert!(anodized::types::Spec::predicate(&span));
        }
        assert!(!anodized::types::Spec::predicate(&ChildSpan {
            first: ChildIndex::from(1_usize),
            last: ChildIndex::ZERO,
        }));
        assert!(matches!(
            range_span(&[], KeyRange::all()),
            Err(RecordTreeError::InvalidProofShape { .. })
        ));
    }
}
