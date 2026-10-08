//! The canonical node encoding: how a leaf and an internal node become bytes,
//! how those bytes become a node again, and what a decoder refuses.
//!
//! # The two node shapes
//!
//! A **leaf** carries a run of records in key order. An **internal** node
//! carries child references, each a separator key (the first key reachable
//! through that child), the child's identity, and the child's record count.
//! Both encodings open with the node domain tag and the encoding version, so
//! node bytes are self-describing and cannot be read as material of another
//! domain.
//!
//! # What decoding checks
//!
//! Decoding is fail-closed and checks more than framing. A leaf's records must
//! be strictly increasing; an internal node's separators must be strictly
//! increasing, its children must each carry at least one record, and its
//! children's counts must sum to the count in its header. Trailing bytes are a
//! refusal, so one encoding admits one byte string. Every count is checked
//! against the bytes that remain before it decides an allocation, and against
//! the pinned per-structure ceilings.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;

use crate::bytes::EncodedNode;
use crate::bytes::NODE_HASH_LEN;
use crate::bytes::NodeHash;
use crate::bytes::OwnedEncodedNode;
use crate::bytes::OwnedRecordKey;
use crate::bytes::OwnedRecordValue;
use crate::bytes::RecordKey;
use crate::error::RecordTreeError;
use crate::error::WireVersion;
use crate::params::EncodingVersion;
use crate::record::Record;
use crate::record::RecordCount;
use crate::record::RecordIndex;
use crate::record::RecordRef;
use crate::wire::ChildCount;
use crate::wire::Cursor;
use crate::wire::DecodeCompletion;
use crate::wire::DecodeWork;
use crate::wire::Domain;
use crate::wire::LEAST_CHILD_BYTES;
use crate::wire::LEAST_RECORD_BYTES;
use crate::wire::MAX_LEAF_RECORDS;
use crate::wire::MAX_NODE_BYTES;
use crate::wire::MAX_NODE_CHILDREN;
use crate::wire::WireBuffer;
use crate::wire::WireBytes;
use crate::wire::WireLong;
use crate::wire::WireTag;
use crate::wire::WireWord;
use crate::wire::digest;

/// The discriminator of a leaf node.
const TAG_LEAF: WireTag = WireTag(0x00_u8);

/// The discriminator of an internal node.
const TAG_INTERNAL: WireTag = WireTag(0x01_u8);

/// Which shape a node has.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeKind
{
    /// The node carries records.
    Leaf,
    /// The node carries child references.
    Internal,
}

/// A position among an internal node's children.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildIndex(usize);

impl ChildIndex
{
    /// The first position.
    pub const ZERO: Self = Self(0_usize);

    /// Returns the position one later than this one.
    ///
    /// # Specification
    /// - requires: nothing; the position counts children already seen.
    /// - ensures: `|ret| ret.is_ok() == (usize::from(self) < usize::MAX)` — the
    ///   position one later when representable.
    /// - provides: the position advance an internal node's child walk takes.
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
                context: "child position".into(),
            })
    }
}

impl From<usize> for ChildIndex
{
    /// Reads a `usize` as a child position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ChildIndex> for usize
{
    /// Reads the child position back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ChildIndex) -> Self
    {
        index.0
    }
}

/// One child reference inside an internal node.
///
/// The reference is the whole of what an internal node says about a child: its
/// first key, its identity, and how many records it stands for. A verifier
/// checks all three against the decoded child rather than trusting any of them.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ChildRef
{
    /// The first key reachable through this child.
    first_key: OwnedRecordKey,
    /// The child's identity.
    hash: NodeHash,
    /// How many records the child stands for.
    record_count: RecordCount,
}

impl ChildRef
{
    /// Builds a child reference.
    ///
    /// # Specification
    /// - requires: `first_key` is the least key reachable through the child,
    ///   `hash` is that child's encoding identity, and `record_count` is how
    ///   many records it stands for; none of the three is checkable here, and a
    ///   decoder re-establishes all three against the child itself.
    /// - ensures: the reference carries exactly the three parts offered.
    /// - provides: the whole of what an internal node says about a child, so a
    ///   verifier checks a claim rather than reconstructing one.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn new<K>(
        first_key: K,
        hash: NodeHash,
        record_count: RecordCount,
    ) -> Self
    where
        K: Into<OwnedRecordKey>,
    {
        Self {
            first_key: first_key.into(),
            hash,
            record_count,
        }
    }

    /// Returns the first key reachable through this child.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn first_key(&self) -> RecordKey<'_>
    {
        self.first_key.as_borrowed()
    }

    /// Returns the child's identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn identity(&self) -> NodeHash
    {
        self.hash
    }

    /// Returns how many records the child stands for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn record_count(&self) -> RecordCount
    {
        self.record_count
    }
}

/// A decoded leaf.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeafNode
{
    /// The leaf's records, strictly increasing in key order.
    records: Box<[Record]>,
}

impl LeafNode
{
    /// Returns the leaf's records.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the records in strictly increasing key order, which the
    ///   decoder refused to admit any other way.
    /// - provides: the payload a leaf proof and a record lookup both read, in
    ///   the order the identity was folded over.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn records(&self) -> &[Record]
    {
        self.records.as_ref()
    }

    /// Returns the leaf's first key, when the leaf is non-empty.
    ///
    /// # Specification
    /// - requires: nothing — an empty leaf is admissible input.
    /// - ensures: the least key the leaf holds, which is its first under the
    ///   key order the decoder established.
    /// - provides: the separator an internal node claims for this child.
    /// - fails: yields nothing for an empty leaf, which only a record-less
    ///   tree's single leaf is.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn first_key(&self) -> Option<RecordKey<'_>>
    {
        self.records.first().map(Record::key)
    }

    /// Returns how many records the leaf carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.as_ref().ok().map(|count| u64::from(*count)) ==
    ///   u64::try_from(self.records.len()).ok()` — the record count of a
    ///   decoded leaf when it fits the wire width, so the decoder's check of a
    ///   declared count has the material to compare against.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] on a `usize` length
    ///   that exceeds the `u64` wire width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the count exceeds the wire
    /// width.
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().map(|count| u64::from(*count))
        == u64::try_from(self.records.len()).ok())]
    pub fn record_count(&self) -> Result<RecordCount, RecordTreeError>
    {
        RecordCount::of_slice(self.records.as_ref())
    }
}

/// A decoded internal node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InternalNode
{
    /// The total record count the header claims, checked against the children.
    record_count: RecordCount,
    /// The children, strictly increasing in separator order.
    children: Box<[ChildRef]>,
}

impl InternalNode
{
    /// Returns the total record count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn record_count(&self) -> RecordCount
    {
        self.record_count
    }

    /// Returns the children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the children in strictly increasing separator order, which
    ///   the decoder refused to admit any other way.
    /// - provides: the child list a descent and a proof layout both walk.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn children(&self) -> &[ChildRef]
    {
        self.children.as_ref()
    }

    /// Returns the position of the child a key would be found through.
    ///
    /// # Specification
    /// - requires: nothing — a key no child covers is admissible input.
    /// - ensures: the position `select_child` names for `key` against this
    ///   node's children: the child in which the key's presence or absence is
    ///   decidable, never one that could not hold it.
    /// - provides: the descent step from an internal node, without exposing the
    ///   child list's ordering rule to the caller.
    /// - fails: yields nothing when the node has no child, which the decoder
    ///   admits for no internal node.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn child_for_key(
        &self,
        key: RecordKey<'_>,
    ) -> Option<ChildIndex>
    {
        select_child(self.children.as_ref(), key)
    }
}

/// Returns the position of the child a key would be found through.
///
/// # Specification
/// - requires: `children` is strictly increasing in separator order.
/// - ensures: the answer is the last position whose separator does not sort
///   after `key`, or the first position when every separator sorts after it —
///   the child in which the key's presence or absence is decidable, never a
///   child that could not hold it. An empty child list has no answer.
/// - provides: the descent step shared by lookup, by proof construction and by
///   proof verification, so a prover and a verifier cannot disagree about which
///   child a query selects.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is the separator comparison and
///   the fall-through, a finite class enumerated exhaustively: below the first
///   separator, exactly on a separator, between two, above the last, and the
///   empty list.
/// - witness: `node::tests::child_selection_picks_the_last_separator_at_or_below_the_key`
/// - witness: `node::tests::child_selection_has_no_answer_without_children`
// The predicate covers the two structural halves — an answer exactly when there
// is a child to answer with, and an answer that indexes the list — which is
// what "never a child that could not hold it" rests on. Which child is the
// right one is the separator comparison, and restating it here would be the
// body again.
#[must_use]
#[spec(ensures: |ret| ret.is_some() != children.is_empty()
    && ret.is_none_or(|index| usize::from(index) < children.len()))]
pub fn select_child(
    children: &[ChildRef],
    key: RecordKey<'_>,
) -> Option<ChildIndex>
{
    let mut selected: Option<ChildIndex> = None;

    for (position, child) in children.iter().enumerate() {
        if child.first_key() <= key {
            selected = Some(ChildIndex::from(position));
        }
        else {
            return selected.or(Some(ChildIndex::ZERO));
        }
    }

    selected.map_or_else(|| children.first().map(|_| ChildIndex::ZERO), Some)
}

/// A decoded node of either shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DecodedNode
{
    /// The node carries records.
    Leaf(LeafNode),
    /// The node carries child references.
    Internal(InternalNode),
}

impl DecodedNode
{
    /// Returns the node's shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> NodeKind
    {
        match *self {
            | Self::Leaf(_) => NodeKind::Leaf,
            | Self::Internal(_) => NodeKind::Internal,
        }
    }

    /// Returns the leaf, or refuses a node that is not one.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: `|ret| ret.is_ok() == matches!(*self, Self::Leaf(_))` — a
    ///   leaf answers and an internal node refuses. That the answer is this
    ///   node's own leaf is structural: the variant carries one field, and a
    ///   value comparison would walk every record on every call.
    /// - provides: the checked view of the leaf side of a decoded node.
    /// - fails: [`RecordTreeError::InvalidProofShape`] — the node is internal.
    /// - panics: none.
    /// # Errors
    /// [`RecordTreeError::InvalidProofShape`] — the node is internal where a
    /// leaf was required.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == matches!(*self, Self::Leaf(_)))]
    pub fn as_leaf(&self) -> Result<&LeafNode, RecordTreeError>
    {
        match *self {
            | Self::Leaf(ref leaf) => Ok(leaf),
            | Self::Internal(_) => Err(RecordTreeError::InvalidProofShape {
                context: "a leaf was required and the node is internal".into(),
            }),
        }
    }
}

/// What a node encoding declares, read without materializing its contents.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeLayout
{
    /// The node's shape.
    kind: NodeKind,
    /// The record count the header declares.
    record_count: RecordCount,
    /// The number of children, for an internal node.
    children: Option<ChildCount>,
}

impl NodeLayout
{
    /// Returns the node's shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> NodeKind
    {
        self.kind
    }

    /// Returns the record count the header declares.
    ///
    /// # Specification
    /// - requires: nothing; the count is the header's own claim.
    /// - ensures: the declared count, uninterpreted — a layout is what the
    ///   header said, not what the payload proved.
    /// - provides: the declared total a decoder checks the payload against.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn record_count(&self) -> RecordCount
    {
        self.record_count
    }

    /// Returns the number of children, for an internal node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the declared child count for an internal layout, and nothing
    ///   for a leaf one.
    /// - provides: the shape-dependent half of a header, as an absence rather
    ///   than a zero, so a leaf cannot read as an internal node with no
    ///   children.
    /// - fails: yields nothing for a leaf, which carries records rather than
    ///   children.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn children(&self) -> Option<ChildCount>
    {
        self.children
    }
}

/// Encoded node bytes offered under a claimed identity.
///
/// The pairing is the store boundary's unit: bytes are never handed across it
/// without the identity they are claimed to have, so the recomputation check
/// has something to check against.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct StoredNode<'node>
{
    /// The claimed identity.
    hash: NodeHash,
    /// The bytes.
    bytes: EncodedNode<'node>,
}

impl<'node> StoredNode<'node>
{
    /// Pairs bytes with the identity they are claimed to have.
    ///
    /// # Specification
    /// - requires: nothing — bytes that do not hash to `hash` are admissible
    ///   input, and are exactly what the store check refuses.
    /// - ensures: the pair carries exactly the identity and the bytes offered,
    ///   unchecked.
    /// - provides: the store boundary's unit, so bytes never cross it without
    ///   the identity a recomputation can check them against.
    /// - fails: never — the pairing is checked where it is used.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new(
        hash: NodeHash,
        bytes: EncodedNode<'node>,
    ) -> Self
    {
        Self { hash, bytes }
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

    /// Returns the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bytes(&self) -> EncodedNode<'node>
    {
        self.bytes
    }
}

/// Computes the identity of encoded node bytes.
///
/// # Specification
/// - requires: nothing; the bytes may be arbitrary.
/// - ensures: equal bytes give equal identities, and the identity is taken
///   under the node domain, so it never coincides with the identity the same
///   bytes would have as material of another domain.
/// - provides: the tree's node identity, and the only way one is produced. The
///   postcondition stays prose: both halves relate two calls — one pair of byte
///   strings, one pair of domains — and one call carries one pair.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the identity of one pinned encoding is a
///   golden, and the domain claim is separated by the same bytes hashed under a
///   second domain.
/// - witness: `node::tests::the_node_identity_is_pinned`
/// - witness: `wire::tests::digests_of_one_body_differ_across_domains`
#[inline]
#[must_use]
pub fn hash_node(bytes: EncodedNode<'_>) -> NodeHash
{
    digest(Domain::Node, WireBytes::from(bytes.as_ref()))
}

/// Encodes a run of records as a leaf.
///
/// # Specification
/// - requires: `records` is strictly increasing in key order — the caller's
///   obligation, re-established by the decoder rather than assumed by it.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|node|
///   decode_node(node.as_borrowed(), &mut
///   DecodeWork::new()).is_ok_and(|decoded| match decoded {
///   DecodedNode::Leaf(leaf) =>
///   leaf.records().iter().map(Record::as_record_ref).eq(records.iter().
///   copied()), DecodedNode::Internal(_) => false }))` — the encoding decodes
///   back to exactly these records.
/// - provides: the leaf half of the canonical encoding.
/// - fails: [`RecordTreeError::BudgetExceeded`] when the run exceeds the leaf
///   record budget or the encoded leaf exceeds the node byte budget;
///   [`RecordTreeError::ArithmeticOverflow`] when a count or a field length
///   exceeds the wire width.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::BudgetExceeded`] — the run exceeds the leaf record
/// budget or the encoded leaf exceeds the node byte budget.
/// [`RecordTreeError::ArithmeticOverflow`] — a count or field length exceeds
/// the wire width.
///
/// # Adequacy
/// - hypothesis: L2 agreement — a round-trip property over generated corpora
///   asserts decode after encode is the identity on records, with an empty leaf
///   and a leaf of empty-byte fields as the named boundary inputs.
/// - witness: `node::tests::leaves_round_trip`
/// - witness: `node::tests::an_empty_leaf_round_trips`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|node| {
    decode_node(node.as_borrowed(), &mut DecodeWork::new()).is_ok_and(|decoded| match decoded {
        | DecodedNode::Leaf(leaf) => leaf
            .records()
            .iter()
            .map(Record::as_record_ref)
            .eq(records.iter().copied()),
        | DecodedNode::Internal(_) => false,
    })
}))]
pub fn encode_leaf(records: &[RecordRef<'_>]) -> Result<OwnedEncodedNode, RecordTreeError>
{
    let count = RecordCount::of_slice(records)?;

    if count > MAX_LEAF_RECORDS {
        return Err(RecordTreeError::BudgetExceeded {
            context: "leaf record count".into(),
        });
    }

    let mut bytes = WireBuffer::new();
    push_header(&mut bytes, TAG_LEAF);
    bytes.push_long(WireLong::from(u64::from(count)));

    for record in records {
        bytes.push_length_prefixed(
            WireBytes::from(record.key().as_ref()),
            "leaf key length".into(),
        )?;
        bytes.push_length_prefixed(
            WireBytes::from(record.value().as_ref()),
            "leaf value length".into(),
        )?;
    }

    let node = OwnedEncodedNode::from(Vec::<u8>::from(bytes));

    if node.as_ref().len() > usize::from(MAX_NODE_BYTES) {
        return Err(RecordTreeError::BudgetExceeded {
            context: "node byte length".into(),
        });
    }

    Ok(node)
}

/// Encodes child references as an internal node.
///
/// # Specification
/// - requires: `children` is non-empty, strictly increasing in separator order,
///   and each child stands for at least one record — the caller's obligation,
///   re-established by the decoder.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|node|
///   decode_node(node.as_borrowed(), &mut
///   DecodeWork::new()).is_ok_and(|decoded| match decoded {
///   DecodedNode::Internal(internal) => internal.children() == children,
///   DecodedNode::Leaf(_) => false }))` — the encoding decodes back to exactly
///   these children, and the decoder admits it only when the header carries
///   their record counts summed.
/// - provides: the internal half of the canonical encoding.
/// - fails: [`RecordTreeError::BudgetExceeded`] when the child list exceeds the
///   child budget or the encoded node exceeds the node byte budget;
///   [`RecordTreeError::ArithmeticOverflow`] when a count or a field length
///   exceeds the wire width; [`RecordTreeError::InvalidProofShape`] when there
///   are no children, because an internal node with no children names no
///   records and cannot be a root.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::BudgetExceeded`] — the child list exceeds the child
/// budget or the encoded node exceeds the node byte budget.
/// [`RecordTreeError::ArithmeticOverflow`] — a count or field length exceeds
/// the wire width.
/// [`RecordTreeError::InvalidProofShape`] — the child list is empty.
///
/// # Adequacy
/// - hypothesis: L2 agreement — a round-trip property over generated trees
///   asserts decode after encode is the identity on children — plus L3 for the
///   empty-children guard, whose distinguishing input is the empty slice.
/// - witness: `node::tests::internal_nodes_round_trip`
/// - witness: `node::tests::an_internal_node_needs_children`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|node| {
    decode_node(node.as_borrowed(), &mut DecodeWork::new()).is_ok_and(|decoded| match decoded {
        | DecodedNode::Internal(internal) => internal.children() == children,
        | DecodedNode::Leaf(_) => false,
    })
}))]
pub fn encode_internal(children: &[ChildRef]) -> Result<OwnedEncodedNode, RecordTreeError>
{
    if children.is_empty() {
        return Err(RecordTreeError::InvalidProofShape {
            context: "an internal node carries no children".into(),
        });
    }

    let Ok(child_count) = u64::try_from(children.len())
    else {
        return Err(RecordTreeError::ArithmeticOverflow {
            context: "child count does not fit the wire width".into(),
        });
    };

    if child_count > u64::from(MAX_NODE_CHILDREN) {
        return Err(RecordTreeError::BudgetExceeded {
            context: "internal child count".into(),
        });
    }

    let mut total = RecordCount::ZERO;

    for child in children {
        total = total.plus(child.record_count())?;
    }

    let mut bytes = WireBuffer::new();
    push_header(&mut bytes, TAG_INTERNAL);
    bytes.push_long(WireLong::from(u64::from(total)));
    bytes.push_long(WireLong::from(child_count));

    for child in children {
        bytes.push_length_prefixed(
            WireBytes::from(child.first_key().as_ref()),
            "separator length".into(),
        )?;
        bytes.push_hash(child.identity());
        bytes.push_long(WireLong::from(u64::from(child.record_count())));
    }

    let node = OwnedEncodedNode::from(Vec::<u8>::from(bytes));

    if node.as_ref().len() > usize::from(MAX_NODE_BYTES) {
        return Err(RecordTreeError::BudgetExceeded {
            context: "node byte length".into(),
        });
    }

    Ok(node)
}

/// Reads what a node encoding declares without materializing its contents.
///
/// # Specification
/// - requires: nothing; the bytes are arbitrary and possibly hostile.
/// - ensures: `|ret| ret.is_ok() == decode_node(bytes, &mut
///   DecodeWork::new()).is_ok()` — on success the bytes are a complete,
///   canonical node encoding whose internal order and count invariants hold,
///   because the check runs the materializing decoder and drops the result, so
///   the caller never holds the contents.
/// - provides: the store's admission check, which needs to know that bytes are
///   node material before the store holds them.
/// - fails: [`RecordTreeError::MalformedNode`] for framing, order or count
///   defects; [`RecordTreeError::UnsupportedVersion`] for an unknown version;
///   [`RecordTreeError::BudgetExceeded`] when a declared count exceeds its
///   ceiling; [`RecordTreeError::ArithmeticOverflow`] when a count exceeds a
///   width.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::MalformedNode`] — framing, order, or count defect.
/// [`RecordTreeError::UnsupportedVersion`] — unknown encoding version.
/// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its ceiling.
/// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
///
/// # Adequacy
/// - hypothesis: L2 agreement — inspection is required to accept exactly the
///   encodings the materializing decoder accepts, asserted as a differential
///   over generated nodes and over each mutated-byte rejection case.
/// - witness: `node::tests::inspection_agrees_with_decoding`
/// - witness: `node::tests::truncation_is_refused`
#[inline]
#[spec(ensures: |ret| ret.is_ok() == decode_node(bytes, &mut DecodeWork::new()).is_ok())]
pub fn inspect_node(bytes: EncodedNode<'_>) -> Result<NodeLayout, RecordTreeError>
{
    let mut work = DecodeWork::new();
    let decoded = decode_node(bytes, &mut work)?;

    match decoded {
        | DecodedNode::Leaf(leaf) => {
            let record_count = leaf.record_count()?;

            Ok(NodeLayout {
                kind: NodeKind::Leaf,
                record_count,
                children: None,
            })
        },
        | DecodedNode::Internal(internal) => {
            let Ok(child_count) = u64::try_from(internal.children().len())
            else {
                return Err(RecordTreeError::ArithmeticOverflow {
                    context: "child count does not fit the wire width".into(),
                });
            };

            Ok(NodeLayout {
                kind: NodeKind::Internal,
                record_count: internal.record_count(),
                children: Some(ChildCount::from(child_count)),
            })
        },
    }
}

/// Recomputes a stored node's identity and refuses bytes that are not node
/// material under it.
///
/// # Specification
/// - requires: nothing; both the bytes and the claimed identity are arbitrary.
/// - ensures: `|ret| ret.is_ok() == (hash_node(node.bytes()) == node.identity()
///   && inspect_node(node.bytes()).is_ok())` — on success the bytes hash to the
///   claimed identity under the node domain and decode as a canonical node.
/// - provides: the check that makes a store's returned bytes verified rather
///   than merely retrieved.
/// - fails: [`RecordTreeError::HashMismatch`] when the recomputed identity
///   differs, plus every [`inspect_node`] failure.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::HashMismatch`] — the bytes do not hash to the claimed
/// identity.
/// [`RecordTreeError::MalformedNode`] — the bytes are not node material.
/// [`RecordTreeError::UnsupportedVersion`] — unknown encoding version.
/// [`RecordTreeError::BudgetExceeded`] — a declared count exceeds its ceiling.
/// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is the identity comparison,
///   separated by the matching pair and by a pair differing in one byte of the
///   claimed identity, with the exact variant and both payloads asserted.
/// - witness: `node::tests::a_mismatched_identity_is_refused`
#[inline]
#[spec(ensures: |ret| ret.is_ok()
    == (hash_node(node.bytes()) == node.identity() && inspect_node(node.bytes()).is_ok()))]
pub fn verify_stored_node(node: StoredNode<'_>) -> Result<(), RecordTreeError>
{
    let actual = hash_node(node.bytes());

    if actual != node.identity() {
        return Err(RecordTreeError::HashMismatch {
            expected: node.identity(),
            actual,
        });
    }

    let _layout = inspect_node(node.bytes())?;

    Ok(())
}

/// Decodes node bytes, charging the work to `work`.
///
/// # Specification
/// - requires: nothing; the bytes are arbitrary and possibly hostile.
/// - ensures: on success every invariant the encoders promise holds of the
///   returned node, and `work` has been charged one node plus the records the
///   node materialized.
/// - provides: the materializing decoder every verifier reads nodes through.
///   The postcondition stays prose: the encoder-agreement half is a law over
///   two implementations, and a clause for the charge half alone would be
///   weaker than the line it replaces.
/// - fails: [`RecordTreeError::MalformedNode`] for framing, order or count
///   defects; [`RecordTreeError::UnsupportedVersion`] for an unknown version;
///   [`RecordTreeError::DuplicateKeys`] for an equal adjacent key pair;
///   [`RecordTreeError::BudgetExceeded`] when a ceiling is crossed;
///   [`RecordTreeError::ArithmeticOverflow`] when a count exceeds a width.
/// - panics: none.
/// - intension: one forward pass over the bytes with no seek and no lookahead,
///   and no allocation before the count that sizes it has been checked against
///   the bytes that remain. The observation is the charge recorded in `work`,
///   which is one node and exactly the records materialized.
///
/// # Errors
/// [`RecordTreeError::MalformedNode`] — framing, order, or count defect.
/// [`RecordTreeError::UnsupportedVersion`] — unknown encoding version.
/// [`RecordTreeError::DuplicateKeys`] — a leaf repeats a key.
/// [`RecordTreeError::BudgetExceeded`] — a ceiling is crossed.
/// [`RecordTreeError::ArithmeticOverflow`] — a count exceeds a width.
///
/// # Adequacy
/// - hypothesis: L2 agreement for the round trip, and L3 for each refusal — one
///   witness per named failure mode, each asserting the exact variant on an
///   input that triggers only that mode.
/// - witness: `node::tests::leaves_round_trip`
/// - witness: `node::tests::internal_nodes_round_trip`
/// - witness: `node::tests::truncation_is_refused`
/// - witness: `node::tests::trailing_bytes_are_refused`
/// - witness: `node::tests::an_unknown_version_is_refused`
/// - witness: `node::tests::an_unknown_kind_is_refused`
/// - witness: `node::tests::unsorted_leaf_records_are_refused`
/// - witness: `node::tests::repeated_leaf_keys_are_refused`
/// - witness: `node::tests::unsorted_separators_are_refused`
/// - witness: `node::tests::a_childless_internal_node_is_refused`
/// - witness: `node::tests::an_empty_child_is_refused`
/// - witness: `node::tests::a_wrong_internal_record_total_is_refused`
/// - witness: `node::tests::an_oversized_node_is_refused`
/// - witness: `node::tests::an_overstated_record_count_is_refused`
#[inline]
pub fn decode_node(
    bytes: EncodedNode<'_>,
    work: &mut DecodeWork,
) -> Result<DecodedNode, RecordTreeError>
{
    if bytes.as_ref().len() > usize::from(MAX_NODE_BYTES) {
        return Err(RecordTreeError::BudgetExceeded {
            context: "node byte length".into(),
        });
    }

    work.charge_node()?;

    let mut cursor = Cursor::new(WireBytes::from(bytes.as_ref()));
    cursor.expect_domain(Domain::Node, "node domain".into())?;
    let version = cursor.read_word("node encoding version".into())?;
    let _version = EncodingVersion::from_number(WireVersion::from(u16::from(version)))?;
    let kind = cursor.read_tag("node kind".into())?;

    let decoded = match kind {
        | TAG_LEAF => {
            let leaf = decode_leaf(&mut cursor, work)?;

            DecodedNode::Leaf(leaf)
        },
        | TAG_INTERNAL => {
            let internal = decode_internal(&mut cursor)?;

            DecodedNode::Internal(internal)
        },
        | _ => {
            return Err(RecordTreeError::MalformedNode {
                context: "node kind is unknown".into(),
            });
        },
    };

    if cursor.completion() != DecodeCompletion::Complete {
        return Err(RecordTreeError::MalformedNode {
            context: "node has trailing bytes".into(),
        });
    }

    Ok(decoded)
}

/// Appends the header both node shapes share.
///
/// # Specification
/// - requires: `bytes` is empty or holds only complete earlier nodes, and
///   `kind` is one of the two node discriminators.
/// - ensures: appends the node domain tag, the current encoding version as a
///   little-endian word, and `kind`, in that order — the three fields every
///   node shape opens with.
/// - provides: the one site the shared header is written at, so a leaf and an
///   internal node cannot drift apart in it, and so the version a node declares
///   is the build's own.
/// - fails: never.
/// - panics: none.
fn push_header(
    bytes: &mut WireBuffer,
    kind: WireTag,
)
{
    bytes.push_domain(Domain::Node);
    bytes.push_word(WireWord::from(u16::from(EncodingVersion::CURRENT.number())));
    bytes.push_tag(kind);
}

/// Decodes a leaf payload.
///
/// # Specification
/// - requires: `cursor` sits at a leaf payload, and `work` is this node's
///   accounting accumulator.
/// - ensures: on success the leaf's keys are strictly increasing, its record
///   count matches the declared count, and `work` has been charged that count.
/// - provides: the leaf payload the node decoder materializes. The
///   postcondition stays prose: the declared count is read from `cursor` inside
///   the body and is not carried by the returned leaf, so no clause can compare
///   against it.
/// - fails: [`RecordTreeError::MalformedNode`] on a truncated or unsorted
///   payload; [`RecordTreeError::DuplicateKeys`] on an equal adjacent key pair;
///   [`RecordTreeError::BudgetExceeded`] when the declared count exceeds the
///   leaf ceiling; [`RecordTreeError::ArithmeticOverflow`] when a count exceeds
///   the host width.
/// - panics: none.
fn decode_leaf(
    cursor: &mut Cursor<'_>,
    work: &mut DecodeWork,
) -> Result<LeafNode, RecordTreeError>
{
    let declared = cursor.read_long("leaf record count".into())?;
    let declared = RecordCount::from(u64::from(declared));

    if declared > MAX_LEAF_RECORDS {
        return Err(RecordTreeError::BudgetExceeded {
            context: "leaf record count".into(),
        });
    }

    work.charge_records(declared)?;
    let capacity = cursor.admissible_item_count(
        WireLong::from(u64::from(declared)),
        LEAST_RECORD_BYTES,
        "leaf record count".into(),
    )?;
    let capacity = usize::from(capacity);
    let mut records = Vec::<Record>::with_capacity(capacity);
    let mut position = RecordIndex::ZERO;

    for _ in 0_usize .. capacity {
        let key = cursor.read_length_prefixed("leaf key".into())?;
        let value = cursor.read_length_prefixed("leaf value".into())?;
        let key = OwnedRecordKey::from(key.as_ref());

        if let Some(earlier) = records.last() {
            match earlier.key().as_ref().cmp(key.as_ref()) {
                | Ordering::Less => {},
                | Ordering::Equal => {
                    return Err(RecordTreeError::DuplicateKeys {
                        first: RecordIndex::from(records.len().saturating_sub(0x01_usize)),
                        second: position,
                    });
                },
                | Ordering::Greater => {
                    return Err(RecordTreeError::MalformedNode {
                        context: "leaf records are unsorted".into(),
                    });
                },
            }
        }

        position = position.next()?;
        records.push(Record::new(key, OwnedRecordValue::from(value.as_ref())));
    }

    Ok(LeafNode {
        records: records.into_boxed_slice(),
    })
}

/// Decodes an internal payload.
///
/// # Specification
/// - requires: `cursor` sits at an internal payload.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|internal|
///   internal.children().iter().zip(internal.children().iter().skip(1))
///   .all(|(earlier, later)| earlier.first_key() < later.first_key()) &&
///   internal.children().iter().all(|child| child.record_count() !=
///   RecordCount::ZERO) && internal.children().iter().try_fold(
///   RecordCount::ZERO, |total, child| total.plus(child.record_count()).ok())
///   == Some(internal.record_count()))` — on success the separators are
///   strictly increasing, every child reference stands for at least one record,
///   and the child record counts sum to the declared total, which the returned
///   node carries.
/// - fails: [`RecordTreeError::MalformedNode`] on a truncated payload, unsorted
///   separators, or a child that stands for no records;
///   [`RecordTreeError::BudgetExceeded`] when the child count exceeds the node
///   ceiling; [`RecordTreeError::ArithmeticOverflow`] when a count exceeds the
///   host width.
/// - panics: none.
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|internal| {
    internal
        .children()
        .iter()
        .zip(internal.children().iter().skip(1_usize))
        .all(|(earlier, later)| earlier.first_key() < later.first_key())
        && internal
            .children()
            .iter()
            .all(|child| child.record_count() != RecordCount::ZERO)
        && internal
            .children()
            .iter()
            .try_fold(RecordCount::ZERO, |total, child| total.plus(child.record_count()).ok())
            == Some(internal.record_count())
}))]
fn decode_internal(cursor: &mut Cursor<'_>) -> Result<InternalNode, RecordTreeError>
{
    let declared_records = cursor.read_long("internal record count".into())?;
    let declared_records = RecordCount::from(u64::from(declared_records));
    let declared_children = cursor.read_long("internal child count".into())?;
    let declared_children = ChildCount::from(u64::from(declared_children));

    if declared_children == ChildCount::ZERO {
        return Err(RecordTreeError::MalformedNode {
            context: "an internal node carries no children".into(),
        });
    }

    if declared_children > MAX_NODE_CHILDREN {
        return Err(RecordTreeError::BudgetExceeded {
            context: "internal child count".into(),
        });
    }

    let capacity = cursor.admissible_item_count(
        WireLong::from(u64::from(declared_children)),
        LEAST_CHILD_BYTES,
        "internal child count".into(),
    )?;
    let capacity = usize::from(capacity);
    let mut children = Vec::<ChildRef>::with_capacity(capacity);
    let mut total = RecordCount::ZERO;

    for _ in 0_usize .. capacity {
        let first_key = cursor.read_length_prefixed("separator key".into())?;
        let first_key = OwnedRecordKey::from(first_key.as_ref());
        let hash = cursor.take_array::<NODE_HASH_LEN>("child identity".into())?;
        let record_count = cursor.read_long("child record count".into())?;
        let record_count = RecordCount::from(u64::from(record_count));

        if record_count == RecordCount::ZERO {
            return Err(RecordTreeError::MalformedNode {
                context: "a child stands for no records".into(),
            });
        }

        if let Some(earlier) = children.last()
            && earlier.first_key().as_ref() >= first_key.as_ref()
        {
            return Err(RecordTreeError::MalformedNode {
                context: "separators are not strictly increasing".into(),
            });
        }

        total = total.plus(record_count)?;
        children.push(ChildRef::new(
            first_key,
            NodeHash::from(<[u8; NODE_HASH_LEN]>::from(hash)),
            record_count,
        ));
    }

    if total != declared_records {
        return Err(RecordTreeError::MalformedNode {
            context: "child record counts do not sum to the declared total".into(),
        });
    }

    Ok(InternalNode {
        record_count: total,
        children: children.into_boxed_slice(),
    })
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::vec;
    use alloc::vec::Vec;

    use super::ChildIndex;
    use super::ChildRef;
    use super::DecodedNode;
    use super::NodeKind;
    use super::StoredNode;
    use super::decode_node;
    use super::encode_internal;
    use super::encode_leaf;
    use super::hash_node;
    use super::inspect_node;
    use super::verify_stored_node;
    use crate::bytes::EncodedNode;
    use crate::bytes::NodeHash;
    use crate::bytes::OwnedRecordKey;
    use crate::bytes::RecordKey;
    use crate::bytes::RecordValue;
    use crate::error::RecordTreeError;
    use crate::error::WireVersion;
    use crate::params::EncodingVersion;
    use crate::record::Record;
    use crate::record::RecordCount;
    use crate::record::RecordIndex;
    use crate::record::RecordRef;
    use crate::wire::ChildCount;
    use crate::wire::DecodeWork;
    use crate::wire::Domain;
    use crate::wire::MAX_LEAF_RECORDS;
    use crate::wire::MAX_NODE_BYTES;
    use crate::wire::WireTag;

    /// A seed byte for a node identity no tree produces.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct HashSeed(u8);

    /// Raw node bytes under construction, before they are handed to a decoder.
    #[repr(transparent)]
    #[derive(Debug)]
    struct NodeBytes(Vec<u8>);

    impl NodeBytes
    {
        /// The node bytes so far, as the borrowed encoding the decoder takes.
        ///
        /// # Specification
        /// trivial.
        fn as_bytes(&self) -> EncodedNode<'_>
        {
            EncodedNode::from(self.0.as_slice())
        }
    }

    /// A byte run under length-prefix framing.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct ByteRun<'bytes>(&'bytes [u8]);

    /// A node identity built from one seed byte.
    ///
    /// # Specification
    /// - requires: nothing; every seed is admissible.
    /// - ensures: an identity whose first byte is the seed and whose remaining
    ///   bytes are zero, so distinct seeds give distinct identities.
    /// - provides: an identity no encoding produces, which is what the mismatch
    ///   and child-reference fixtures below need.
    /// - panics: none.
    fn node_hash(seed: HashSeed) -> NodeHash
    {
        let mut bytes = [0_u8; 32_usize];
        bytes[0] = seed.0;

        NodeHash::from(bytes)
    }

    /// Decodes node bytes against a fresh accounting accumulator.
    ///
    /// # Specification
    /// - requires: nothing; malformed and adversarial bytes are the point.
    /// - ensures: exactly what [`decode_node`] answers for `bytes` under an
    ///   accumulator charged by nothing else.
    /// - provides: the per-call budget isolation the fixtures below need, so
    ///   one case's accounting cannot pay for the next.
    /// - fails: propagates the decoder's refusal unchanged.
    /// - panics: none.
    fn decode(bytes: EncodedNode<'_>) -> Result<DecodedNode, RecordTreeError>
    {
        let mut work = DecodeWork::new();

        decode_node(bytes, &mut work)
    }

    /// Forty records with distinct keys already in key order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: forty records whose keys are the zero-padded decimal
    ///   positions, so they are distinct and sorted.
    /// - provides: the payload the encode and decode fixtures below round trip,
    ///   large enough to cross a leaf boundary.
    /// - panics: none.
    fn sample_records() -> Vec<Record>
    {
        (0_usize .. 40_usize)
            .map(|index| {
                Record::new(
                    format!("key-{index:04}").into_bytes(),
                    format!("value-{index:04}").into_bytes(),
                )
            })
            .collect()
    }

    /// Borrows a corpus as the record references an encoder takes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly one borrowed reference per element of `records`, in
    ///   the order `records` holds them, so nothing is dropped, added, or
    ///   permuted.
    /// - provides: the reference sequence an encoder takes, matching the corpus
    ///   position for position.
    /// - fails: never.
    /// - panics: none.
    fn borrow(records: &[Record]) -> Vec<RecordRef<'_>>
    {
        records.iter().map(Record::as_record_ref).collect()
    }

    #[test]
    fn the_node_identity_is_pinned()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");

        // Hand check of the encoding: the node domain tag, the encoding
        // version two as a little-endian word (2 = 0x0002, low byte 0x02
        // first), the leaf kind byte, the record count one as a
        // little-endian long (0x01 followed by seven zero bytes), then each
        // run: a little-endian long length one and the run's own byte.
        let mut expected = Vec::from(b"gandr:storage-records:node:v1");
        expected.extend_from_slice(&[0x02_u8, 0x00]);
        expected.push(0x00_u8);
        expected.extend_from_slice(&[0x01_u8, 0, 0, 0, 0, 0, 0, 0]);
        expected.extend_from_slice(&[0x01_u8, 0, 0, 0, 0, 0, 0, 0, b'a']);
        expected.extend_from_slice(&[0x01_u8, 0, 0, 0, 0, 0, 0, 0, b'1']);
        assert_eq!(Vec::from(encoded.as_ref()), expected);

        let hash = hash_node(encoded.as_borrowed());

        assert_eq!(
            format!("{hash}"),
            "3ee3f38a2610c969e4695d08f800611d7d8dba159c6dfe6cc2c81f5713ebc327"
        );
    }

    #[test]
    fn leaves_round_trip()
    {
        let owned = sample_records();
        let records = borrow(owned.as_slice());
        let encoded = encode_leaf(records.as_slice()).expect("the leaf encodes");
        let decoded = decode(encoded.as_borrowed()).expect("the leaf decodes");
        let leaf = decoded.as_leaf().expect("a leaf decodes as a leaf");

        let expected: Vec<Record> = records.iter().map(|record| Record::from(*record)).collect();
        assert_eq!(leaf.records(), expected.as_slice());
        assert_eq!(decoded.kind(), NodeKind::Leaf);
    }

    #[test]
    fn an_empty_leaf_round_trips()
    {
        let encoded = encode_leaf(&[]).expect("an empty leaf encodes");
        let decoded = decode(encoded.as_borrowed()).expect("an empty leaf decodes");
        let leaf = decoded.as_leaf().expect("a leaf decodes as a leaf");

        assert_eq!(leaf.records(), [].as_slice());
        assert_eq!(leaf.first_key(), None);
        assert_eq!(leaf.record_count(), Ok(RecordCount::ZERO));
    }

    #[test]
    fn internal_nodes_round_trip()
    {
        let children = vec![
            ChildRef::new(b"a", node_hash(HashSeed(1_u8)), RecordCount::from(2_u64)),
            ChildRef::new(b"m", node_hash(HashSeed(2_u8)), RecordCount::from(3_u64)),
            ChildRef::new(b"z", node_hash(HashSeed(3_u8)), RecordCount::from(1_u64)),
        ];
        let encoded = encode_internal(children.as_slice()).expect("the node encodes");
        let decoded = decode(encoded.as_borrowed()).expect("the node decodes");

        match decoded {
            | DecodedNode::Internal(ref internal) => {
                assert_eq!(internal.children(), children.as_slice());
                assert_eq!(internal.record_count(), RecordCount::from(6_u64));
            },
            | DecodedNode::Leaf(_) => panic!("an internal encoding decoded as a leaf"),
        }
        assert_eq!(decoded.kind(), NodeKind::Internal);
    }

    #[test]
    fn an_internal_node_needs_children()
    {
        assert_eq!(
            encode_internal(&[]),
            Err(RecordTreeError::InvalidProofShape {
                context: "an internal node carries no children".into(),
            })
        );
    }

    #[test]
    fn child_selection_picks_the_last_separator_at_or_below_the_key()
    {
        let children = vec![
            ChildRef::new(b"a", node_hash(HashSeed(1_u8)), RecordCount::from(1_u64)),
            ChildRef::new(b"m", node_hash(HashSeed(2_u8)), RecordCount::from(1_u64)),
            ChildRef::new(b"z", node_hash(HashSeed(3_u8)), RecordCount::from(1_u64)),
        ];
        let encoded = encode_internal(children.as_slice()).expect("the node encodes");
        let decoded = decode(encoded.as_borrowed()).expect("the node decodes");
        let internal = match decoded {
            | DecodedNode::Internal(internal) => internal,
            | DecodedNode::Leaf(_) => panic!("an internal encoding decoded as a leaf"),
        };

        assert_eq!(
            internal.child_for_key(RecordKey::from(b"0")),
            Some(ChildIndex::from(0_usize))
        );
        assert_eq!(
            internal.child_for_key(RecordKey::from(b"a")),
            Some(ChildIndex::from(0_usize))
        );
        assert_eq!(
            internal.child_for_key(RecordKey::from(b"n")),
            Some(ChildIndex::from(1_usize))
        );
        assert_eq!(
            internal.child_for_key(RecordKey::from(b"zz")),
            Some(ChildIndex::from(2_usize))
        );
    }

    #[test]
    fn child_selection_has_no_answer_without_children()
    {
        assert_eq!(super::select_child(&[], RecordKey::from(b"a")), None);
    }

    #[test]
    fn inspection_agrees_with_decoding()
    {
        let owned = sample_records();
        let records = borrow(owned.as_slice());
        let leaf = encode_leaf(records.as_slice()).expect("the leaf encodes");
        let layout = inspect_node(leaf.as_borrowed()).expect("the leaf is node material");

        assert_eq!(layout.kind(), NodeKind::Leaf);
        assert_eq!(layout.record_count(), RecordCount::from(40_u64));
        assert_eq!(layout.children(), None);

        let children = vec![ChildRef::new(
            b"a",
            node_hash(HashSeed(1_u8)),
            RecordCount::from(9_u64),
        )];
        let internal = encode_internal(children.as_slice()).expect("the node encodes");
        let layout = inspect_node(internal.as_borrowed()).expect("the node is node material");

        assert_eq!(layout.kind(), NodeKind::Internal);
        assert_eq!(layout.record_count(), RecordCount::from(9_u64));
        assert_eq!(layout.children(), Some(ChildCount::from(0x01_u64)));
    }

    #[test]
    fn truncation_is_refused()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let bytes = encoded.as_ref();
        let (head, _tail) = bytes.split_at(bytes.len().saturating_sub(1_usize));

        assert_eq!(
            decode(EncodedNode::from(head)),
            Err(RecordTreeError::MalformedNode {
                context: "leaf value".into(),
            })
        );
    }

    #[test]
    fn trailing_bytes_are_refused()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let mut bytes = Vec::from(encoded.as_ref());
        bytes.push(0_u8);

        assert_eq!(
            decode(EncodedNode::from(bytes.as_slice())),
            Err(RecordTreeError::MalformedNode {
                context: "node has trailing bytes".into(),
            })
        );
    }

    #[test]
    fn a_foreign_domain_is_refused()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let mut bytes = Vec::from(encoded.as_ref());
        let tag = Domain::Node.tag();
        bytes[usize::from(tag.len()).saturating_sub(1_usize)] = b'2';

        assert_eq!(
            decode(EncodedNode::from(bytes.as_slice())),
            Err(RecordTreeError::MalformedNode {
                context: "node domain".into(),
            })
        );
    }

    #[test]
    fn an_unknown_version_is_refused()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let mut bytes = Vec::from(encoded.as_ref());
        let offset = usize::from(Domain::Node.tag().len());
        // The version field is little-endian, so its low byte leads: setting
        // it to nine names the version nine, which no build accepts.
        bytes[offset] = 9_u8;

        assert_eq!(
            decode(EncodedNode::from(bytes.as_slice())),
            Err(RecordTreeError::UnsupportedVersion {
                version: WireVersion::from(9_u16),
            })
        );
    }

    #[test]
    fn an_unknown_kind_is_refused()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let mut bytes = Vec::from(encoded.as_ref());
        let offset = usize::from(Domain::Node.tag().len()).saturating_add(2_usize);
        bytes[offset] = 0x7f_u8;

        assert_eq!(
            decode(EncodedNode::from(bytes.as_slice())),
            Err(RecordTreeError::MalformedNode {
                context: "node kind is unknown".into(),
            })
        );
    }

    #[test]
    fn unsorted_leaf_records_are_refused()
    {
        let mut bytes = leaf_prefix(RecordCount::from(2_u64));
        push_record(&mut bytes, b"b".into(), b"2".into());
        push_record(&mut bytes, b"a".into(), b"1".into());

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::MalformedNode {
                context: "leaf records are unsorted".into(),
            })
        );
    }

    #[test]
    fn repeated_leaf_keys_are_refused()
    {
        let mut bytes = leaf_prefix(RecordCount::from(2_u64));
        push_record(&mut bytes, b"a".into(), b"1".into());
        push_record(&mut bytes, b"a".into(), b"2".into());

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::DuplicateKeys {
                first: RecordIndex::from(0_usize),
                second: RecordIndex::from(1_usize),
            })
        );
    }

    #[test]
    fn an_overstated_record_count_is_refused()
    {
        let mut bytes = leaf_prefix(RecordCount::from(9_u64));
        push_record(&mut bytes, b"a".into(), b"1".into());

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::MalformedNode {
                context: "leaf record count".into(),
            })
        );
    }

    #[test]
    fn an_oversized_leaf_count_is_refused()
    {
        let bytes = leaf_prefix(RecordCount::from(
            u64::from(MAX_LEAF_RECORDS).saturating_add(1_u64),
        ));

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::BudgetExceeded {
                context: "leaf record count".into(),
            })
        );
    }

    #[test]
    fn an_oversized_node_is_refused()
    {
        let bytes = NodeBytes(vec![
            0_u8;
            usize::from(MAX_NODE_BYTES).saturating_add(1_usize)
        ]);

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::BudgetExceeded {
                context: "node byte length".into(),
            })
        );
    }

    #[test]
    fn an_over_budget_leaf_is_refused()
    {
        let count = usize::try_from(u64::from(MAX_LEAF_RECORDS)).expect("the leaf ceiling fits");
        let records: Vec<RecordRef<'_>> =
            core::iter::repeat_n(RecordRef::new(b"", b""), count).collect();

        assert_eq!(
            encode_leaf(records.as_slice()),
            Err(RecordTreeError::BudgetExceeded {
                context: "node byte length".into(),
            })
        );
    }

    #[test]
    fn an_over_budget_internal_node_is_refused()
    {
        let separator = [0xab_u8; 300_usize];
        let child = ChildRef::new(
            separator.as_slice(),
            node_hash(HashSeed(0x01_u8)),
            RecordCount::from(0x01_u64),
        );
        let children: Vec<ChildRef> = core::iter::repeat_with(|| child.clone())
            .take(0x01_0000_usize)
            .collect();

        assert_eq!(
            encode_internal(children.as_slice()),
            Err(RecordTreeError::BudgetExceeded {
                context: "node byte length".into(),
            })
        );
    }

    #[test]
    fn unsorted_separators_are_refused()
    {
        let mut bytes = internal_prefix(RecordCount::from(2_u64), ChildCount::from(2_u64));
        push_child(
            &mut bytes,
            b"m".into(),
            node_hash(HashSeed(1_u8)),
            RecordCount::from(1_u64),
        );
        push_child(
            &mut bytes,
            b"a".into(),
            node_hash(HashSeed(2_u8)),
            RecordCount::from(1_u64),
        );

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::MalformedNode {
                context: "separators are not strictly increasing".into(),
            })
        );
    }

    #[test]
    fn a_childless_internal_node_is_refused()
    {
        let bytes = internal_prefix(RecordCount::from(0_u64), ChildCount::from(0_u64));

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::MalformedNode {
                context: "an internal node carries no children".into(),
            })
        );
    }

    #[test]
    fn an_empty_child_is_refused()
    {
        let mut bytes = internal_prefix(RecordCount::from(0_u64), ChildCount::from(1_u64));
        push_child(
            &mut bytes,
            b"a".into(),
            node_hash(HashSeed(1_u8)),
            RecordCount::from(0_u64),
        );

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::MalformedNode {
                context: "a child stands for no records".into(),
            })
        );
    }

    #[test]
    fn a_wrong_internal_record_total_is_refused()
    {
        let mut bytes = internal_prefix(RecordCount::from(5_u64), ChildCount::from(1_u64));
        push_child(
            &mut bytes,
            b"a".into(),
            node_hash(HashSeed(1_u8)),
            RecordCount::from(1_u64),
        );

        assert_eq!(
            decode(bytes.as_bytes()),
            Err(RecordTreeError::MalformedNode {
                context: "child record counts do not sum to the declared total".into(),
            })
        );
    }

    #[test]
    fn a_mismatched_identity_is_refused()
    {
        let encoded = encode_leaf(&[RecordRef::new(b"a", b"1")]).expect("the leaf encodes");
        let actual = hash_node(encoded.as_borrowed());

        assert_eq!(
            verify_stored_node(StoredNode::new(actual, encoded.as_borrowed())),
            Ok(())
        );
        assert_eq!(
            verify_stored_node(StoredNode::new(
                node_hash(HashSeed(0xaa_u8)),
                encoded.as_borrowed()
            )),
            Err(RecordTreeError::HashMismatch {
                expected: node_hash(HashSeed(0xaa_u8)),
                actual,
            })
        );
    }

    #[test]
    fn non_node_material_is_refused_by_the_store_check()
    {
        let body = b"not a node";
        let hash = hash_node(EncodedNode::from(body));

        assert_eq!(
            verify_stored_node(StoredNode::new(hash, EncodedNode::from(body))),
            Err(RecordTreeError::MalformedNode {
                context: "node domain".into(),
            })
        );
    }

    /// The shared node header, ending in `kind`.
    ///
    /// # Specification
    /// - requires: nothing; an unknown discriminator is admissible and is what
    ///   the unknown-kind fixture needs.
    /// - ensures: the node domain tag, the current encoding version as a
    ///   little-endian word, and `kind`, in that order — the same three fields
    ///   the encoder writes, spelled out here rather than reused.
    /// - provides: the hand-built prefix every malformed-payload fixture below
    ///   extends, written independently so a fixture cannot agree with the
    ///   encoder by construction.
    /// - panics: none.
    fn header(kind: WireTag) -> NodeBytes
    {
        let mut bytes = Vec::from(Domain::Node.tag().as_ref());
        bytes.extend_from_slice(
            u16::from(EncodingVersion::CURRENT.number())
                .to_le_bytes()
                .as_slice(),
        );
        bytes.push(u8::from(kind));

        NodeBytes(bytes)
    }

    /// A leaf header declaring `count` records, with no payload.
    ///
    /// # Specification
    /// - requires: nothing; a declared count the payload will not match is the
    ///   point.
    /// - ensures: the shared header with the leaf discriminator, followed by
    ///   `count` as a little-endian wire-width number.
    /// - provides: the prefix the truncation and count-disagreement fixtures
    ///   below extend.
    /// - panics: none.
    fn leaf_prefix(count: RecordCount) -> NodeBytes
    {
        let mut bytes = header(WireTag::from(0x00_u8));
        bytes
            .0
            .extend_from_slice(u64::from(count).to_le_bytes().as_slice());

        bytes
    }

    /// An internal header declaring both counts, with no payload.
    ///
    /// # Specification
    /// - requires: nothing; declared counts the payload will not match are the
    ///   point.
    /// - ensures: the shared header with the internal discriminator, then
    ///   `records` and then `children`, each as a little-endian wire-width
    ///   number.
    /// - provides: the prefix the child-payload fixtures below extend.
    /// - panics: none.
    fn internal_prefix(
        records: RecordCount,
        children: ChildCount,
    ) -> NodeBytes
    {
        let mut bytes = header(WireTag::from(0x01_u8));
        bytes
            .0
            .extend_from_slice(u64::from(records).to_le_bytes().as_slice());
        bytes
            .0
            .extend_from_slice(u64::from(children).to_le_bytes().as_slice());

        bytes
    }

    /// Appends one record's key and value under length-prefix framing.
    ///
    /// # Specification
    /// - requires: nothing; any key and value widths are admissible.
    /// - ensures: appends the key then the value, each behind its own
    ///   little-endian length prefix — the leaf payload framing.
    /// - provides: the record-appending half of the hand-built fixtures.
    /// - panics: when a body exceeds the wire width, which the expectation
    ///   names; every fixture body here is a few bytes.
    fn push_record(
        bytes: &mut NodeBytes,
        key: RecordKey<'_>,
        value: RecordValue<'_>,
    )
    {
        push_length_prefixed(bytes, ByteRun(key.as_ref()));
        push_length_prefixed(bytes, ByteRun(value.as_ref()));
    }

    /// Appends one child reference in payload order.
    ///
    /// # Specification
    /// - requires: nothing; any separator width is admissible.
    /// - ensures: appends the separator behind its length prefix, then the
    ///   identity's bytes, then the record count as a little-endian wire-width
    ///   number — the internal payload framing.
    /// - provides: the child-appending half of the hand-built fixtures.
    /// - panics: when the separator exceeds the wire width, which the
    ///   expectation in the helper below names.
    fn push_child(
        bytes: &mut NodeBytes,
        key: RecordKey<'_>,
        hash: NodeHash,
        records: RecordCount,
    )
    {
        push_length_prefixed(bytes, ByteRun(key.as_ref()));
        bytes.0.extend_from_slice(hash.as_ref());
        bytes
            .0
            .extend_from_slice(u64::from(records).to_le_bytes().as_slice());
    }

    /// Appends a byte run behind its little-endian length prefix.
    ///
    /// # Specification
    /// - requires: `body` is short enough for the wire width, which every
    ///   fixture here satisfies.
    /// - ensures: appends the run's length as a little-endian wire-width
    ///   number, then the run itself.
    /// - provides: the framing primitive both appenders above are written on.
    /// - panics: when the run exceeds the wire width, so a fixture that grew
    ///   past it fails loudly rather than writing a truncated prefix.
    fn push_length_prefixed(
        bytes: &mut NodeBytes,
        body: ByteRun<'_>,
    )
    {
        let length = u64::try_from(body.0.len()).expect("test bodies are short");
        bytes.0.extend_from_slice(length.to_le_bytes().as_slice());
        bytes.0.extend_from_slice(body.0);
    }

    #[test]
    fn owned_keys_borrow_without_copying_semantics()
    {
        let key = OwnedRecordKey::from(b"key");

        assert_eq!(key.as_borrowed().as_ref(), b"key".as_slice());
    }
}
