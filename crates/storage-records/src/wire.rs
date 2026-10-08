//! The byte layer: hash domains, the append buffer, the decoding cursor, and
//! the budgets that bound the work a small input can force.
//!
//! # Domain separation
//!
//! Every digest this crate computes puts a [`Domain`] string at the front of
//! the hashed preimage. Two byte languages sharing one backing namespace need
//! domain-separated digests, or a value of one language can be presented as a
//! value of the other under an identity that verifies. The keyed-record plane
//! implemented here is one such language; the value plane's chunk encoding is
//! another, and the two planes are expected to share a backing object. A chunk
//! digest must be a function of the value's own canonical bytes under the chunk
//! domain, never of this crate's leaf framing — which is exactly what the
//! domain prefix buys, and why the prefix is inside the preimage rather than
//! beside it.
//!
//! # Budgets
//!
//! Decoding is bounded twice. Per-structure ceilings ([`MAX_NODE_BYTES`],
//! [`MAX_LEAF_RECORDS`], [`MAX_NODE_CHILDREN`], [`MAX_PROOF_NODES`]) bound one
//! node or one proof envelope, and a total accumulator ([`DecodeWork`]) bounds
//! the sum over every node of one proof. The second is not implied by the
//! first: node count and per-node record count are separately bounded, so
//! without a total a proof of `n` cheap nodes each near its own record ceiling
//! forces work proportional to their product. The accumulator saturates and is
//! compared once per charge, so exhaustion is a refusal rather than an
//! overflow.

use alloc::vec::Vec;

use anodized::spec;

use crate::bytes::NODE_HASH_LEN;
use crate::bytes::NodeHash;
use crate::error::FailureContext;
use crate::error::RecordTreeError;
use crate::record::RecordCount;

/// The hash domain a digest is computed under.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Domain::tag`] returns a distinct, non-empty byte string per
///   variant, and no tag is a prefix of another because all four share the same
///   prefix and differ in the segment after it.
/// - provides: the separation that makes a digest answer for exactly one byte
///   language. The postcondition stays prose: distinctness and prefix-freedom
///   relate the four variants to each other, and a data specification states a
///   property of one value.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is the tag table, a finite
///   class enumerated exhaustively and asserted pairwise distinct and pairwise
///   non-prefix.
/// - witness: `wire::tests::domain_tags_are_distinct_and_prefix_free`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Domain
{
    /// The canonical encoding of one tree node.
    Node,
    /// The root manifest binding parameters, record count and root node.
    Root,
    /// The canonical encoding of one record, as fed to the boundary rule.
    Record,
    /// The boundary decision digest for one record.
    Boundary,
}

impl Domain
{
    /// Returns the byte string this domain prefixes its preimages with.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the fixed byte string for this variant, which the type's own
    ///   specification states is distinct from every other's and no other's
    ///   prefix.
    /// - provides: the domain separation a digest is computed under, so one
    ///   byte string cannot answer for two languages.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn tag(self) -> DomainTag
    {
        match self {
            | Self::Node => DomainTag(b"gandr:storage-records:node:v1"),
            | Self::Root => DomainTag(b"gandr:storage-records:root:v1"),
            | Self::Record => DomainTag(b"gandr:storage-records:record:v1"),
            | Self::Boundary => DomainTag(b"gandr:storage-records:boundary:v1"),
        }
    }
}

/// The byte string a domain prefixes its hashed preimages with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DomainTag(&'static [u8]);

impl DomainTag
{
    /// Returns the tag's byte length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn len(self) -> EncodedLength
    {
        EncodedLength(self.0.len())
    }
}

impl AsRef<[u8]> for DomainTag
{
    /// Borrows the tag's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// A borrowed run of wire bytes with no framing of its own.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireBytes<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for WireBytes<'bytes>
{
    /// Reads a byte slice as a run of wire bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        Self(bytes)
    }
}

impl<'bytes> From<WireBytes<'bytes>> for &'bytes [u8]
{
    /// Reads the run back out as a byte slice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: WireBytes<'bytes>) -> Self
    {
        bytes.0
    }
}

impl AsRef<[u8]> for WireBytes<'_>
{
    /// Borrows the run's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// A fixed-width run of wire bytes read as one field.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct WireArray<const LEN: usize>([u8; LEN]);

impl<const LEN: usize> From<[u8; LEN]> for WireArray<LEN>
{
    /// Reads a fixed-width byte array as one wire field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; LEN]) -> Self
    {
        Self(bytes)
    }
}

impl<const LEN: usize> From<WireArray<LEN>> for [u8; LEN]
{
    /// Reads the field back out as its bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: WireArray<LEN>) -> Self
    {
        bytes.0
    }
}

/// One discriminator byte of a wire format.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireTag(pub u8);

impl From<u8> for WireTag
{
    /// Reads a byte as a discriminator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: u8) -> Self
    {
        Self(tag)
    }
}

impl From<WireTag> for u8
{
    /// Reads the discriminator back out as a byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: WireTag) -> Self
    {
        tag.0
    }
}

/// One little-endian sixteen-bit field of a wire format.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireWord(u16);

impl From<u16> for WireWord
{
    /// Reads a `u16` as a sixteen-bit wire field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u16) -> Self
    {
        Self(value)
    }
}

impl From<WireWord> for u16
{
    /// Reads the field back out as a `u16`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WireWord) -> Self
    {
        value.0
    }
}

/// One little-endian sixty-four-bit field of a wire format.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireLong(u64);

impl From<u64> for WireLong
{
    /// Reads a `u64` as a sixty-four-bit wire field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

impl From<WireLong> for u64
{
    /// Reads the field back out as a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WireLong) -> Self
    {
        value.0
    }
}

/// A checked allocation capacity for items a decoder is about to materialize.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ItemCapacity(usize);

impl From<usize> for ItemCapacity
{
    /// Reads a `usize` as a checked allocation capacity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(capacity: usize) -> Self
    {
        Self(capacity)
    }
}

impl From<ItemCapacity> for usize
{
    /// Reads the capacity back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(capacity: ItemCapacity) -> Self
    {
        capacity.0
    }
}

/// Computes the digest of a preimage read as material of `domain`.
///
/// # Specification
/// - requires: `preimage` already carries the domain tag at its front when it
///   is a self-describing encoding — node and record encodings do, so this
///   function is called on them with the matching domain and the tag is not
///   repeated.
/// - ensures: equal `(domain, preimage)` pairs give equal digests, and the
///   digest is a function of the domain as well as the bytes.
/// - provides: the crate's only hashing entry point, so no digest is computed
///   without a domain. The postcondition stays prose: both halves relate two
///   calls, and one call carries one domain and one preimage.
/// - fails: never.
/// - panics: none.
#[inline]
#[must_use]
pub(crate) fn digest(
    domain: Domain,
    preimage: WireBytes<'_>,
) -> NodeHash
{
    let mut hasher = blake3::Hasher::new();
    let _tagged = hasher.update(domain.tag().as_ref());
    let _body = hasher.update(preimage.as_ref());
    let mut output = [0_u8; NODE_HASH_LEN];
    hasher.finalize_xof().fill(output.as_mut_slice());

    NodeHash::from(output)
}

/// A byte length of one encoded structure.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EncodedLength(usize);

impl From<usize> for EncodedLength
{
    /// Reads a `usize` as an encoded byte length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: usize) -> Self
    {
        Self(length)
    }
}

impl From<EncodedLength> for usize
{
    /// Reads the length back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: EncodedLength) -> Self
    {
        length.0
    }
}

/// A count of child references carried by an internal node.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildCount(u64);

impl ChildCount
{
    /// The empty count.
    pub const ZERO: Self = Self(0_u64);
}

impl From<u64> for ChildCount
{
    /// Reads a `u64` as a child count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u64) -> Self
    {
        Self(count)
    }
}

impl From<ChildCount> for u64
{
    /// Reads the child count back out as a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ChildCount) -> Self
    {
        count.0
    }
}

/// A count of encoded nodes carried by a proof.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeCount(u64);

impl From<u64> for NodeCount
{
    /// Reads a `u64` as a node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u64) -> Self
    {
        Self(count)
    }
}

impl From<NodeCount> for u64
{
    /// Reads the node count back out as a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: NodeCount) -> Self
    {
        count.0
    }
}

/// The largest canonical encoding one node may occupy.
pub const MAX_NODE_BYTES: EncodedLength = EncodedLength(0x0100_0000_usize);

/// The largest number of records one leaf may carry.
pub const MAX_LEAF_RECORDS: RecordCount = RecordCount(0x0010_0000_u64);
/// The largest number of children one internal node may carry.
pub const MAX_NODE_CHILDREN: ChildCount = ChildCount(0x0010_0000_u64);

/// The largest number of encoded nodes one proof may carry.
pub const MAX_PROOF_NODES: NodeCount = NodeCount(0x0000_1000_u64);

/// The largest number of records one proof may materialize in total, summed
/// over every node it carries.
pub const MAX_PROOF_RECORDS: RecordCount = RecordCount(0x0040_0000_u64);
/// The least bytes one encoded record can occupy: two length prefixes and two
/// empty bodies.
pub const LEAST_RECORD_BYTES: EncodedLength = EncodedLength(16_usize);

/// The least bytes one encoded child reference can occupy: a separator length
/// prefix, an empty separator, an identity, and a record count.
pub const LEAST_CHILD_BYTES: EncodedLength = EncodedLength(48_usize);

/// The running total of work one proof has already forced.
///
/// # Specification
/// - requires: one accumulator per proof verification, charged before the work
///   it accounts for is performed.
/// - ensures: after any sequence of charges the recorded totals are the
///   saturated sums of the charged amounts, and a total that reached its
///   ceiling stays refused for every later charge.
/// - provides: the artifact-total bound the per-structure ceilings do not
///   imply. The postcondition stays prose: it ranges over a sequence of
///   charges, and each charging method states its own step below.
/// - fails: [`RecordTreeError::BudgetExceeded`] on the charge that crosses a
///   ceiling.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is the two comparisons against
///   the ceilings, separated by charging exactly to a ceiling (admitted) and
///   one beyond it (refused), plus a saturating charge that would overflow.
/// - witness: `wire::tests::work_admits_charges_up_to_the_ceiling`
/// - witness: `wire::tests::work_refuses_the_charge_past_the_ceiling`
/// - witness: `wire::tests::work_saturates_instead_of_wrapping`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DecodeWork
{
    /// Nodes decoded so far.
    nodes: u64,
    /// Records materialized so far.
    records: u64,
}

impl DecodeWork
{
    /// Starts a fresh accounting.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: both charges are zero, so no earlier decode's work is carried
    ///   into this one.
    /// - provides: the per-decode budget isolation the ceilings are enforced
    ///   against.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            nodes: 0_u64,
            records: 0_u64,
        }
    }

    /// Charges one decoded node.
    ///
    /// # Specification
    /// - requires: one accumulator per proof verification, charged before the
    ///   work it accounts for.
    /// - ensures: `|ret| self.nodes == entry_nodes.saturating_add(1) &&
    ///   ret.is_ok() == (self.nodes <= u64::from(MAX_PROOF_NODES))`, for
    ///   `entry_nodes` the total at entry — the node total is the saturating
    ///   count of every charge, and a total that reached its ceiling stays
    ///   refused.
    /// - fails: [`RecordTreeError::BudgetExceeded`] on the charge that crosses
    ///   [`MAX_PROOF_NODES`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::BudgetExceeded`] — the proof carries more nodes than
    /// [`MAX_PROOF_NODES`] admits.
    #[inline]
    #[spec(
        captures: entry_nodes = self.nodes,
        ensures: |ret| self.nodes == entry_nodes.saturating_add(1_u64)
            && ret.is_ok() == (self.nodes <= u64::from(MAX_PROOF_NODES)),
    )]
    pub fn charge_node(&mut self) -> Result<(), RecordTreeError>
    {
        self.nodes = self.nodes.saturating_add(1_u64);

        if self.nodes > u64::from(MAX_PROOF_NODES) {
            return Err(RecordTreeError::BudgetExceeded {
                context: "proof node count".into(),
            });
        }

        Ok(())
    }

    /// Charges the records one node materialized.
    ///
    /// # Specification
    /// - requires: one accumulator per proof verification, charged before the
    ///   work it accounts for.
    /// - ensures: `|ret| self.records ==
    ///   entry_records.saturating_add(u64::from(count)) && ret.is_ok() ==
    ///   (self.records <= u64::from(MAX_PROOF_RECORDS))`, for `entry_records`
    ///   the total at entry — the record total is the saturating sum of every
    ///   charge, and a total that reached its ceiling stays refused.
    /// - fails: [`RecordTreeError::BudgetExceeded`] on the charge that crosses
    ///   [`MAX_PROOF_RECORDS`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::BudgetExceeded`] — the proof materializes more
    /// records in total than [`MAX_PROOF_RECORDS`] admits.
    #[inline]
    #[spec(
        captures: entry_records = self.records,
        ensures: |ret| self.records == entry_records.saturating_add(u64::from(count))
            && ret.is_ok() == (self.records <= u64::from(MAX_PROOF_RECORDS)),
    )]
    pub fn charge_records(
        &mut self,
        count: RecordCount,
    ) -> Result<(), RecordTreeError>
    {
        self.records = self.records.saturating_add(u64::from(count));

        if self.records > u64::from(MAX_PROOF_RECORDS) {
            return Err(RecordTreeError::BudgetExceeded {
                context: "proof total record count".into(),
            });
        }

        Ok(())
    }

    /// Returns the nodes charged so far.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn nodes(&self) -> NodeCount
    {
        NodeCount(self.nodes)
    }

    /// Returns the records charged so far.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn records(&self) -> RecordCount
    {
        RecordCount(self.records)
    }
}

/// Refuses a proof that the verifier's budgets cannot carry.
///
/// The verifier charges the carried nodes and the records they materialize to
/// [`DecodeWork`], whose ceilings are these same constants; this is the
/// prover's half of that symmetry, so a proof it passes is one the crate's
/// own verifier will not refuse for a budget.
///
/// # Specification
/// - requires: totals charged to one proof's accounting.
/// - ensures: `|ret| ret.is_ok() == (nodes <= MAX_PROOF_NODES && records <=
///   MAX_PROOF_RECORDS)` — reports the totals when both fit the proof budgets.
/// - fails: [`RecordTreeError::BudgetExceeded`] when a total exceeds a budget.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::BudgetExceeded`] — the carried nodes or the records the
/// proof materializes exceed a proof budget.
#[spec(ensures: |ret| ret.is_ok() == (nodes <= MAX_PROOF_NODES && records <= MAX_PROOF_RECORDS))]
pub(crate) fn ensure_proof_budget(
    nodes: NodeCount,
    records: RecordCount,
) -> Result<(), RecordTreeError>
{
    if nodes > MAX_PROOF_NODES {
        return Err(RecordTreeError::BudgetExceeded {
            context: "proof node count".into(),
        });
    }

    if records > MAX_PROOF_RECORDS {
        return Err(RecordTreeError::BudgetExceeded {
            context: "proof total record count".into(),
        });
    }

    Ok(())
}

/// An append-only buffer for canonical encodings.
///
/// Encoding is always append-only and never seeks, so the buffer exposes only
/// the four pushes the formats use.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct WireBuffer(Vec<u8>);

impl WireBuffer
{
    /// Starts an empty buffer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new() -> Self
    {
        Self(Vec::new())
    }

    /// Appends a domain tag.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends exactly the domain's tag bytes, in order, and changes
    ///   nothing already appended.
    /// - provides: the domain prefix a self-describing encoding opens with.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub(crate) fn push_domain(
        &mut self,
        domain: Domain,
    )
    {
        self.0.extend_from_slice(domain.tag().as_ref());
    }

    /// Appends one discriminator byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn push_tag(
        &mut self,
        tag: WireTag,
    )
    {
        self.0.push(u8::from(tag));
    }

    /// Appends one little-endian sixteen-bit field.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the field's two bytes least-significant first, the
    ///   byte order the current encoding version fixes.
    /// - provides: the sixteen-bit field writer, so no caller chooses an
    ///   endianness of its own.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub(crate) fn push_word(
        &mut self,
        value: WireWord,
    )
    {
        self.0
            .extend_from_slice(u16::from(value).to_le_bytes().as_slice());
    }

    /// Appends one little-endian sixty-four-bit field.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the field's eight bytes least-significant first, the
    ///   byte order the current encoding version fixes.
    /// - provides: the sixty-four-bit field writer, so no caller chooses an
    ///   endianness of its own.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub(crate) fn push_long(
        &mut self,
        value: WireLong,
    )
    {
        self.0
            .extend_from_slice(u64::from(value).to_le_bytes().as_slice());
    }

    /// Appends raw bytes with no framing of their own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn push_bytes(
        &mut self,
        bytes: WireBytes<'_>,
    )
    {
        self.0.extend_from_slice(bytes.as_ref());
    }

    /// Appends a node identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn push_hash(
        &mut self,
        hash: NodeHash,
    )
    {
        self.0.extend_from_slice(hash.as_ref());
    }

    /// Appends a sixty-four-bit length prefix followed by the bytes it counts.
    ///
    /// # Specification
    /// - requires: nothing; a run too wide for the prefix is admissible input
    ///   and is refused.
    /// - ensures: on success appends the run's length as a little-endian
    ///   sixty-four-bit field and then the run itself, so a decoder reads the
    ///   count before the bytes it covers; on refusal nothing is appended.
    /// - provides: the one framing every variable-width field uses.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] carrying `context` when
    ///   the run's length exceeds the wire width, so a length is never written
    ///   narrower than the bytes it counts.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::ArithmeticOverflow`] — the byte length exceeds the
    /// wire width.
    #[inline]
    pub(crate) fn push_length_prefixed(
        &mut self,
        bytes: WireBytes<'_>,
        context: FailureContext,
    ) -> Result<(), RecordTreeError>
    {
        let Ok(length) = u64::try_from(bytes.as_ref().len())
        else {
            return Err(RecordTreeError::ArithmeticOverflow { context });
        };

        self.push_long(WireLong::from(length));
        self.push_bytes(bytes);

        Ok(())
    }

    /// Returns the bytes appended so far.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn as_bytes(&self) -> WireBytes<'_>
    {
        WireBytes(self.0.as_slice())
    }
}

impl From<WireBuffer> for Vec<u8>
{
    /// Reads the appended bytes back out as a vector.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(buffer: WireBuffer) -> Self
    {
        buffer.0
    }
}

/// Whether a decoder consumed all of its input.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DecodeCompletion
{
    /// Every byte was consumed.
    Complete,
    /// Bytes remain after the structure ended.
    TrailingBytes,
}

/// A forward-only reader over one canonical encoding.
///
/// Every read is bounds-checked and reports a [`FailureContext`] naming the
/// field that was truncated, so a malformed encoding names its own defect.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Cursor<'bytes>
{
    /// The bytes not yet read.
    remaining: &'bytes [u8],
}

impl<'bytes> Cursor<'bytes>
{
    /// Starts a cursor over `bytes`.
    ///
    /// # Specification
    /// - requires: nothing; empty and malformed input are both admissible.
    /// - ensures: the cursor's unread bytes are exactly `bytes`, in order.
    /// - provides: the forward-only reader every decode is written against.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) const fn new(bytes: WireBytes<'bytes>) -> Self
    {
        Self { remaining: bytes.0 }
    }

    /// Takes exactly `length` bytes.
    ///
    /// # Specification
    /// - requires: at least `length` unread bytes. The precondition stays
    ///   prose: a shortfall is the `- fails:` arm below and not a caller
    ///   violation, so a clause here would turn a documented refusal into an
    ///   abort.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|bytes|
    ///   entry_remaining.get(.. usize::from(length)) == Some(bytes.as_ref()) &&
    ///   entry_remaining.get(usize::from(length) ..) == Some(self.remaining))`,
    ///   for `entry_remaining` the unread bytes at entry — consumes exactly
    ///   `length` bytes and returns them.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   read truncates.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — fewer than `length` bytes remain.
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| ret.as_ref().ok().is_none_or(|bytes| {
            entry_remaining.get(.. usize::from(length)) == Some(bytes.as_ref())
                && entry_remaining.get(usize::from(length) ..) == Some(self.remaining)
        }),
    )]
    pub(crate) fn take(
        &mut self,
        length: EncodedLength,
        context: FailureContext,
    ) -> Result<WireBytes<'bytes>, RecordTreeError>
    {
        let length = usize::from(length);

        if self.remaining.len() < length {
            return Err(RecordTreeError::MalformedNode { context });
        }

        let (head, tail) = self.remaining.split_at(length);
        self.remaining = tail;

        Ok(WireBytes(head))
    }

    /// Takes exactly `LEN` bytes as one fixed-width field.
    ///
    /// # Specification
    /// - requires: at least `LEN` unread bytes, prose for the reason
    ///   [`Cursor::take`] states.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|field| { let field =
    ///   <[u8; LEN]>::from(*field); entry_remaining.get(.. LEN) ==
    ///   Some(field.as_slice()) && entry_remaining.get(LEN ..) ==
    ///   Some(self.remaining) })`, for `entry_remaining` the unread bytes at
    ///   entry — consumes exactly `LEN` bytes and returns them as one field.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   read truncates.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — fewer than `LEN` bytes remain.
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| ret.as_ref().ok().is_none_or(|field| {
            let field = <[u8; LEN]>::from(*field);

            entry_remaining.get(.. LEN) == Some(field.as_slice())
                && entry_remaining.get(LEN ..) == Some(self.remaining)
        }),
    )]
    pub(crate) fn take_array<const LEN: usize>(
        &mut self,
        context: FailureContext,
    ) -> Result<WireArray<LEN>, RecordTreeError>
    {
        let bytes = self.take(EncodedLength(LEN), context)?;
        let mut array = [0_u8; LEN];
        array.copy_from_slice(bytes.as_ref());

        Ok(WireArray(array))
    }

    /// Reads one discriminator byte.
    ///
    /// # Specification
    /// - requires: at least one unread byte, prose for the reason
    ///   [`Cursor::take`] states.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|tag|
    ///   entry_remaining.first().copied() == Some(u8::from(*tag)) &&
    ///   entry_remaining.get(1 ..) == Some(self.remaining))`, for
    ///   `entry_remaining` the unread bytes at entry — consumes the
    ///   discriminator byte and returns it.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   byte is missing.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — the field is truncated.
    #[inline]
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| ret.as_ref().ok().is_none_or(|tag| {
            entry_remaining.first().copied() == Some(u8::from(*tag))
                && entry_remaining.get(1_usize ..) == Some(self.remaining)
        }),
    )]
    pub(crate) fn read_tag(
        &mut self,
        context: FailureContext,
    ) -> Result<WireTag, RecordTreeError>
    {
        let bytes = self.take_array::<1>(context)?;

        Ok(WireTag(u8::from_le_bytes(bytes.0)))
    }

    /// Reads one little-endian sixteen-bit field.
    ///
    /// # Specification
    /// - requires: at least two unread bytes, prose for the reason
    ///   [`Cursor::take`] states.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|value| { let bytes =
    ///   u16::from(*value).to_le_bytes(); entry_remaining.get(.. 2) ==
    ///   Some(bytes.as_slice()) && entry_remaining.get(2 ..) ==
    ///   Some(self.remaining) })`, for `entry_remaining` the unread bytes at
    ///   entry — consumes the field and returns it in host order.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   field is truncated.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — the field is truncated.
    #[inline]
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| ret.as_ref().ok().is_none_or(|value| {
            let bytes = u16::from(*value).to_le_bytes();

            entry_remaining.get(.. 2_usize) == Some(bytes.as_slice())
                && entry_remaining.get(2_usize ..) == Some(self.remaining)
        }),
    )]
    pub(crate) fn read_word(
        &mut self,
        context: FailureContext,
    ) -> Result<WireWord, RecordTreeError>
    {
        let bytes = self.take_array::<2>(context)?;

        Ok(WireWord(u16::from_le_bytes(bytes.0)))
    }

    /// Reads one little-endian sixty-four-bit field.
    ///
    /// # Specification
    /// - requires: at least eight unread bytes, prose for the reason
    ///   [`Cursor::take`] states.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|value| { let bytes =
    ///   u64::from(*value).to_le_bytes(); entry_remaining.get(.. 8) ==
    ///   Some(bytes.as_slice()) && entry_remaining.get(8 ..) ==
    ///   Some(self.remaining) })`, for `entry_remaining` the unread bytes at
    ///   entry — consumes the field and returns it in host order.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   field is truncated.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — the field is truncated.
    #[inline]
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| ret.as_ref().ok().is_none_or(|value| {
            let bytes = u64::from(*value).to_le_bytes();

            entry_remaining.get(.. 8_usize) == Some(bytes.as_slice())
                && entry_remaining.get(8_usize ..) == Some(self.remaining)
        }),
    )]
    pub(crate) fn read_long(
        &mut self,
        context: FailureContext,
    ) -> Result<WireLong, RecordTreeError>
    {
        let bytes = self.take_array::<8>(context)?;

        Ok(WireLong(u64::from_le_bytes(bytes.0)))
    }

    /// Reads a sixty-four-bit length prefix and the bytes it counts.
    ///
    /// # Specification
    /// - requires: a complete length prefix and the bytes it counts, prose for
    ///   the reason [`Cursor::take`] states.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|bytes| { let bytes =
    ///   bytes.as_ref(); let prefix =
    ///   u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes(); let
    ///   consumed = 8.saturating_add(bytes.len()); entry_remaining.get(.. 8) ==
    ///   Some(prefix.as_slice()) && entry_remaining.get(8 .. consumed) ==
    ///   Some(bytes) && entry_remaining.get(consumed ..) ==
    ///   Some(self.remaining) })`, for `entry_remaining` the unread bytes at
    ///   entry — consumes the prefix and exactly the bytes it counts.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   prefix or its bytes truncate; [`RecordTreeError::ArithmeticOverflow`]
    ///   when the prefix exceeds the host width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — the prefix or its bytes are
    /// truncated.
    /// [`RecordTreeError::ArithmeticOverflow`] — the prefix exceeds the host
    /// width.
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| ret.as_ref().ok().is_none_or(|bytes| {
            let bytes = bytes.as_ref();
            let prefix = u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes();
            let consumed = 8_usize.saturating_add(bytes.len());

            entry_remaining.get(.. 8_usize) == Some(prefix.as_slice())
                && entry_remaining.get(8_usize .. consumed) == Some(bytes)
                && entry_remaining.get(consumed ..) == Some(self.remaining)
        }),
    )]
    pub(crate) fn read_length_prefixed(
        &mut self,
        context: FailureContext,
    ) -> Result<WireBytes<'bytes>, RecordTreeError>
    {
        let length = self.read_long(context)?;
        let Ok(length) = usize::try_from(u64::from(length))
        else {
            return Err(RecordTreeError::ArithmeticOverflow { context });
        };

        self.take(EncodedLength(length), context)
    }

    /// Rejects a magic string that does not match `domain`.
    ///
    /// # Specification
    /// - requires: `domain`'s tag unread at the cursor's head, prose for the
    ///   reason [`Cursor::take`] states.
    /// - ensures: `|ret| { let tag = domain.tag(); ret.is_err() ||
    ///   (entry_remaining.get(.. usize::from(tag.len())) == Some(tag.as_ref())
    ///   && entry_remaining.get(usize::from(tag.len()) ..) ==
    ///   Some(self.remaining)) }`, for `entry_remaining` the unread bytes at
    ///   entry — consumes the tag when it matches `domain`.
    /// - fails: [`RecordTreeError::MalformedNode`] naming `context` when the
    ///   tag is truncated or differs.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — the tag is truncated or differs.
    #[spec(
        captures: entry_remaining = self.remaining,
        ensures: |ret| {
            let tag = domain.tag();

            ret.is_err()
                || (entry_remaining.get(.. usize::from(tag.len())) == Some(tag.as_ref())
                    && entry_remaining.get(usize::from(tag.len()) ..) == Some(self.remaining))
        },
    )]
    pub(crate) fn expect_domain(
        &mut self,
        domain: Domain,
        context: FailureContext,
    ) -> Result<(), RecordTreeError>
    {
        let tag = domain.tag();
        let read = self.take(tag.len(), context)?;

        if read.as_ref() != tag.as_ref() {
            return Err(RecordTreeError::MalformedNode { context });
        }

        Ok(())
    }

    /// Reports whether a claimed item count could possibly fit in the bytes
    /// that remain.
    ///
    /// A count read from bytes decides an allocation, so it is checked against
    /// the input that has to carry those items before anything is reserved: an
    /// eight-byte count field otherwise buys an arbitrarily large reservation.
    ///
    /// # Specification
    /// - requires: nothing; `count` is data read from bytes.
    /// - ensures: `|ret| ret.as_ref().ok().is_none_or(|capacity|
    ///   usize::try_from(u64::from(count)) == Ok(usize::from(*capacity)) &&
    ///   usize::from(*capacity).checked_mul(usize::from(least_bytes_each))
    ///   .is_some_and(|least| least <= self.remaining.len()))` — returns the
    ///   count when the remaining bytes could encode its items at
    ///   `least_bytes_each`.
    /// - provides: the reservation bound an allocation-sized field clears
    ///   before any bytes are reserved for its items.
    /// - fails: [`RecordTreeError::ArithmeticOverflow`] naming `context` when
    ///   the count exceeds the host width; [`RecordTreeError::MalformedNode`]
    ///   when the bytes could not carry the items.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::MalformedNode`] — the count exceeds what the
    /// remaining bytes could encode.
    /// [`RecordTreeError::ArithmeticOverflow`] — the count exceeds the host
    /// width.
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|capacity| {
        usize::try_from(u64::from(count)) == Ok(usize::from(*capacity))
            && usize::from(*capacity)
                .checked_mul(usize::from(least_bytes_each))
                .is_some_and(|least| least <= self.remaining.len())
    }))]
    pub(crate) fn admissible_item_count(
        &self,
        count: WireLong,
        least_bytes_each: EncodedLength,
        context: FailureContext,
    ) -> Result<ItemCapacity, RecordTreeError>
    {
        let Ok(count) = usize::try_from(u64::from(count))
        else {
            return Err(RecordTreeError::ArithmeticOverflow { context });
        };
        let Some(least_total) = count.checked_mul(usize::from(least_bytes_each))
        else {
            return Err(RecordTreeError::MalformedNode { context });
        };

        if least_total > self.remaining.len() {
            return Err(RecordTreeError::MalformedNode { context });
        }

        Ok(ItemCapacity(count))
    }

    /// Reports whether every byte has been consumed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`DecodeCompletion::Complete`] exactly when no byte is
    ///   unread, and [`DecodeCompletion::TrailingBytes`] otherwise.
    /// - provides: the trailing-byte check a decoder ends on, so bytes past a
    ///   complete structure are refused rather than ignored.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) const fn completion(&self) -> DecodeCompletion
    {
        if self.remaining.is_empty() {
            DecodeCompletion::Complete
        }
        else {
            DecodeCompletion::TrailingBytes
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use super::Cursor;
    use super::DecodeCompletion;
    use super::DecodeWork;
    use super::Domain;
    use super::EncodedLength;
    use super::ItemCapacity;
    use super::MAX_PROOF_NODES;
    use super::MAX_PROOF_RECORDS;
    use super::NodeCount;
    use super::WireBuffer;
    use super::WireBytes;
    use super::WireLong;
    use super::WireTag;
    use super::WireWord;
    use super::digest;
    use super::ensure_proof_budget;
    use crate::error::RecordTreeError;
    use crate::record::RecordCount;

    const DOMAINS: [Domain; 4] = [Domain::Node, Domain::Root, Domain::Record, Domain::Boundary];

    #[test]
    fn domain_tags_are_distinct_and_prefix_free()
    {
        for (left_index, left) in DOMAINS.iter().enumerate() {
            for (right_index, right) in DOMAINS.iter().enumerate() {
                if left_index == right_index {
                    continue;
                }

                assert_ne!(left.tag(), right.tag());
                assert!(!left.tag().as_ref().starts_with(right.tag().as_ref()));
            }

            assert_ne!(left.tag().len(), EncodedLength::from(0_usize));
        }
    }

    #[test]
    fn digests_of_one_body_differ_across_domains()
    {
        let body = WireBytes::from(b"the same bytes under two languages".as_slice());

        assert_ne!(digest(Domain::Node, body), digest(Domain::Record, body));
        assert_eq!(digest(Domain::Node, body), digest(Domain::Node, body));
    }

    #[test]
    fn work_admits_charges_up_to_the_ceiling()
    {
        let mut work = DecodeWork::new();

        assert_eq!(work.charge_records(MAX_PROOF_RECORDS), Ok(()));
        assert_eq!(work.records(), MAX_PROOF_RECORDS);
        assert_eq!(work.charge_node(), Ok(()));
        assert_eq!(u64::from(work.nodes()), 1_u64);
    }

    #[test]
    fn work_refuses_the_charge_past_the_ceiling()
    {
        let mut work = DecodeWork::new();
        assert_eq!(work.charge_records(MAX_PROOF_RECORDS), Ok(()));

        assert_eq!(
            work.charge_records(RecordCount::from(1_u64)),
            Err(RecordTreeError::BudgetExceeded {
                context: "proof total record count".into(),
            })
        );
    }

    #[test]
    fn work_saturates_instead_of_wrapping()
    {
        let mut work = DecodeWork::new();
        let _first = work.charge_records(RecordCount::from(u64::MAX));

        assert_eq!(
            work.charge_records(RecordCount::from(u64::MAX)),
            Err(RecordTreeError::BudgetExceeded {
                context: "proof total record count".into(),
            })
        );
        assert_eq!(u64::from(work.records()), u64::MAX);
    }

    #[test]
    fn node_charges_stop_at_their_own_ceiling()
    {
        let mut work = DecodeWork::new();

        for _ in 0_u64 .. u64::from(MAX_PROOF_NODES) {
            assert_eq!(work.charge_node(), Ok(()));
        }

        assert_eq!(
            work.charge_node(),
            Err(RecordTreeError::BudgetExceeded {
                context: "proof node count".into(),
            })
        );
    }

    #[test]
    fn the_prover_budget_admits_the_ceiling()
    {
        assert_eq!(
            ensure_proof_budget(MAX_PROOF_NODES, MAX_PROOF_RECORDS),
            Ok(())
        );
    }

    #[test]
    fn the_prover_budget_refuses_the_node_ceiling_plus_one()
    {
        let nodes = NodeCount::from(u64::from(MAX_PROOF_NODES).saturating_add(0x01_u64));

        assert_eq!(
            ensure_proof_budget(nodes, RecordCount::ZERO),
            Err(RecordTreeError::BudgetExceeded {
                context: "proof node count".into(),
            })
        );
    }

    #[test]
    fn the_prover_budget_refuses_the_record_ceiling_plus_one()
    {
        let records = RecordCount::from(u64::from(MAX_PROOF_RECORDS).saturating_add(0x01_u64));

        assert_eq!(
            ensure_proof_budget(MAX_PROOF_NODES, records),
            Err(RecordTreeError::BudgetExceeded {
                context: "proof total record count".into(),
            })
        );
    }

    #[test]
    fn cursor_reads_what_the_buffer_wrote()
    {
        let mut buffer = WireBuffer::new();
        buffer.push_domain(Domain::Node);
        buffer.push_word(WireWord::from(7_u16));
        buffer.push_tag(WireTag::from(3_u8));
        buffer.push_long(WireLong::from(11_u64));
        buffer
            .push_length_prefixed(WireBytes::from(b"payload".as_slice()), "payload".into())
            .expect("the payload length fits");

        let bytes = buffer.as_bytes();
        let mut cursor = Cursor::new(bytes);
        cursor
            .expect_domain(Domain::Node, "domain".into())
            .expect("the domain matches");
        assert_eq!(
            cursor.read_word("version".into()),
            Ok(WireWord::from(7_u16))
        );
        assert_eq!(cursor.read_tag("kind".into()), Ok(WireTag::from(3_u8)));
        assert_eq!(cursor.read_long("count".into()), Ok(WireLong::from(11_u64)));
        assert_eq!(
            cursor.read_length_prefixed("payload".into()),
            Ok(WireBytes::from(b"payload".as_slice()))
        );
        assert_eq!(cursor.completion(), DecodeCompletion::Complete);
    }

    #[test]
    fn cursor_refuses_a_wrong_domain()
    {
        let mut buffer = WireBuffer::new();
        buffer.push_domain(Domain::Record);

        let bytes = buffer.as_bytes();
        let mut cursor = Cursor::new(bytes);

        assert_eq!(
            cursor.expect_domain(Domain::Node, "domain".into()),
            Err(RecordTreeError::MalformedNode {
                context: "domain".into(),
            })
        );
    }

    #[test]
    fn cursor_refuses_a_count_the_bytes_cannot_carry()
    {
        let bytes = vec![0_u8; 4_usize];
        let cursor = Cursor::new(WireBytes::from(bytes.as_slice()));

        assert_eq!(
            cursor.admissible_item_count(
                WireLong::from(3_u64),
                EncodedLength::from(2_usize),
                "items".into()
            ),
            Err(RecordTreeError::MalformedNode {
                context: "items".into(),
            })
        );
        assert_eq!(
            cursor
                .admissible_item_count(
                    WireLong::from(2_u64),
                    EncodedLength::from(2_usize),
                    "items".into()
                )
                .map(usize::from),
            Ok(2_usize)
        );
    }

    #[test]
    fn cursor_reports_trailing_bytes()
    {
        let bytes = vec![1_u8, 2_u8];
        let mut cursor = Cursor::new(WireBytes::from(bytes.as_slice()));
        let _first = cursor.read_tag("byte".into()).expect("one byte remains");

        assert_eq!(cursor.completion(), DecodeCompletion::TrailingBytes);
    }

    #[test]
    fn item_capacity_is_the_checked_count()
    {
        let bytes = vec![0_u8; 16_usize];
        let cursor = Cursor::new(WireBytes::from(bytes.as_slice()));
        let capacity = cursor
            .admissible_item_count(
                WireLong::from(4_u64),
                EncodedLength::from(4_usize),
                "items".into(),
            )
            .expect("the bytes carry four items of four bytes");

        assert_eq!(capacity, ItemCapacity::from(4_usize));
    }

    #[test]
    fn the_wire_round_trip_pins_little_endian_bytes()
    {
        let mut buffer = WireBuffer::new();
        buffer.push_word(WireWord::from(0x0102_u16));
        buffer.push_long(WireLong::from(0x0102_0304_0506_0708_u64));

        let bytes: Vec<u8> = buffer.into();
        // The literal is the little-endian byte order the wire format
        // promises, asserted byte for byte on every host endianness,
        // then read back through the cursor: the round trip must
        // answer the exact values pushed.
        assert_eq!(bytes, vec![
            0x02, 0x01, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01
        ]);

        let mut cursor = Cursor::new(WireBytes::from(bytes.as_slice()));
        assert_eq!(
            cursor.read_word("word".into()),
            Ok(WireWord::from(0x0102_u16))
        );
        assert_eq!(
            cursor.read_long("long".into()),
            Ok(WireLong::from(0x0102_0304_0506_0708_u64))
        );
    }
}
