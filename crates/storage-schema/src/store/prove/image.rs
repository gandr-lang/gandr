//! A proof's image: what a reader on another endpoint receives.
//!
//! # The image
//!
//! ```text
//! image     := u64le manifest length || manifest image
//!           || evidence
//!           || u64le node count || node*
//! evidence  := 0x01 || u64le value length || value      the answering record
//!            | 0x02 || neighbour || neighbour           an absent key's predecessor, then successor
//!            | 0x03 || u64le record count || record*    the answering run
//! neighbour := 0x00 | 0x01 || record
//! record    := u64le key length || key || u64le value length || value
//! node      := u64le node length || node image
//! ```
//!
//! **Choice: the image carries what the reader can't compute, and nothing
//! it can.** A record-plane proof is its envelope, its root node, the key or
//! range it answers at, its claimed records and its node images. The image
//! carries the manifest, the claimed records and the node images. The reader
//! derives the rest itself. The key or range comes from its own question and
//! schema. The table's root and root node come from the manifest under the
//! reader's parameters. Each node's identity is hashed from the node's bytes.
//! So a decoded proof is the proof [`Store::prove`] made, and a forged part
//! is refused by verification rather than trusted by decoding.
//!
//! The framing follows the manifest's: fixed-width little-endian integers,
//! with each variable field preceded by its length. Counts read from the
//! image are untrusted, so the decoder grows each list only as far as the
//! bytes actually present.
//!
//! **Alternatives.** An image that carries its question and site is
//! self-describing. But the reader has to compare them with its own question
//! anyway, and the verifier would ignore the bytes. **Reversal.** A holder
//! that sends proofs to questions the reader didn't ask, as a subscription
//! would. There the image has to name its question.
//!
//! [`Store::prove`]: crate::Store::prove

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_records::EncodedNode;
use gandr_storage_records::MembershipProof;
use gandr_storage_records::NonMembershipEvidence;
use gandr_storage_records::NonMembershipProof;
use gandr_storage_records::OwnedKeyRange;
use gandr_storage_records::ProofEnvelope;
use gandr_storage_records::ProofKind;
use gandr_storage_records::ProofNode;
use gandr_storage_records::RangeProof;
use gandr_storage_records::Record;
use gandr_storage_records::TreeParams;
use gandr_storage_records::hash_node;

use super::Evidence;
use super::Proof;
use super::Question;
use super::site;
use crate::error::ProofFault;
use crate::error::StoreError;
use crate::manifest::ManifestImage;
use crate::manifest::StoreManifest;
use crate::schema::Schema;

/// The evidence tag of a present record.
const PRESENT: u8 = 0x01_u8;
/// The evidence tag of an absent key.
const ABSENT: u8 = 0x02_u8;
/// The evidence tag of a run.
const RUN: u8 = 0x03_u8;
/// The tag of a side with no neighbour.
const NO_NEIGHBOUR: u8 = 0x00_u8;
/// The tag of a side with a neighbour.
const NEIGHBOUR: u8 = 0x01_u8;

/// A proof image, borrowed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProofImage<'image>(&'image [u8]);

impl<'image> From<&'image [u8]> for ProofImage<'image>
{
    /// Reads bytes as a candidate image; [`Proof::decode`] decides.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'image [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ProofImage<'_>
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// A proof image, owned.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProofImageBuf(Box<[u8]>);

impl AsRef<[u8]> for ProofImageBuf
{
    /// Borrows the image bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// An image under construction.
#[repr(transparent)]
struct Writer(Vec<u8>);

impl Writer
{
    /// Appends a length or a count as `u64le`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn length(
        &mut self,
        length: Length,
    )
    {
        // Anything held in memory has a length that fits sixty-four bits on
        // every supported target.
        let length = u64::try_from(length.0).unwrap_or(u64::MAX);
        self.0.extend_from_slice(&length.to_le_bytes());
    }

    /// Appends a field's length, then its bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn framed(
        &mut self,
        body: Body<'_>,
    )
    {
        self.length(Length(body.0.len()));
        self.0.extend_from_slice(body.0);
    }

    /// Appends a record's key, then its value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn record(
        &mut self,
        record: &Record,
    )
    {
        self.framed(Body(record.key().as_ref()));
        self.framed(Body(record.value().as_ref()));
    }

    /// Appends one side of an absent key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn neighbour(
        &mut self,
        neighbour: Option<&Record>,
    )
    {
        match neighbour {
            None => self.0.push(NO_NEIGHBOUR),
            Some(record) => {
                self.0.push(NEIGHBOUR);
                self.record(record);
            },
        }
    }

    /// Appends the node images in proof order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn nodes(
        &mut self,
        nodes: &[ProofNode],
    )
    {
        self.length(Length(nodes.len()));
        for node in nodes {
            self.framed(Body(node.bytes().as_ref()));
        }
    }
}

impl Proof
{
    /// The proof's image.
    ///
    /// # Specification
    /// - ensures: the bytes are the layout the module documentation states;
    ///   [`Proof::decode`] under the proof's question, the store's schema and
    ///   its parameters returns this proof.
    /// - panics: none.
    /// - executable: none — the layout's independent statement is the round
    ///   trip and the golden prefix the witnesses pin.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — every kind of question round-trips to an equal
    ///   proof that verifies to the store's answer; the image opens with the
    ///   framed manifest and its evidence tag.
    /// - witness: `tests::proofs::every_kind_of_proof_round_trips_through_its_image`
    #[inline]
    #[must_use]
    pub fn encode(&self) -> ProofImageBuf
    {
        let manifest = self.manifest.encode();
        let mut image = Writer(Vec::new());
        image.framed(Body(manifest.as_ref()));
        match self.evidence {
            Evidence::Present(ref proof) => {
                image.0.push(PRESENT);
                image.framed(Body(proof.value().as_ref()));
                image.nodes(proof.nodes());
            },
            Evidence::Absent(ref proof) => {
                image.0.push(ABSENT);
                image.neighbour(proof.evidence().predecessor());
                image.neighbour(proof.evidence().successor());
                image.nodes(proof.nodes());
            },
            Evidence::Run(ref proof) => {
                image.0.push(RUN);
                image.length(Length(proof.records().len()));
                for record in proof.records() {
                    image.record(record);
                }
                image.nodes(proof.nodes());
            },
        }
        ProofImageBuf(image.0.into_boxed_slice())
    }

    /// Reads a proof back from its image, for the reader's question.
    ///
    /// # Specification
    /// - requires: nothing; any bytes are admitted as input.
    /// - ensures: on success the proof answers `question`, its image is `image`
    ///   byte for byte, and its record-plane proof is bound to the table root
    ///   the carried manifest names under `params`. It isn't yet checked
    ///   against any store root: [`Proof::verify`] does that.
    /// - fails: [`StoreError::Proof`] naming the first part, in image order,
    ///   that is cut short or carries an unknown tag, then trailing bytes;
    ///   [`StoreError::Manifest`] for a malformed carried manifest;
    ///   [`StoreError::SchemaMismatch`], [`StoreError::ProfileMismatch`] and
    ///   [`StoreError::TableCount`] for a manifest of another reader;
    ///   [`StoreError::WrongQuestion`] for evidence of a kind that can't answer
    ///   `question`; and the refusals [`Store::prove`] gives for a question the
    ///   schema refuses.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — every kind of question round-trips; every proper
    ///   prefix is refused as cut short, an unknown tag and a trailing byte by
    ///   name, and a run offered for a single cell as the wrong question.
    /// - witness: `tests::proofs::every_kind_of_proof_round_trips_through_its_image`
    /// - witness: `tests::proofs::a_malformed_proof_image_is_refused_by_part`
    ///
    /// [`Store::prove`]: crate::Store::prove
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |proof| proof.question == *question && proof.encode().as_ref() == image.as_ref()))]
    pub fn decode(
        image: ProofImage<'_>,
        schema: &Schema,
        params: TreeParams,
        question: &Question,
    ) -> Result<Self, StoreError>
    {
        let mut cursor = Cursor(image.0);
        let manifest = cursor.framed()?;
        let manifest = StoreManifest::decode(ManifestImage::from(manifest.0))?;
        manifest.ensure_reader(schema, params)?;
        let site = site(schema, question)?;
        let tree_root = manifest.tree_root(site.object, params)?;
        let root_node = manifest
            .tables()
            .get(usize::from(site.object))
            .ok_or(StoreError::TableCount)?
            .root_node();

        let Field([tag]) = cursor.chunk::<1>()?;
        let evidence = match (tag, question) {
            (
                PRESENT,
                &Question::Part { .. } | &Question::Arrow { .. } | &Question::Value { .. },
            ) => {
                let value = cursor.framed()?.0;
                let nodes = cursor.nodes()?;
                Evidence::Present(MembershipProof::new(
                    ProofEnvelope::new(tree_root, ProofKind::Membership),
                    root_node,
                    site.key,
                    value,
                    nodes,
                ))
            },
            (ABSENT, &Question::Part { .. }) => {
                let predecessor = cursor.neighbour()?;
                let successor = cursor.neighbour()?;
                let nodes = cursor.nodes()?;
                Evidence::Absent(NonMembershipProof::new(
                    ProofEnvelope::new(tree_root, ProofKind::NonMembership),
                    root_node,
                    site.key,
                    NonMembershipEvidence::new(predecessor.0, successor.0),
                    nodes,
                ))
            },
            (RUN, &Question::Preimage { .. } | &Question::ValuePreimage { .. }) => {
                let range = OwnedKeyRange::from_range(site.range()?);
                let count = cursor.length()?;
                let mut records = Vec::new();
                for _record in 0_usize .. count.0 {
                    records.push(cursor.record()?);
                }
                let nodes = cursor.nodes()?;
                Evidence::Run(RangeProof::new(
                    ProofEnvelope::new(tree_root, ProofKind::Range),
                    root_node,
                    range,
                    records,
                    nodes,
                ))
            },
            (PRESENT | ABSENT | RUN, _) => return Err(StoreError::WrongQuestion),
            _unknown => return Err(fault(ProofFault::Tag)),
        };
        if !cursor.0.is_empty() {
            return Err(fault(ProofFault::Trailing));
        }
        Ok(Self {
            manifest,
            question: question.clone(),
            evidence,
        })
    }
}

/// The proof-fault refusal.
///
/// # Specification
/// trivial.
#[inline]
const fn fault(fault: ProofFault) -> StoreError
{
    StoreError::Proof { fault }
}

/// A length or a count read from or written to an image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Length(usize);

/// The fixed-width bytes of one field.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Field<const WIDTH: usize>([u8; WIDTH]);

/// One side of an absent key, as the image claims it.
#[repr(transparent)]
struct Neighbour(Option<Record>);

/// The bytes of one framed field.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Body<'body>(&'body [u8]);

/// A read position in a proof image.
#[repr(transparent)]
struct Cursor<'image>(&'image [u8]);

impl<'image> Cursor<'image>
{
    /// Consumes a fixed-width field.
    ///
    /// # Specification
    /// - ensures: on success the next `WIDTH` bytes, consumed.
    /// - fails: [`ProofFault::Truncated`] when fewer remain.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the round trip is
    ///   its independent observation.
    ///
    /// # Errors
    /// [`StoreError::Proof`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every proper prefix of an image is refused as cut
    ///   short.
    /// - witness: `tests::proofs::a_malformed_proof_image_is_refused_by_part`
    #[inline]
    fn chunk<const WIDTH: usize>(&mut self) -> Result<Field<WIDTH>, StoreError>
    {
        let (bytes, rest) = self
            .0
            .split_first_chunk::<WIDTH>()
            .ok_or(fault(ProofFault::Truncated))?;
        self.0 = rest;
        Ok(Field(*bytes))
    }

    /// Consumes a `u64le` length that this target can hold.
    ///
    /// # Specification
    /// - ensures: on success the length the eight bytes state.
    /// - fails: [`ProofFault::Truncated`] when fewer remain or the length
    ///   exceeds this target's `usize`.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the round trip is
    ///   its independent observation.
    ///
    /// # Errors
    /// [`StoreError::Proof`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every proper prefix of an image is refused as cut
    ///   short.
    /// - witness: `tests::proofs::a_malformed_proof_image_is_refused_by_part`
    #[inline]
    fn length(&mut self) -> Result<Length, StoreError>
    {
        let bytes = self.chunk::<8>()?;
        usize::try_from(u64::from_le_bytes(bytes.0))
            .map(Length)
            .map_err(|_overflow| fault(ProofFault::Truncated))
    }

    /// Consumes a length, then that many bytes.
    ///
    /// # Specification
    /// - ensures: on success the field's bytes, consumed with their length.
    /// - fails: [`ProofFault::Truncated`] when fewer bytes remain than the
    ///   length states.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the round trip is
    ///   its independent observation.
    ///
    /// # Errors
    /// [`StoreError::Proof`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every proper prefix of an image is refused as cut
    ///   short.
    /// - witness: `tests::proofs::a_malformed_proof_image_is_refused_by_part`
    #[inline]
    fn framed(&mut self) -> Result<Body<'image>, StoreError>
    {
        let length = self.length()?;
        let (bytes, rest) = self
            .0
            .split_at_checked(length.0)
            .ok_or(fault(ProofFault::Truncated))?;
        self.0 = rest;
        Ok(Body(bytes))
    }

    /// Consumes a record's key, then its value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn record(&mut self) -> Result<Record, StoreError>
    {
        let key = self.framed()?;
        let value = self.framed()?;
        Ok(Record::new(key.0, value.0))
    }

    /// Consumes one side of an absent key.
    ///
    /// # Specification
    /// - ensures: on success the claimed neighbour, or none.
    /// - fails: [`ProofFault::Tag`] for a tag other than none or one record;
    ///   [`ProofFault::Truncated`] when the record is cut short.
    /// - panics: none.
    /// - executable: none — the value is the decoding itself; the round trip is
    ///   its independent observation.
    ///
    /// # Errors
    /// [`StoreError::Proof`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dead part's proof round-trips with its neighbours;
    ///   a changed neighbour tag is refused by name.
    /// - witness: `tests::proofs::a_malformed_proof_image_is_refused_by_part`
    #[inline]
    fn neighbour(&mut self) -> Result<Neighbour, StoreError>
    {
        let Field([tag]) = self.chunk::<1>()?;
        match tag {
            NO_NEIGHBOUR => Ok(Neighbour(None)),
            NEIGHBOUR => Ok(Neighbour(Some(self.record()?))),
            _unknown => Err(fault(ProofFault::Tag)),
        }
    }

    /// Consumes the node images and hashes each one's identity from its
    /// bytes.
    ///
    /// # Specification
    /// - ensures: on success the nodes in image order, no identity taken from
    ///   the image.
    /// - fails: [`ProofFault::Truncated`] when a node is cut short.
    /// - panics: none.
    /// - executable: none — the identities are checked by the record plane's
    ///   verification walking them from the table root.
    ///
    /// # Errors
    /// [`StoreError::Proof`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every decoded proof verifies to the store's answer.
    /// - witness: `tests::proofs::every_kind_of_proof_round_trips_through_its_image`
    #[inline]
    fn nodes(&mut self) -> Result<Box<[ProofNode]>, StoreError>
    {
        let count = self.length()?;
        // The count is untrusted: grow only by nodes actually present.
        let mut nodes = Vec::new();
        for _node in 0_usize .. count.0 {
            let body = self.framed()?;
            nodes.push(ProofNode::new(hash_node(EncodedNode::from(body.0)), body.0));
        }
        Ok(nodes.into_boxed_slice())
    }
}
