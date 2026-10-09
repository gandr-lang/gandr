//! The artifact manifest: what names a committed kernel artifact, as a byte
//! image and an identity.
//!
//! # The image
//!
//! ```text
//! image    := "gandr:storage-artifact:manifest:v1"
//!          || u16le manifest version
//!          || u16le kernel format version
//!          || u64le commitment length || boundary commitment
//!          || u64le record count
//!          || 32-byte root node identity
//! identity := BLAKE3(image)
//! ```
//!
//! Every integer is little-endian at a fixed width and the domain is inside
//! the hashed bytes, so an artifact identity, a value manifest digest and a
//! record-plane node identity never hash the same preimage. The decoder admits
//! exactly the images the encoder writes, so a manifest decoded from bytes
//! re-encodes to those bytes and its identity is their BLAKE3.
//!
//! # What the identity binds
//!
//! The boundary commitment is the record plane's own
//! ([`TreeParams::boundary_commitment`]), carried opaque; the root node's
//! bytes carry the record encoding version, so the node identity binds it.
//! The kernel format version names which canonical encoding the records
//! carry. A matching identity is provenance, never validity:
//! [`ArtifactManifest::read_under`] hands the reassembled bytes to the
//! kernel's decoder, which refuses what it refuses whatever the identity.
//!
//! # Refusal order
//!
//! [`ArtifactManifest::decode`] reads the fields in image order and refuses at
//! the first that is foreign, unknown or cut short, then refuses trailing
//! bytes. [`ArtifactManifest::read_under`] refuses a kernel format or a
//! boundary commitment the reader does not share before the store is asked
//! for anything; then the record plane's refusals for a node the store cannot
//! authenticate; then a tree the records do not rebuild; then a misplaced key;
//! then the kernel's decoder; then a record cut off a segment boundary.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_term::DecodedArtifact;
use gandr_kernel_term::FORMAT_VERSION;
use gandr_kernel_term::FormatVersion;
use gandr_kernel_term::decode;
use gandr_storage_records::BlockStore;
use gandr_storage_records::DecodeWork;
use gandr_storage_records::DecodedNode;
use gandr_storage_records::NodeHash;
use gandr_storage_records::ProfileCommitment;
use gandr_storage_records::Record;
use gandr_storage_records::RecordCount;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use gandr_storage_records::TreeRoot;
use gandr_storage_records::decode_node;

use crate::error::ArtifactError;
use crate::error::ManifestField;
use crate::record::ArtifactRecordSet;

/// The domain every manifest image opens with, inside the hashed preimage.
pub const MANIFEST_DOMAIN: &[u8] = b"gandr:storage-artifact:manifest:v1";

/// The byte length of an [`ArtifactIdentity`]: one BLAKE3 output.
pub const ARTIFACT_IDENTITY_LEN: usize = 0x20_usize;

/// The byte length of a root node identity.
const ROOT_NODE_LEN: usize = 0x20_usize;

/// The image's fixed-width fields after the domain, the commitment aside: the
/// two versions, the commitment length, the record count and the root node.
const MANIFEST_FIXED_LEN: usize = 0x34_usize;

/// The layout version of an artifact manifest.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArtifactManifestVersion(u16);

impl ArtifactManifestVersion
{
    /// The manifest layout this build names artifacts under.
    pub const V1: Self = Self(1_u16);
}

impl From<u16> for ArtifactManifestVersion
{
    /// Reads the number as a manifest layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: u16) -> Self
    {
        Self(version)
    }
}

impl From<ArtifactManifestVersion> for u16
{
    /// Reads the version back out as its number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: ArtifactManifestVersion) -> Self
    {
        version.0
    }
}

/// The BLAKE3 identity of one artifact manifest image.
///
/// Deliberately its own type, with no conversion to a value manifest's digest
/// or a record-plane node identity: the three name different things under
/// different domains, and a signature taking one never accepts another.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArtifactIdentity([u8; ARTIFACT_IDENTITY_LEN]);

impl From<[u8; ARTIFACT_IDENTITY_LEN]> for ArtifactIdentity
{
    /// Reads thirty-two bytes as an artifact identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; ARTIFACT_IDENTITY_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ArtifactIdentity
{
    /// Borrows the identity's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl fmt::Display for ArtifactIdentity
{
    /// Writes the identity as lowercase hexadecimal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes two lowercase hexadecimal digits per byte, in byte
    ///   order, sixty-four in all.
    /// - provides: the spelling a refusal or a log line names an artifact by.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

impl fmt::Debug for ArtifactIdentity
{
    /// Writes the identity as its type name around its hexadecimal spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "ArtifactIdentity({self})")
    }
}

/// Borrowed bytes offered to [`ArtifactManifest::decode`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ManifestImage<'image>(&'image [u8]);

impl<'image> From<&'image [u8]> for ManifestImage<'image>
{
    /// Reads a byte slice as a manifest image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'image [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ManifestImage<'_>
{
    /// Borrows the image's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// The owned image [`ArtifactManifest::encode`] writes.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ManifestImageBuf(Box<[u8]>);

impl AsRef<[u8]> for ManifestImageBuf
{
    /// Borrows the image's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

impl ManifestImageBuf
{
    /// Borrows the image for [`ArtifactManifest::decode`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_image(&self) -> ManifestImage<'_>
    {
        ManifestImage(&self.0)
    }
}

/// The identity of one committed kernel artifact: the kernel format its
/// records carry, the boundary commitment its tree was cut under, the records
/// it holds and the root node they hang from.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ArtifactManifest
{
    /// The manifest layout version.
    manifest_version: ArtifactManifestVersion,
    /// The kernel format version the records carry.
    kernel_format: FormatVersion,
    /// The record plane's boundary commitment the tree was cut under.
    commitment: ProfileCommitment,
    /// The records the tree holds: the header and one per declaration.
    record_count: RecordCount,
    /// The root node's identity.
    root_node: NodeHash,
}

impl ArtifactManifest
{
    /// Names one committed artifact.
    ///
    /// # Specification
    /// - requires: the fields describe one record tree: `commitment` is the
    ///   boundary commitment of the parameters it was built under,
    ///   `record_count` its records and `root_node` its root node's identity.
    /// - ensures: the manifest carries them unchanged at
    ///   [`ArtifactManifestVersion::V1`]. The clause checks every field but the
    ///   commitment, which the constructor takes by value.
    /// - provides: the description [`crate::build`] returns.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.kernel_format == kernel_format
        && ret.record_count == record_count
        && ret.root_node == root_node
        && ret.manifest_version == ArtifactManifestVersion::V1)]
    pub fn new(
        kernel_format: FormatVersion,
        commitment: ProfileCommitment,
        record_count: RecordCount,
        root_node: NodeHash,
    ) -> Self
    {
        Self {
            manifest_version: ArtifactManifestVersion::V1,
            kernel_format,
            commitment,
            record_count,
            root_node,
        }
    }

    /// Returns the manifest layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn manifest_version(&self) -> ArtifactManifestVersion
    {
        self.manifest_version
    }

    /// Returns the kernel format version the records carry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kernel_format(&self) -> FormatVersion
    {
        self.kernel_format
    }

    /// Returns the boundary commitment the tree was cut under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn commitment(&self) -> &ProfileCommitment
    {
        &self.commitment
    }

    /// Returns the records the tree holds: the header and one per
    /// declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn record_count(&self) -> RecordCount
    {
        self.record_count
    }

    /// Returns the root node's identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node(&self) -> NodeHash
    {
        self.root_node
    }

    /// Writes the manifest's image: the domain, then every field in fixed
    /// order and width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the image is [`MANIFEST_DOMAIN`] followed by the fields in
    ///   the order and widths this module documents, every integer
    ///   little-endian; [`ArtifactManifest::decode`] reads it back as `self`.
    /// - provides: the bytes a consumer stores and sends, and the preimage of
    ///   [`ArtifactManifest::identity`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — one manifest's image read back field by
    ///   field against bytes written out by hand, and decoded back equal.
    /// - witness: `manifest::tests::the_manifest_layout_is_golden`
    /// - witness: `manifest::tests::the_manifest_round_trips_through_decode`
    #[inline]
    #[must_use]
    // The round trip is checked from decode's side alone: an encode predicate
    // calling decode would recurse through decode's own predicate.
    #[spec(ensures: |ret| ret.as_ref().starts_with(MANIFEST_DOMAIN)
        && ret.as_ref().len() == MANIFEST_DOMAIN
            .len()
            .saturating_add(MANIFEST_FIXED_LEN)
            .saturating_add(self.commitment.as_ref().len()))]
    pub fn encode(&self) -> ManifestImageBuf
    {
        let commitment: &[u8] = self.commitment.as_ref();
        // A commitment is held in memory, so its length fits sixty-four bits on
        // every target Rust supports.
        let commitment_length = u64::try_from(commitment.len()).unwrap_or(u64::MAX);
        let mut image = Vec::with_capacity(
            MANIFEST_DOMAIN
                .len()
                .saturating_add(MANIFEST_FIXED_LEN)
                .saturating_add(commitment.len()),
        );
        image.extend_from_slice(MANIFEST_DOMAIN);
        image.extend_from_slice(u16::from(self.manifest_version).to_le_bytes().as_slice());
        image.extend_from_slice(u16::from(self.kernel_format).to_le_bytes().as_slice());
        image.extend_from_slice(commitment_length.to_le_bytes().as_slice());
        image.extend_from_slice(commitment);
        image.extend_from_slice(u64::from(self.record_count).to_le_bytes().as_slice());
        image.extend_from_slice(self.root_node.as_ref());

        ManifestImageBuf(image.into_boxed_slice())
    }

    /// Reads a manifest image, refusing every image the encoder would not
    /// write.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: on success the manifest whose [`ArtifactManifest::encode`] is
    ///   exactly `image`.
    /// - provides: the only way from bytes to a manifest; the cursor reads each
    ///   field once, front to back, with no recursion, and checks a declared
    ///   length against the bytes that remain before reading under it.
    /// - fails: in image order, [`ArtifactError::MalformedManifest`] naming a
    ///   foreign domain or a manifest version other than one;
    ///   [`ArtifactError::TruncatedManifest`] naming the field the image ends
    ///   inside, the commitment when its declared length passes the image's
    ///   end; then [`ArtifactError::TrailingManifestBytes`] for bytes past the
    ///   root node identity. Every kernel format version and every commitment
    ///   is admitted; whether the reader shares them is
    ///   [`ArtifactManifest::read_under`]'s question.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — the golden decodes from its own image —
    ///   plus L3 for each refusal: an unknown manifest version, a foreign
    ///   domain, one byte short and one byte over, a commitment length past the
    ///   image's end, and every proper prefix of the golden.
    /// - witness: `manifest::tests::the_manifest_round_trips_through_decode`
    /// - witness: `manifest::tests::an_unknown_manifest_version_is_refused`
    /// - witness: `manifest::tests::a_malformed_manifest_is_rejected`
    /// - witness: `manifest::tests::a_bad_commitment_length_is_rejected`
    /// - witness: `manifest::tests::truncation_at_every_prefix_is_rejected`
    #[inline]
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|manifest| manifest.encode().as_ref() == image.as_ref()))]
    pub fn decode(image: ManifestImage<'_>) -> Result<Self, ArtifactError>
    {
        let mut cursor = ManifestCursor(image.0);
        cursor.domain()?;
        let manifest_version = cursor.manifest_version()?;
        let kernel_format = cursor.kernel_format()?;
        let commitment = cursor.commitment()?;
        let record_count = cursor.record_count()?;
        let root_node = cursor.root_node()?;
        cursor.finish()?;

        Ok(Self {
            manifest_version,
            kernel_format,
            commitment,
            record_count,
            root_node,
        })
    }

    /// Names the manifest: BLAKE3 over its whole image, domain included.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the identity is BLAKE3 over [`ArtifactManifest::encode`]'s
    ///   image, so two manifests share an identity exactly when every field
    ///   agrees, up to BLAKE3 collisions.
    /// - provides: the name a consumer stores to refer to a committed artifact,
    ///   and the one identity the artifact layer mints.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — the golden's identity against a digest an
    ///   independent BLAKE3 tool computed over its hand-built image — plus L3
    ///   for binding: one manifest per field, each moving the identity.
    /// - witness: `manifest::tests::the_identity_is_blake3_of_the_canonical_bytes`
    /// - witness: `manifest::tests::any_field_perturbation_changes_the_identity`
    #[inline]
    #[must_use]
    pub fn identity(&self) -> ArtifactIdentity
    {
        // economy: hashes an encoded copy; a hashing sink beside the encoder
        // saves the allocation if identities show in a profile.
        ArtifactIdentity(*blake3::hash(self.encode().as_ref()).as_bytes())
    }

    /// Reads the committed artifact back from `store` through the kernel's
    /// decoder.
    ///
    /// # Specification
    /// - requires: `store` holds the artifact's nodes, or refuses for those it
    ///   does not.
    /// - ensures: on success the artifact the kernel's decoder returns for the
    ///   reassembled records, read only after the manifest's kernel format and
    ///   boundary commitment matched `expected`, the stored records rebuilt the
    ///   tree the manifest names, their keys stood where their positions
    ///   require, and each record ended at a segment boundary of the decode.
    /// - provides: the checked read: integrity first — the stored bytes are the
    ///   ones the manifest names — then validity, decided by the kernel's
    ///   decoder alone under its work budgets. A decoded artifact is not an
    ///   admitted one; admission is the consumer's next wall.
    /// - fails: [`ArtifactError::UnsupportedKernelFormat`],
    ///   [`ArtifactError::Records`] for parameters this build does not
    ///   implement, and [`ArtifactError::IncompatibleProfile`], before the
    ///   store is asked for anything; [`ArtifactError::Records`] for a node the
    ///   store does not hold or cannot authenticate, or a node of the wrong
    ///   shape; [`ArtifactError::TreeMismatch`];
    ///   [`ArtifactError::MisplacedRecord`]; [`ArtifactError::Kernel`];
    ///   [`ArtifactError::SegmentBoundary`].
    /// - panics: none.
    /// - intension: the store is read at the root and, for an internal root, at
    ///   each child leaf, iteratively; a record tree is one leaf or one
    ///   internal node over leaves, so nothing descends further.
    ///
    /// # Errors
    /// [`ArtifactError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — a committed artifact, small and multi-leaf,
    ///   reads back equal to the decode of its own image — plus L3 for the
    ///   decision surfaces: a foreign kernel format and a foreign commitment
    ///   refused with an empty store, an absent root refused by the store, a
    ///   tree whose identity matches but whose bytes the kernel refuses, keys
    ///   out of place, and records cut off a segment boundary.
    /// - witness: `artifact_contract::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `artifact_contract::artifact_contract::a_foreign_profile_or_format_is_refused_before_any_load`
    /// - witness: `artifact_contract::artifact_contract::a_matching_identity_over_bytes_the_kernel_refuses_is_refused`
    /// - witness: `artifact_contract::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
    /// - witness: `artifact_contract::artifact_contract::records_cut_off_a_segment_boundary_are_refused`
    #[inline]
    pub fn read_under<S>(
        &self,
        store: &S,
        expected: TreeParams,
    ) -> Result<DecodedArtifact, ArtifactError>
    where
        S: BlockStore + ?Sized,
    {
        if self.kernel_format != FORMAT_VERSION {
            return Err(ArtifactError::UnsupportedKernelFormat {
                found: self.kernel_format,
            });
        }
        expected.ensure_supported()?;
        if expected.boundary_commitment() != self.commitment {
            return Err(ArtifactError::IncompatibleProfile);
        }
        let loaded = load_records(store, self.root_node)?;
        let refs: Vec<RecordRef<'_>> = loaded.iter().map(Record::as_record_ref).collect();
        let rebuilt = RecordTree::build(&refs, expected)?;
        let named = TreeRoot::seal(expected, self.record_count, self.root_node)?;
        if rebuilt.root() != named {
            return Err(ArtifactError::TreeMismatch);
        }
        let set = ArtifactRecordSet::from_stored(rebuilt.records())?;
        let image = set.reassemble();
        let decoded = decode(image.as_image())?;
        set.ensure_cut_at(decoded.segments())?;

        Ok(decoded)
    }
}

/// Loads every record a stored tree holds, in key order.
///
/// # Specification
/// - requires: nothing; a node the store does not hold, cannot authenticate or
///   holds in the wrong shape is refused by name.
/// - ensures: on success the records of the root when it is a leaf, or of each
///   child leaf in child order when it is internal, each node loaded through
///   the store's verified load and decoded under its own work account.
/// - provides: the read path's traversal, kept to the record plane's two
///   shapes; the records are checked against the manifest by rebuilding.
/// - fails: [`ArtifactError::Records`] carrying the store's or the node
///   decoder's refusal, or the refusal of a child that is not a leaf.
/// - panics: none.
///
/// # Errors
/// [`ArtifactError::Records`] — as listed above.
fn load_records<S>(
    store: &S,
    root: NodeHash,
) -> Result<Vec<Record>, ArtifactError>
where
    S: BlockStore + ?Sized,
{
    let stored = store.load(root)?;
    let node = decode_node(stored.bytes(), &mut DecodeWork::new())?;
    let internal = match node {
        | DecodedNode::Leaf(leaf) => return Ok(leaf.records().to_vec()),
        | DecodedNode::Internal(internal) => internal,
    };
    let mut records = Vec::new();
    for child in internal.children() {
        let stored = store.load(child.identity())?;
        let node = decode_node(stored.bytes(), &mut DecodeWork::new())?;
        let leaf = node.as_leaf()?;
        records.extend_from_slice(leaf.records());
    }

    Ok(records)
}

/// The fixed-width bytes of one manifest field, before they are read as it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FieldBytes<const WIDTH: usize>([u8; WIDTH]);

/// The unread rest of a manifest image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ManifestCursor<'image>(&'image [u8]);

impl ManifestCursor<'_>
{
    /// Takes the next field's fixed-width bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the first `WIDTH` unread bytes, and the cursor
    ///   past them; on refusal the cursor does not move.
    /// - provides: every fixed-width read the decoder makes.
    /// - fails: [`ArtifactError::TruncatedManifest`] naming `field` when fewer
    ///   bytes remain.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::TruncatedManifest`] — the image ends inside `field`.
    #[spec(captures: [entry = self.0.len()],
        ensures: |ret| ret.is_err() || self.0.len().saturating_add(WIDTH) == entry)]
    fn take<const WIDTH: usize>(
        &mut self,
        field: ManifestField,
    ) -> Result<FieldBytes<WIDTH>, ArtifactError>
    {
        let Some((bytes, rest)) = self.0.split_first_chunk::<WIDTH>()
        else {
            return Err(ArtifactError::TruncatedManifest { field });
        };
        self.0 = rest;

        Ok(FieldBytes(*bytes))
    }

    /// Reads the domain.
    ///
    /// # Specification
    /// - requires: the cursor is at the image's start.
    /// - ensures: on success the cursor is past [`MANIFEST_DOMAIN`].
    /// - provides: the domain check, first, so no field of another byte
    ///   language is ever read.
    /// - fails: [`ArtifactError::MalformedManifest`] naming the domain when a
    ///   byte differs from it, and [`ArtifactError::TruncatedManifest`] naming
    ///   the domain when the image is a proper prefix of it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError`] — as listed above.
    fn domain(&mut self) -> Result<(), ArtifactError>
    {
        let agrees = self
            .0
            .iter()
            .zip(MANIFEST_DOMAIN)
            .all(|(found, expected)| found == expected);
        if !agrees {
            return Err(ArtifactError::MalformedManifest {
                field: ManifestField::Domain,
            });
        }
        let Some(rest) = self.0.strip_prefix(MANIFEST_DOMAIN)
        else {
            return Err(ArtifactError::TruncatedManifest {
                field: ManifestField::Domain,
            });
        };
        self.0 = rest;

        Ok(())
    }

    /// Reads the manifest version, admitting only the one this build writes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success [`ArtifactManifestVersion::V1`].
    /// - provides: the version gate before any versioned field is read.
    /// - fails: [`ArtifactError::MalformedManifest`] naming the version for any
    ///   other number, and the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError`] — as listed above.
    fn manifest_version(&mut self) -> Result<ArtifactManifestVersion, ArtifactError>
    {
        let bytes = self.take::<2>(ManifestField::ManifestVersion)?;
        let version = ArtifactManifestVersion(u16::from_le_bytes(bytes.0));
        if version != ArtifactManifestVersion::V1 {
            return Err(ArtifactError::MalformedManifest {
                field: ManifestField::ManifestVersion,
            });
        }

        Ok(version)
    }

    /// Reads the kernel format version.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the version the field carries; every value is
    ///   admitted, and whether the reader decodes it is the read's question.
    /// - provides: the kernel format field.
    /// - fails: the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::TruncatedManifest`] — as listed above.
    fn kernel_format(&mut self) -> Result<FormatVersion, ArtifactError>
    {
        let bytes = self.take::<2>(ManifestField::KernelFormat)?;

        Ok(FormatVersion(u16::from_le_bytes(bytes.0)))
    }

    /// Reads the length-prefixed boundary commitment.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the commitment is exactly the bytes the prefix
    ///   counts, and the cursor is past them.
    /// - provides: the commitment field, opaque, read with the declared length
    ///   checked against the bytes that remain before anything is copied.
    /// - fails: [`ArtifactError::TruncatedManifest`] naming the length when the
    ///   image ends inside the prefix, and naming the commitment when fewer
    ///   bytes remain than it declares.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::TruncatedManifest`] — as listed above.
    fn commitment(&mut self) -> Result<ProfileCommitment, ArtifactError>
    {
        let declared = self.take::<8>(ManifestField::CommitmentLength)?;
        let truncated = ArtifactError::TruncatedManifest {
            field: ManifestField::Commitment,
        };
        // A length past the address space cannot be present in the image.
        let Ok(length) = usize::try_from(u64::from_le_bytes(declared.0))
        else {
            return Err(truncated);
        };
        let Some((commitment, rest)) = self.0.split_at_checked(length)
        else {
            return Err(truncated);
        };
        self.0 = rest;

        Ok(ProfileCommitment::from(Box::<[u8]>::from(commitment)))
    }

    /// Reads the record count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the count the field carries; every value is
    ///   admitted, and whether the stored tree holds it is the read's question.
    /// - provides: the record count field.
    /// - fails: the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::TruncatedManifest`] — as listed above.
    fn record_count(&mut self) -> Result<RecordCount, ArtifactError>
    {
        let bytes = self.take::<8>(ManifestField::RecordCount)?;

        Ok(RecordCount(u64::from_le_bytes(bytes.0)))
    }

    /// Reads the root node identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the identity the field carries; whether the store
    ///   holds it is the read's question.
    /// - provides: the root node field.
    /// - fails: the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::TruncatedManifest`] — as listed above.
    fn root_node(&mut self) -> Result<NodeHash, ArtifactError>
    {
        let bytes = self.take::<ROOT_NODE_LEN>(ManifestField::RootNode)?;

        Ok(NodeHash::from(bytes.0))
    }

    /// Refuses bytes past the last field.
    ///
    /// # Specification
    /// - requires: every field has been read.
    /// - ensures: `|ret| ret.is_ok() == self.0.is_empty()` — success exactly
    ///   when nothing is left.
    /// - provides: the image's end, so one manifest has one image.
    /// - fails: [`ArtifactError::TrailingManifestBytes`] when bytes remain.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ArtifactError::TrailingManifestBytes`] — bytes remain.
    #[spec(ensures: |ret| ret.is_ok() == self.0.is_empty())]
    fn finish(self) -> Result<(), ArtifactError>
    {
        if self.0.is_empty() {
            Ok(())
        }
        else {
            Err(ArtifactError::TrailingManifestBytes)
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_term::FormatVersion;
    use gandr_storage_records::NodeHash;
    use gandr_storage_records::ProfileCommitment;
    use gandr_storage_records::RecordCount;

    use super::ArtifactIdentity;
    use super::ArtifactManifest;
    use super::MANIFEST_DOMAIN;
    use super::ManifestImage;
    use crate::error::ArtifactError;
    use crate::error::ManifestField;

    /// The golden commitment: three bytes, so its length prefix is visible.
    const COMMITMENT: [u8; 3] = [0xC0, 0xC1, 0xC2];

    /// The golden manifest: kernel format `0x0203`, the three-byte commitment
    /// `c0 c1 c2`, forty-two records, and a root node at bytes `0x00` to
    /// `0x1f`.
    ///
    /// # Specification
    /// trivial.
    fn golden() -> ArtifactManifest
    {
        ArtifactManifest::new(
            FormatVersion(0x0203),
            ProfileCommitment::from(Vec::from(COMMITMENT)),
            RecordCount(42),
            NodeHash::from(ROOT),
        )
    }

    /// The golden root node identity's bytes: `0x00` to `0x1f`.
    const ROOT: [u8; 32] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
        0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D,
        0x1E, 0x1F,
    ];

    /// Where the golden image's commitment length prefix begins: past the
    /// domain and the two versions.
    const COMMITMENT_LENGTH_OFFSET: usize = MANIFEST_DOMAIN.len().saturating_add(4);

    #[test]
    fn the_manifest_layout_is_golden()
    {
        let image = golden().encode();
        let root = ROOT;
        let fields: [(&str, &[u8]); 7] = [
            ("domain", b"gandr:storage-artifact:manifest:v1"),
            ("manifest version", &[0x01, 0x00]),
            ("kernel format version", &[0x03, 0x02]),
            ("commitment length", &[0x03, 0, 0, 0, 0, 0, 0, 0]),
            ("commitment", &COMMITMENT),
            ("record count", &[0x2A, 0, 0, 0, 0, 0, 0, 0]),
            ("root node identity", root.as_slice()),
        ];

        // Read back field by field, so a disagreement says which field moved.
        let mut rest: &[u8] = image.as_ref();
        for (name, field) in fields {
            let (head, tail) = rest.split_at(field.len());
            assert_eq!(head, field, "the image's {name}");
            rest = tail;
        }
        assert!(rest.is_empty(), "nothing follows the root node identity");
        assert_eq!(89, image.as_ref().len(), "the golden image's length");
    }

    #[test]
    fn the_manifest_round_trips_through_decode()
    {
        let manifest = golden();
        assert_eq!(
            Ok(manifest.clone()),
            ArtifactManifest::decode(manifest.encode().as_image()),
            "decode inverts encode"
        );
    }

    #[test]
    fn the_identity_is_blake3_of_the_canonical_bytes()
    {
        // BLAKE3 of the golden image, computed by `b3sum` over a file holding
        // exactly the bytes `the_manifest_layout_is_golden` writes out. A
        // literal, never recomputed: recomputing it would be the implementation
        // agreeing with itself.
        const IDENTITY: [u8; 32] = [
            0x08, 0xF5, 0x06, 0x1C, 0xF4, 0xBA, 0x0E, 0x73, 0x32, 0xB0, 0x84, 0xDB, 0x93, 0x9E,
            0x54, 0x38, 0x1E, 0x6B, 0x41, 0xC9, 0x05, 0x72, 0x06, 0xBB, 0x39, 0x1F, 0xE1, 0x30,
            0x2F, 0x57, 0xD1, 0xD8,
        ];

        assert_eq!(
            ArtifactIdentity::from(IDENTITY),
            golden().identity(),
            "the identity is BLAKE3 of the hand-built image"
        );
        assert_eq!(
            golden().identity(),
            golden().identity(),
            "the identity is deterministic"
        );
    }

    #[test]
    fn any_field_perturbation_changes_the_identity()
    {
        let base = golden().identity();
        let mut root = ROOT;
        let first = root.first_mut().expect("the identity is not empty");
        *first = 0xFF;
        let perturbed = [
            (
                "the kernel format version",
                ArtifactManifest::new(
                    FormatVersion(0x0204),
                    ProfileCommitment::from(Vec::from(COMMITMENT)),
                    RecordCount(42),
                    NodeHash::from(ROOT),
                ),
            ),
            (
                "the boundary commitment",
                ArtifactManifest::new(
                    FormatVersion(0x0203),
                    ProfileCommitment::from(Vec::from([0xC0, 0xC1, 0xC3])),
                    RecordCount(42),
                    NodeHash::from(ROOT),
                ),
            ),
            (
                "the record count",
                ArtifactManifest::new(
                    FormatVersion(0x0203),
                    ProfileCommitment::from(Vec::from(COMMITMENT)),
                    RecordCount(43),
                    NodeHash::from(ROOT),
                ),
            ),
            (
                "the root node identity",
                ArtifactManifest::new(
                    FormatVersion(0x0203),
                    ProfileCommitment::from(Vec::from(COMMITMENT)),
                    RecordCount(42),
                    NodeHash::from(root),
                ),
            ),
        ];
        for (field, manifest) in perturbed {
            assert_ne!(base, manifest.identity(), "{field} moves the identity");
        }
    }

    #[test]
    fn an_unknown_manifest_version_is_refused()
    {
        let mut bytes = Vec::from(golden().encode().as_ref());
        // The manifest version follows the domain, little-endian.
        let version = bytes
            .get_mut(MANIFEST_DOMAIN.len())
            .expect("the image holds its version");
        *version = 0x02;
        assert_eq!(
            Err(ArtifactError::MalformedManifest {
                field: ManifestField::ManifestVersion,
            }),
            ArtifactManifest::decode(ManifestImage::from(bytes.as_slice())),
            "an unknown manifest version is refused by name"
        );
    }

    #[test]
    fn a_malformed_manifest_is_rejected()
    {
        let good = Vec::from(golden().encode().as_ref());

        let mut foreign = good.clone();
        let first = foreign.first_mut().expect("the image is not empty");
        *first = b'X';
        assert_eq!(
            Err(ArtifactError::MalformedManifest {
                field: ManifestField::Domain,
            }),
            ArtifactManifest::decode(ManifestImage::from(foreign.as_slice())),
            "a foreign domain is refused"
        );

        let short = good.split_last().expect("the image is not empty").1;
        assert_eq!(
            Err(ArtifactError::TruncatedManifest {
                field: ManifestField::RootNode,
            }),
            ArtifactManifest::decode(ManifestImage::from(short)),
            "an image one byte short ends inside the root node identity"
        );

        let mut trailing = good;
        trailing.push(0x00);
        assert_eq!(
            Err(ArtifactError::TrailingManifestBytes),
            ArtifactManifest::decode(ManifestImage::from(trailing.as_slice())),
            "a trailing byte is refused"
        );
    }

    #[test]
    fn a_bad_commitment_length_is_rejected()
    {
        let good = Vec::from(golden().encode().as_ref());
        let offset = COMMITMENT_LENGTH_OFFSET;
        for declared in [u64::try_from(good.len()).expect("a length"), u64::MAX] {
            let mut bytes = good.clone();
            let prefix = bytes
                .get_mut(offset .. offset.saturating_add(8))
                .expect("the image holds the length prefix");
            prefix.copy_from_slice(&declared.to_le_bytes());
            assert_eq!(
                Err(ArtifactError::TruncatedManifest {
                    field: ManifestField::Commitment,
                }),
                ArtifactManifest::decode(ManifestImage::from(bytes.as_slice())),
                "a commitment length of {declared} passes the image's end"
            );
        }
    }

    #[test]
    fn truncation_at_every_prefix_is_rejected()
    {
        let good = Vec::from(golden().encode().as_ref());
        for length in 0 .. good.len() {
            let prefix = good.get(.. length).expect("a proper prefix");
            assert!(
                matches!(
                    ArtifactManifest::decode(ManifestImage::from(prefix)),
                    Err(ArtifactError::TruncatedManifest { .. })
                ),
                "the prefix of length {length} ends inside a field"
            );
        }
    }
}
