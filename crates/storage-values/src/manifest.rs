//! The value profile and manifest: what a content pointer is only meaningful
//! under, as a byte language and an identity.
//!
//! # The rule
//!
//! Wherever a choice changes the addresses but no round trip can see it, the
//! profile carries it, so two deployments that disagree hold unequal profiles
//! and refuse each other rather than both committing correctly and sharing
//! nothing, with no diagnostic on either side.
//!
//! | field | what differs if two deployments disagree |
//! | ----- | ---------------------------------------- |
//! | typed chunker parameters | kappa and the cap fix where cuts fall, and so every digest |
//! | digest family | the hash fixes the addresses outright |
//! | codec identity | a different token encoding of the same value is a different value |
//! | child index base | what a child reference counts from |
//! | boundary classification | which constructors are cut candidates at all |
//! | chunk frame version | the framed preimage is what is hashed |
//!
//! The digest family, the boundary classification and the frame version are
//! fixed by this build — one variant each — and carried anyway, so a second
//! option is a refused mismatch rather than an unrecorded assumption.
//!
//! # The image
//!
//! ```text
//! image    := "gandr:storage-values:manifest:v1"
//!          || u16le manifest version
//!          || u64le commitment length || chunker commitment
//!          || u8 digest family
//!          || u16le codec identifier || u16le codec version
//!          || u8 child index base
//!          || u8 boundary classification
//!          || u16le chunk frame version
//!          || 32-byte root digest || u32le root offset
//!          || u64le token count
//! identity := BLAKE3(image)
//! ```
//!
//! Every integer is little-endian at a fixed width, every tag is one byte with
//! zero assigned to nothing, and the domain is inside the hashed bytes, so a
//! manifest identity and a chunk digest never hash the same preimage. The
//! decoder admits exactly the images the encoder writes, so a manifest decoded
//! from bytes re-encodes to those bytes and its identity is their BLAKE3.
//!
//! # Refusal order
//!
//! [`ValueManifest::decode`] reads the fields in image order and refuses at
//! the first that is foreign, unknown or cut short, then refuses trailing
//! bytes. [`ValueManifest::read_under`] refuses a profile the reader does not
//! share, naming the first differing field, before any chunk is loaded; only
//! then can a chunk be missing ([`ValueError::UnknownChunk`]) or invalid
//! ([`ValueError::DigestMismatch`], [`ValueError::MalformedChunk`]).
//! [`ValueManifest::closure`] loads every chunk a reader would, refusing the
//! first absent one by name, then refuses a token count the chunks do not
//! deliver.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_storage_chunker::AlgorithmVersion;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::PARAMETER_DOMAIN;
use gandr_storage_chunker::ParameterCommitment;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunkerParams;

use crate::chunk::ChunkStore;
use crate::closure::ValueClosure;
use crate::closure::walk_closure;
use crate::deref::cam_deref;
use crate::error::ManifestField;
use crate::error::ProfileField;
use crate::error::ValueError;
use crate::index_base::ChildIndexBase;
use crate::ptr::CHUNK_DIGEST_LEN;
use crate::ptr::ChunkDigest;
use crate::ptr::ContentPtr;
use crate::ptr::TokenOffset;
use crate::tokens::CanonicalValue;
use crate::units::ChunkFormatVersion;
use crate::units::CodecId;
use crate::units::CodecVersion;
use crate::units::ManifestImage;
use crate::units::ManifestImageBuf;
use crate::units::ValueManifestVersion;

/// The domain every manifest image opens with, inside the hashed preimage.
pub const MANIFEST_DOMAIN: &[u8] = b"gandr:storage-values:manifest:v1";

/// The byte length of a [`ManifestDigest`]: one BLAKE3 output.
pub const MANIFEST_DIGEST_LEN: usize = 0x20_usize;

/// The image's fixed-width fields after the domain, the commitment aside: the
/// version, the commitment length, three tags, the codec pair, the frame
/// version, the root digest and offset, and the token count.
const MANIFEST_FIXED_LEN: usize = 0x3F_usize;

/// The digest family tag for BLAKE3.
const DIGEST_FAMILY_BLAKE3: u8 = 0x01_u8;

/// The child index base tag for absolute references.
const INDEX_BASE_ABSOLUTE: u8 = 0x01_u8;

/// The child index base tag for chunk-local references.
const INDEX_BASE_CHUNK_LOCAL: u8 = 0x02_u8;

/// The boundary classification tag for every constructor.
const BOUNDARY_EVERY_CONSTRUCTOR: u8 = 0x01_u8;

/// The BLAKE3 identity of one manifest image.
///
/// Deliberately not a [`ChunkDigest`], and no conversion is offered in either
/// direction: a manifest names a committed value under its profile, a chunk
/// digest names one framed body, and the two hash different byte languages
/// under different domains.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ManifestDigest([u8; MANIFEST_DIGEST_LEN]);

impl From<[u8; MANIFEST_DIGEST_LEN]> for ManifestDigest
{
    /// Wraps raw digest bytes without computing anything.
    ///
    /// The digest is claimed by whoever wraps it; comparing it with
    /// [`ValueManifest::identity`] of a decoded image checks the claim.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; MANIFEST_DIGEST_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ManifestDigest
{
    /// Borrows the digest bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl fmt::Display for ManifestDigest
{
    /// Writes the digest as lowercase hexadecimal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly two lowercase hexadecimal digits per byte, in
    ///   byte order, and nothing else.
    /// - provides: the rendering a consumer stores or logs a manifest by.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — the pinned identity renders as the
    ///   hexadecimal an independent BLAKE3 tool printed for the hand-built
    ///   image, whose seventh byte has a zero high nibble a width-less
    ///   rendering would drop.
    /// - witness: `tests::manifest::the_manifest_bytes_are_pinned`
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

impl fmt::Debug for ManifestDigest
{
    /// Writes the digest as [`fmt::Display`] does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(self, f)
    }
}

/// The digest family the addresses are taken in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DigestFamily
{
    /// BLAKE3 with a thirty-two-byte output.
    Blake3,
}

/// Which constructor exits are boundary candidates.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BoundaryClassification
{
    /// Every constructor's exit but the outermost raises a boundary event.
    EveryConstructor,
}

/// The canonical token codec a value was encoded through.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CodecIdentity
{
    /// The codec's stable identifier.
    codec: CodecId,
    /// The codec's layout version.
    version: CodecVersion,
}

impl CodecIdentity
{
    /// Names a codec and its layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        codec: CodecId,
        version: CodecVersion,
    ) -> Self
    {
        Self { codec, version }
    }

    /// Returns the codec's identifier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn codec(&self) -> CodecId
    {
        self.codec
    }

    /// Returns the codec's layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn version(&self) -> CodecVersion
    {
        self.version
    }
}

/// Every constant two deployments must agree on to share storage.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueProfile
{
    /// The typed chunker parameters the value is cut under.
    params: TypedChunkerParams,
    /// The digest family.
    digest_family: DigestFamily,
    /// The token codec.
    codec: CodecIdentity,
    /// The child-reference representation.
    index_base: ChildIndexBase,
    /// Which constructor exits are cut candidates.
    boundary_classification: BoundaryClassification,
    /// The chunk frame layout the digests are taken over.
    chunk_frame_version: ChunkFormatVersion,
}

impl ValueProfile
{
    /// Fixes the constants a content pointer is only meaningful under.
    ///
    /// # Specification
    /// - requires: nothing; a base this encoding cannot represent is refused
    ///   when a value is committed under it.
    /// - ensures: the profile carries the arguments unchanged, with the digest
    ///   family, the boundary classification and the frame version this build
    ///   commits under.
    /// - provides: the unit of agreement between two deployments.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.params == params
        && ret.codec == codec
        && ret.index_base == index_base
        && ret.chunk_frame_version == ChunkFormatVersion::V1)]
    pub fn new(
        params: TypedChunkerParams,
        codec: CodecIdentity,
        index_base: ChildIndexBase,
    ) -> Self
    {
        Self {
            params,
            digest_family: DigestFamily::Blake3,
            codec,
            index_base,
            boundary_classification: BoundaryClassification::EveryConstructor,
            chunk_frame_version: ChunkFormatVersion::V1,
        }
    }

    /// Returns the typed chunker parameters.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> TypedChunkerParams
    {
        self.params
    }

    /// Returns the typed chunker parameters' committed bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chunker_commitment(&self) -> ParameterCommitment
    {
        self.params.commitment()
    }

    /// Returns the digest family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest_family(&self) -> DigestFamily
    {
        self.digest_family
    }

    /// Returns the codec identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn codec(&self) -> CodecIdentity
    {
        self.codec
    }

    /// Returns the child-reference representation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn index_base(&self) -> ChildIndexBase
    {
        self.index_base
    }

    /// Returns which constructor exits are cut candidates.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn boundary_classification(&self) -> BoundaryClassification
    {
        self.boundary_classification
    }

    /// Returns the chunk frame layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn chunk_frame_version(&self) -> ChunkFormatVersion
    {
        self.chunk_frame_version
    }

    /// Refuses a profile that is not the one a reader expects, naming the
    /// first field that differs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.is_ok() == (self == expected)` — success exactly
    ///   when every field agrees.
    /// - provides: the refusal before validation a profile-checked read opens
    ///   with.
    /// - fails: [`ValueError::IncompatibleProfile`] naming the first differing
    ///   field in manifest image order: the chunker commitment, the digest
    ///   family, the codec identifier, the codec version, the child index base,
    ///   the boundary classification, the chunk frame version.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::IncompatibleProfile`] — a field differs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — one expected profile per field that admits a
    ///   second value (kappa and the cap through the commitment, the codec
    ///   identifier and version, the child index base), each refused naming
    ///   that field; a profile differing in two fields, refused naming the
    ///   earlier; and the identical profile, admitted. The digest family, the
    ///   boundary classification and the frame version have one value each in
    ///   this build, so no second profile can differ there; a decoded image
    ///   naming another is refused by its tag before a profile exists.
    /// - witness: `tests::manifest::a_profile_mismatch_is_refused_before_any_chunk_is_read`
    /// - witness: `tests::manifest::a_matching_profile_reads_the_committed_value`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (self == expected))]
    pub fn ensure_matches(
        &self,
        expected: &Self,
    ) -> Result<(), ValueError>
    {
        // Destructured, so a field added to the profile is a field compared
        // here before it compiles.
        let Self {
            params,
            digest_family,
            codec,
            index_base,
            boundary_classification,
            chunk_frame_version,
        } = *self;
        let fields = [
            (params == expected.params, ProfileField::ChunkerCommitment),
            (
                digest_family == expected.digest_family,
                ProfileField::DigestFamily,
            ),
            (
                codec.codec() == expected.codec.codec(),
                ProfileField::CodecId,
            ),
            (
                codec.version() == expected.codec.version(),
                ProfileField::CodecVersion,
            ),
            (
                index_base == expected.index_base,
                ProfileField::ChildIndexBase,
            ),
            (
                boundary_classification == expected.boundary_classification,
                ProfileField::BoundaryClassification,
            ),
            (
                chunk_frame_version == expected.chunk_frame_version,
                ProfileField::ChunkFrameVersion,
            ),
        ];

        match fields.into_iter().find(|&(agrees, _field)| !agrees) {
            | Some((_agrees, field)) => Err(ValueError::IncompatibleProfile { field }),
            | None => Ok(()),
        }
    }
}

/// The identity of one committed value: its profile, its root, and the
/// records a reader of the root delivers.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueManifest
{
    /// The manifest layout version.
    manifest_version: ValueManifestVersion,
    /// The constants a peer must match to share the value.
    profile: ValueProfile,
    /// The root of the committed chunk DAG.
    root: ContentPtr,
    /// The records a reader of the root delivers, child chunks spliced.
    token_count: TokenCount,
}

impl ValueManifest
{
    /// Names one committed value under the profile it was committed with.
    ///
    /// # Specification
    /// - requires: `profile` is the profile the commit that produced `root` ran
    ///   under, and `token_count` is the records a reader of `root` delivers.
    /// - ensures: the manifest carries them unchanged at
    ///   [`ValueManifestVersion::V1`].
    /// - provides: the description [`crate::cam_commit`] returns.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.profile == profile
        && ret.root == root
        && ret.token_count == token_count
        && ret.manifest_version == ValueManifestVersion::V1)]
    pub fn new(
        profile: ValueProfile,
        root: ContentPtr,
        token_count: TokenCount,
    ) -> Self
    {
        Self {
            manifest_version: ValueManifestVersion::V1,
            profile,
            root,
            token_count,
        }
    }

    /// Returns the manifest layout version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn manifest_version(&self) -> ValueManifestVersion
    {
        self.manifest_version
    }

    /// Returns the profile a peer must match.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn profile(&self) -> &ValueProfile
    {
        &self.profile
    }

    /// Returns the root content pointer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> ContentPtr
    {
        self.root
    }

    /// Returns the records a reader of the root delivers — the length of the
    /// value's flat form in records, whatever chunks it was cut into, with
    /// every embedded pointer's value spliced in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn token_count(&self) -> TokenCount
    {
        self.token_count
    }

    /// Writes the manifest's image: the domain, then every field in fixed
    /// order and width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the image is [`MANIFEST_DOMAIN`] followed by the fields in
    ///   the order and widths this module documents, every integer
    ///   little-endian; [`ValueManifest::decode`] reads it back as `self`.
    /// - provides: the bytes a consumer stores and sends, and the preimage of
    ///   [`ValueManifest::identity`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — one manifest's image, read back field by
    ///   field against bytes written out by hand, and the manifests of
    ///   generated commits under generated profiles decoding back equal.
    /// - witness: `tests::manifest::the_manifest_bytes_are_pinned`
    /// - witness: `tests::manifest::a_manifest_round_trips_through_its_bytes`
    #[inline]
    #[must_use]
    // The round trip is checked from decode's side alone: an encode predicate
    // calling decode would recurse through decode's own predicate.
    #[spec(ensures: |ret| ret.as_ref().starts_with(MANIFEST_DOMAIN)
        && ret.as_ref().len() == MANIFEST_DOMAIN
            .len()
            .saturating_add(MANIFEST_FIXED_LEN)
            .saturating_add(self.profile.chunker_commitment().as_ref().len()))]
    pub fn encode(&self) -> ManifestImageBuf
    {
        let committed = self.profile.chunker_commitment();
        let commitment: &[u8] = committed.as_ref();
        // A commitment is held in memory, so its length fits sixty-four bits on
        // every target Rust supports.
        let commitment_length = u64::try_from(commitment.len()).unwrap_or(u64::MAX);
        let codec = self.profile.codec;

        let mut image = Vec::with_capacity(
            MANIFEST_DOMAIN
                .len()
                .saturating_add(MANIFEST_FIXED_LEN)
                .saturating_add(commitment.len()),
        );
        image.extend_from_slice(MANIFEST_DOMAIN);
        image.extend_from_slice(u16::from(self.manifest_version).to_le_bytes().as_slice());
        image.extend_from_slice(commitment_length.to_le_bytes().as_slice());
        image.extend_from_slice(commitment);
        image.push(match self.profile.digest_family {
            | DigestFamily::Blake3 => DIGEST_FAMILY_BLAKE3,
        });
        image.extend_from_slice(u16::from(codec.codec()).to_le_bytes().as_slice());
        image.extend_from_slice(u16::from(codec.version()).to_le_bytes().as_slice());
        image.push(match self.profile.index_base {
            | ChildIndexBase::Absolute => INDEX_BASE_ABSOLUTE,
            | ChildIndexBase::ChunkLocal => INDEX_BASE_CHUNK_LOCAL,
        });
        image.push(match self.profile.boundary_classification {
            | BoundaryClassification::EveryConstructor => BOUNDARY_EVERY_CONSTRUCTOR,
        });
        image.extend_from_slice(
            u16::from(self.profile.chunk_frame_version)
                .to_le_bytes()
                .as_slice(),
        );
        image.extend_from_slice(self.root.digest().as_ref());
        image.extend_from_slice(u32::from(self.root.offset()).to_le_bytes().as_slice());
        image.extend_from_slice(u64::from(self.token_count).to_le_bytes().as_slice());

        ManifestImageBuf::from(image.into_boxed_slice())
    }

    /// Reads a manifest image, refusing every image the encoder would not
    /// write.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: on success the manifest whose [`ValueManifest::encode`] is
    ///   exactly `image`.
    /// - provides: the only way from bytes to a manifest; the cursor reads each
    ///   field once, front to back, with no recursion and no allocation, and
    ///   checks a declared length against the bytes that remain before reading
    ///   under it.
    /// - fails: in image order, [`ValueError::MalformedManifest`] naming a
    ///   foreign domain, a manifest version other than one, a chunker
    ///   commitment that is not a typed one with nonzero kappa and cap, an
    ///   unassigned digest family, child index base or boundary classification
    ///   tag, or a chunk frame version other than one;
    ///   [`ValueError::TruncatedManifest`] naming the field the image ends
    ///   inside; then [`ValueError::TrailingManifestBytes`] for bytes past the
    ///   token count.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — generated manifests decode from their own
    ///   images and re-encode to the same bytes — plus L3 for each refusal: a
    ///   foreign domain, an unknown manifest version, each tagged field's
    ///   unassigned values, a commitment under another algorithm or with zero
    ///   kappa, every prefix of a valid image named by the field it ends inside
    ///   as a layout table in the suite computes it, and one trailing byte.
    /// - witness: `tests::manifest::a_manifest_round_trips_through_its_bytes`
    /// - witness: `tests::manifest::each_malformed_manifest_is_refused_by_name`
    /// - witness: `tests::manifest::a_manifest_image_is_refused_as_a_chunk`
    #[inline]
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|manifest| manifest.encode().as_image() == image))]
    pub fn decode(image: ManifestImage<'_>) -> Result<Self, ValueError>
    {
        let mut cursor = ManifestCursor(image.into());
        cursor.domain()?;
        let manifest_version = cursor.manifest_version()?;
        let params = cursor.chunker_params()?;
        let digest_family = cursor.digest_family()?;
        let codec = cursor.codec()?;
        let index_base = cursor.index_base()?;
        let boundary_classification = cursor.boundary_classification()?;
        let chunk_frame_version = cursor.chunk_frame_version()?;
        let root = cursor.root()?;
        let token_count = cursor.token_count()?;
        cursor.finish()?;

        Ok(Self {
            manifest_version,
            profile: ValueProfile {
                params,
                digest_family,
                codec,
                index_base,
                boundary_classification,
                chunk_frame_version,
            },
            root,
            token_count,
        })
    }

    /// Names the manifest: BLAKE3 over its whole image, domain included.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the digest is BLAKE3 over [`ValueManifest::encode`]'s image,
    ///   so two manifests share an identity exactly when every field agrees, up
    ///   to BLAKE3 collisions.
    /// - provides: the name a consumer stores to refer to a committed value
    ///   under its profile.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — one manifest's identity against a golden an
    ///   independent BLAKE3 tool computed over its hand-built image — plus L3
    ///   for binding: one manifest per field that admits a second value, each
    ///   moving the identity.
    /// - witness: `tests::manifest::the_manifest_bytes_are_pinned`
    /// - witness: `tests::manifest::each_manifest_field_moves_the_identity`
    #[inline]
    #[must_use]
    pub fn identity(&self) -> ManifestDigest
    {
        // economy: hashes an encoded copy; a hashing sink beside the encoder
        // saves the allocation if identities show in a profile.
        ManifestDigest(*blake3::hash(self.encode().as_ref()).as_bytes())
    }

    /// Reads the committed value, refusing a profile the reader does not
    /// share before any chunk is loaded.
    ///
    /// # Specification
    /// - requires: `store` holds the value's chunks, or refuses for those it
    ///   does not.
    /// - ensures: on success the value the root decodes to, read only after the
    ///   manifest's profile matched `expected` in every field.
    /// - provides: the profile-checked read, so a reader assuming other
    ///   constants refuses instead of reading chunks cut under them.
    /// - fails: [`ValueError::IncompatibleProfile`] naming the first differing
    ///   field, before the store is asked for anything; then [`cam_deref`]'s
    ///   refusals: [`ValueError::UnknownChunk`] for a missing chunk,
    ///   [`ValueError::DigestMismatch`] and [`ValueError::MalformedChunk`] for
    ///   an invalid one, and the codec's.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — over a store that counts its loads, each profile
    ///   field that admits a second value is refused by name with no load made,
    ///   and the matching profile reads the committed value back.
    /// - witness: `tests::manifest::a_profile_mismatch_is_refused_before_any_chunk_is_read`
    /// - witness: `tests::manifest::a_matching_profile_reads_the_committed_value`
    #[inline]
    pub fn read_under<Value>(
        &self,
        store: &dyn ChunkStore,
        expected: &ValueProfile,
    ) -> Result<Value, ValueError>
    where
        Value: CanonicalValue,
    {
        self.profile.ensure_matches(expected)?;

        cam_deref(store, self.root)
    }

    /// Loads and verifies every chunk a reader of the value would, and checks
    /// the records they deliver against the token count.
    ///
    /// # Specification
    /// - requires: nothing; a missing or invalid chunk is refused by name.
    /// - ensures: on success the closure holds every chunk a dereference of the
    ///   root loads, each verified, and those chunks deliver exactly the
    ///   manifest's token count; for a manifest [`crate::cam_commit`] returned
    ///   from an empty store, the closure is every chunk that commit wrote.
    /// - provides: the complete closure at dereference — what a consumer pins,
    ///   sends or attests for one committed value.
    /// - fails: [`ValueError::UnknownChunk`] naming the first absent digest in
    ///   stream order; the store's refusals for an invalid chunk; the walk's
    ///   refusals for a malformed subtree or a spent decode budget; then
    ///   [`ValueError::TokenCountMismatch`] when the chunks deliver another
    ///   count than the manifest declares.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 agreement — for generated values under generated
    ///   profiles, and for a value embedding another, committed into one store,
    ///   the closure is the set of digests the store holds — plus L3 for a
    ///   store missing one chunk two seams below the root, refused naming it,
    ///   and a token count one past the spliced total, refused with both
    ///   counts.
    /// - witness: `tests::closure::the_closure_is_every_chunk_the_commit_wrote`
    /// - witness: `tests::closure::a_missing_descendant_fails_the_closure_by_name`
    /// - witness: `tests::closure::a_manifest_overstating_its_tokens_fails_the_closure`
    #[inline]
    #[spec(ensures: |ret| ret
        .as_ref()
        .ok()
        .is_none_or(|closure| closure.digests().contains(&self.root.digest())))]
    pub fn closure(
        &self,
        store: &dyn ChunkStore,
    ) -> Result<ValueClosure, ValueError>
    {
        let walked = walk_closure(store, self.root)?;
        if walked.token_count() != self.token_count {
            return Err(ValueError::TokenCountMismatch {
                declared: self.token_count,
                spliced: walked.token_count(),
            });
        }

        Ok(walked.into_closure())
    }
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
    /// - fails: [`ValueError::TruncatedManifest`] naming `field` when fewer
    ///   bytes remain.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::TruncatedManifest`] — the image ends inside `field`.
    #[spec(captures: [entry = self.0.len()],
        ensures: |ret| ret.is_err() || self.0.len().saturating_add(WIDTH) == entry)]
    fn take<const WIDTH: usize>(
        &mut self,
        field: ManifestField,
    ) -> Result<FieldBytes<WIDTH>, ValueError>
    {
        let Some((bytes, rest)) = self.0.split_first_chunk::<WIDTH>()
        else {
            return Err(ValueError::TruncatedManifest { field });
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
    /// - fails: [`ValueError::MalformedManifest`] naming the domain when a byte
    ///   differs from it, and [`ValueError::TruncatedManifest`] naming the
    ///   domain when the image is a proper prefix of it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn domain(&mut self) -> Result<(), ValueError>
    {
        let agrees = self
            .0
            .iter()
            .zip(MANIFEST_DOMAIN)
            .all(|(found, expected)| found == expected);
        if !agrees {
            return Err(ValueError::MalformedManifest {
                field: ManifestField::Domain,
            });
        }
        let Some(rest) = self.0.strip_prefix(MANIFEST_DOMAIN)
        else {
            return Err(ValueError::TruncatedManifest {
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
    /// - ensures: on success [`ValueManifestVersion::V1`].
    /// - provides: the version gate before any versioned field is read.
    /// - fails: [`ValueError::MalformedManifest`] naming the version for any
    ///   other number, and the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn manifest_version(&mut self) -> Result<ValueManifestVersion, ValueError>
    {
        let bytes = self.take::<2>(ManifestField::ManifestVersion)?;
        let version = ValueManifestVersion::from(u16::from_le_bytes(bytes.0));
        if version != ValueManifestVersion::V1 {
            return Err(ValueError::MalformedManifest {
                field: ManifestField::ManifestVersion,
            });
        }

        Ok(version)
    }

    /// Reads the length-prefixed chunker commitment as typed parameters.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the parameters whose
    ///   [`TypedChunkerParams::commitment`] is exactly the bytes the prefix
    ///   counts: the chunker's parameter domain, the typed algorithm's
    ///   discriminator, then kappa and the cap as sixty-four-bit little-endian
    ///   integers, nothing after.
    /// - provides: the profile's chunking constants, read without allocating;
    ///   the declared length is checked against the bytes that remain before
    ///   anything is read under it.
    /// - fails: [`ValueError::TruncatedManifest`] naming the length when the
    ///   image ends inside the prefix, and naming the commitment when fewer
    ///   bytes remain than it declares; [`ValueError::MalformedManifest`]
    ///   naming the commitment for any other domain, algorithm or length, or a
    ///   zero kappa or cap.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn chunker_params(&mut self) -> Result<TypedChunkerParams, ValueError>
    {
        let declared = self.take::<8>(ManifestField::CommitmentLength)?;
        let truncated = ValueError::TruncatedManifest {
            field: ManifestField::ChunkerCommitment,
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

        let refused = ValueError::MalformedManifest {
            field: ManifestField::ChunkerCommitment,
        };
        let Some(fields) = commitment.strip_prefix(PARAMETER_DOMAIN)
        else {
            return Err(refused);
        };
        let Some((algorithm, fields)) = fields.split_first_chunk::<2>()
        else {
            return Err(refused);
        };
        let Ok(AlgorithmVersion::TypedCdc) =
            AlgorithmVersion::try_from(u16::from_le_bytes(*algorithm))
        else {
            return Err(refused);
        };
        let Some((kappa, fields)) = fields.split_first_chunk::<8>()
        else {
            return Err(refused);
        };
        let Some((cap, fields)) = fields.split_first_chunk::<8>()
        else {
            return Err(refused);
        };
        if !fields.is_empty() {
            return Err(refused);
        }
        let Ok(kappa) = Kappa::try_from(u64::from_le_bytes(*kappa))
        else {
            return Err(refused);
        };
        let Ok(cap) = TokenCap::try_from(u64::from_le_bytes(*cap))
        else {
            return Err(refused);
        };

        Ok(TypedChunkerParams::new(kappa, cap))
    }

    /// Reads the digest family's tag.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the family the tag names.
    /// - provides: the digest family field.
    /// - fails: [`ValueError::MalformedManifest`] naming the digest family for
    ///   an unassigned tag, and the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn digest_family(&mut self) -> Result<DigestFamily, ValueError>
    {
        let FieldBytes([tag]) = self.take::<1>(ManifestField::DigestFamily)?;

        match tag {
            | DIGEST_FAMILY_BLAKE3 => Ok(DigestFamily::Blake3),
            | _ => Err(ValueError::MalformedManifest {
                field: ManifestField::DigestFamily,
            }),
        }
    }

    /// Reads the codec's identifier and layout version.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the codec identity both fields carry; every value
    ///   of either is admitted.
    /// - provides: the codec identity field pair.
    /// - fails: the truncation refusal naming whichever field the image ends
    ///   inside.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::TruncatedManifest`] — as listed above.
    fn codec(&mut self) -> Result<CodecIdentity, ValueError>
    {
        let codec = self.take::<2>(ManifestField::CodecId)?;
        let version = self.take::<2>(ManifestField::CodecVersion)?;

        Ok(CodecIdentity::new(
            CodecId::from(u16::from_le_bytes(codec.0)),
            CodecVersion::from(u16::from_le_bytes(version.0)),
        ))
    }

    /// Reads the child index base's tag.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the base the tag names; both bases are admitted,
    ///   since a manifest may name a base a commit refuses.
    /// - provides: the child index base field.
    /// - fails: [`ValueError::MalformedManifest`] naming the base for an
    ///   unassigned tag, and the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn index_base(&mut self) -> Result<ChildIndexBase, ValueError>
    {
        let FieldBytes([tag]) = self.take::<1>(ManifestField::ChildIndexBase)?;

        match tag {
            | INDEX_BASE_ABSOLUTE => Ok(ChildIndexBase::Absolute),
            | INDEX_BASE_CHUNK_LOCAL => Ok(ChildIndexBase::ChunkLocal),
            | _ => Err(ValueError::MalformedManifest {
                field: ManifestField::ChildIndexBase,
            }),
        }
    }

    /// Reads the boundary classification's tag.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the classification the tag names.
    /// - provides: the boundary classification field.
    /// - fails: [`ValueError::MalformedManifest`] naming the classification for
    ///   an unassigned tag, and the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn boundary_classification(&mut self) -> Result<BoundaryClassification, ValueError>
    {
        let FieldBytes([tag]) = self.take::<1>(ManifestField::BoundaryClassification)?;

        match tag {
            | BOUNDARY_EVERY_CONSTRUCTOR => Ok(BoundaryClassification::EveryConstructor),
            | _ => Err(ValueError::MalformedManifest {
                field: ManifestField::BoundaryClassification,
            }),
        }
    }

    /// Reads the chunk frame version, admitting only the one this build
    /// frames under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success [`ChunkFormatVersion::V1`].
    /// - provides: the chunk frame version field.
    /// - fails: [`ValueError::MalformedManifest`] naming the frame version for
    ///   any other number, and the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    fn chunk_frame_version(&mut self) -> Result<ChunkFormatVersion, ValueError>
    {
        let bytes = self.take::<2>(ManifestField::ChunkFrameVersion)?;
        let version = ChunkFormatVersion::from(u16::from_le_bytes(bytes.0));
        if version != ChunkFormatVersion::V1 {
            return Err(ValueError::MalformedManifest {
                field: ManifestField::ChunkFrameVersion,
            });
        }

        Ok(version)
    }

    /// Reads the root pointer's digest and offset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the pointer both fields carry; every value of
    ///   either is admitted, and whether the store holds the digest is the
    ///   closure's question.
    /// - provides: the root field pair.
    /// - fails: the truncation refusal naming whichever field the image ends
    ///   inside.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::TruncatedManifest`] — as listed above.
    fn root(&mut self) -> Result<ContentPtr, ValueError>
    {
        let digest = self.take::<CHUNK_DIGEST_LEN>(ManifestField::RootDigest)?;
        let offset = self.take::<4>(ManifestField::RootOffset)?;

        Ok(ContentPtr::new(
            ChunkDigest::from(digest.0),
            TokenOffset::from(u32::from_le_bytes(offset.0)),
        ))
    }

    /// Reads the token count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the count the field carries; every value is
    ///   admitted, and whether the chunks deliver it is the closure's question.
    /// - provides: the token count field.
    /// - fails: the truncation refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::TruncatedManifest`] — as listed above.
    fn token_count(&mut self) -> Result<TokenCount, ValueError>
    {
        let bytes = self.take::<8>(ManifestField::TokenCount)?;

        Ok(TokenCount::from(u64::from_le_bytes(bytes.0)))
    }

    /// Refuses bytes past the last field.
    ///
    /// # Specification
    /// - requires: every field has been read.
    /// - ensures: `|ret| ret.is_ok() == self.0.is_empty()` — success exactly
    ///   when nothing is left.
    /// - provides: the image's end, so one manifest has one image.
    /// - fails: [`ValueError::TrailingManifestBytes`] when bytes remain.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::TrailingManifestBytes`] — bytes remain.
    #[spec(ensures: |ret| ret.is_ok() == self.0.is_empty())]
    fn finish(self) -> Result<(), ValueError>
    {
        if self.0.is_empty() {
            Ok(())
        }
        else {
            Err(ValueError::TrailingManifestBytes)
        }
    }
}
