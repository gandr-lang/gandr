//! The value profile and manifest: what a content pointer is only meaningful
//! under.
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

use anodized::spec;
use gandr_storage_chunker::ParameterCommitment;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunkerParams;

use crate::index_base::ChildIndexBase;
use crate::ptr::ContentPtr;
use crate::units::ChunkFormatVersion;
use crate::units::CodecId;
use crate::units::CodecVersion;
use crate::units::ValueManifestVersion;

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
}

/// The identity of one committed value.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ValueManifest
{
    /// The manifest layout version.
    manifest_version: ValueManifestVersion,
    /// The constants a peer must match to share the value.
    profile: ValueProfile,
    /// The root of the committed chunk DAG.
    root: ContentPtr,
    /// The records the value emitted.
    token_count: TokenCount,
}

impl ValueManifest
{
    /// Names one committed value under the profile it was committed with.
    ///
    /// # Specification
    /// - requires: `profile` is the profile the commit that produced `root` ran
    ///   under, and `token_count` is the records that value emitted.
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

    /// Returns the records the value emitted — the length of its flat form in
    /// records, whatever chunks it was cut into.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn token_count(&self) -> TokenCount
    {
        self.token_count
    }
}
