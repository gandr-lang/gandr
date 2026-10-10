//! What a tree commits to: the consensus-sensitive parameter set
//! [`TreeParams`] and the root manifest [`TreeRoot`] that binds it.

use anodized::spec;

use crate::boundary::BoundaryParams;
use crate::boundary::ProfileCommitment;
use crate::bytes::NodeHash;
use crate::error::RecordTreeError;
use crate::error::WireVersion;
use crate::record::RecordCount;
use crate::wire::Domain;
use crate::wire::WireBuffer;
use crate::wire::WireBytes;
use crate::wire::WireLong;
use crate::wire::WireTag;
use crate::wire::WireWord;
use crate::wire::digest;

/// The shape of tree a root names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TreeKind
{
    /// An ordered-record Merkle search tree.
    MerkleSearch,
}

impl TreeKind
{
    /// The shape newly built trees have.
    pub const CURRENT: Self = Self::MerkleSearch;

    /// Returns the discriminator this shape is committed under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fixed byte per shape, distinct across the enum, and never
    ///   derived from the variant's position.
    /// - provides: the discriminator a manifest digest is folded over, so
    ///   reordering this enum cannot change a committed digest.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on one complete manifest preimage; its independent
    ///   digest golden distinguishes a changed discriminator or ordinal-derived
    ///   zero.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == 0x01_u8)]
    const fn tag(self) -> WireTag
    {
        match self {
            | Self::MerkleSearch => WireTag(0x01_u8),
        }
    }
}

/// The version of the canonical encoding a tree's bytes are written in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EncodingVersion
{
    /// The first encoding.
    V1,
    /// The encoding that writes its fixed-width fields little-endian.
    V2,
}

impl EncodingVersion
{
    /// The version newly built trees are written in.
    pub const CURRENT: Self = Self::V2;

    /// Returns the number this version is committed under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fixed number per version, distinct across the enum, and
    ///   never derived from the variant's position.
    /// - provides: the number written into the bytes and folded into a digest,
    ///   so reordering this enum cannot change either.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts all sixteen-bit admission inputs,
    ///   distinguishing renumbering and a wrong unsupported-version payload; L2
    ///   fixes the current version in the manifest digest.
    /// - witness: `params::tests::version_admits_only_the_current_number`
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == match self { Self::V1 => 1, Self::V2 => 2 })]
    pub const fn number(self) -> WireVersion
    {
        match self {
            | Self::V1 => WireVersion(1_u16),
            | Self::V2 => WireVersion(2_u16),
        }
    }

    /// Reads a version number back, refusing one this build does not accept.
    ///
    /// # Specification
    /// - requires: nothing; the number comes from bytes and is arbitrary.
    /// - ensures: on success the returned version's number equals the input.
    /// - provides: the single admission point for a wire version, so no decoder
    ///   silently proceeds on an unknown one.
    /// - fails: [`RecordTreeError::UnsupportedVersion`] on any other number.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::UnsupportedVersion`] — the number names no version
    /// this build accepts.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts all sixteen-bit inputs against a literal
    ///   version table, distinguishing missing admission, extra admissions,
    ///   variant swaps and altered refusal payloads.
    /// - witness: `params::tests::version_admits_only_the_current_number`
    #[inline]
    #[spec(ensures: |ret| ret == if number == Self::CURRENT.number() {
        Ok(Self::CURRENT)
    } else {
        Err(RecordTreeError::UnsupportedVersion { version: number })
    })]
    pub fn from_number(number: WireVersion) -> Result<Self, RecordTreeError>
    {
        if number == Self::CURRENT.number() {
            return Ok(Self::CURRENT);
        }

        Err(RecordTreeError::UnsupportedVersion { version: number })
    }
}

/// The hash family node and root identities are drawn from.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HashAlgorithm
{
    /// BLAKE3 with a thirty-two byte output.
    Blake3,
}

impl HashAlgorithm
{
    /// The family newly built trees use.
    pub const CURRENT: Self = Self::Blake3;

    /// Returns the discriminator this family is committed under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fixed byte per family, distinct across the enum, and
    ///   never derived from the variant's position.
    /// - provides: the discriminator a manifest digest is folded over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on one complete manifest preimage; its independent
    ///   digest golden distinguishes a changed discriminator or ordinal-derived
    ///   zero.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == 0x01_u8)]
    const fn tag(self) -> WireTag
    {
        match self {
            | Self::Blake3 => WireTag(0x01_u8),
        }
    }
}

/// What an internal node's separator keys mean.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SeparatorConvention
{
    /// Each separator is the first key reachable through its child.
    FirstKey,
}

impl SeparatorConvention
{
    /// The convention newly built trees use.
    pub const CURRENT: Self = Self::FirstKey;

    /// Returns the discriminator this convention is committed under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fixed byte per convention, distinct across the enum, and
    ///   never derived from the variant's position.
    /// - provides: the discriminator a manifest digest is folded over.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on one complete manifest preimage; its independent
    ///   digest golden distinguishes a changed discriminator or ordinal-derived
    ///   zero.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == 0x01_u8)]
    const fn tag(self) -> WireTag
    {
        match self {
            | Self::FirstKey => WireTag(0x01_u8),
        }
    }
}

/// Everything two parties must agree on to build the same tree from the same
/// records.
///
/// # Specification
/// - requires: nothing; every field is a closed enumeration or a checked
///   parameter set.
/// - ensures: equality holds exactly when every committed field agrees, and the
///   boundary commitment is derived from the boundary parameters rather than
///   stored beside them, so the two cannot drift apart.
/// - provides: the parameter half of a root manifest.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — all combinations of the admitted field types are
///   representable, including unsupported encoding versions. Equality relates
///   two parameter sets; admission and commitment methods check concrete uses.
///
/// # Adequacy
/// - hypothesis: L2 on the current manifest golden and L3 on independent count,
///   node and boundary changes distinguish omitted commitments; both encoding
///   versions distinguish an unsupported parameter that becomes unreadable.
/// - witness: `params::tests::the_manifest_digest_is_pinned`
/// - witness: `params::tests::every_bound_field_moves_the_manifest_digest`
/// - witness: `params::tests::the_current_parameters_are_supported`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TreeParams
{
    /// The tree shape.
    kind: TreeKind,
    /// The canonical encoding version.
    encoding_version: EncodingVersion,
    /// The hash family.
    hash_algorithm: HashAlgorithm,
    /// The separator meaning.
    separator_convention: SeparatorConvention,
    /// The leaf boundary rule.
    boundary: BoundaryParams,
}

impl TreeParams
{
    /// Builds a parameter set from explicit choices.
    ///
    /// # Specification
    /// - requires: nothing — a combination this build cannot honour is
    ///   admissible input here and is refused by
    ///   [`TreeParams::ensure_supported`], which is what keeps an unsupported
    ///   set readable rather than unrepresentable.
    /// - ensures: the set carries exactly the five choices offered.
    /// - provides: the only way to state a parameter set, so every field is a
    ///   deliberate choice rather than a default.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on both encoding versions and independently changed
    ///   mask widths and caps; sealing refusals and differing manifest
    ///   identities distinguish substituted choices and prematurely rejected
    ///   old versions.
    /// - witness: `params::tests::the_current_parameters_are_supported`
    /// - witness: `params::tests::every_bound_field_moves_the_manifest_digest`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.encoding_version.number().0 == encoding_version.number().0)]
    pub const fn new(
        kind: TreeKind,
        encoding_version: EncodingVersion,
        hash_algorithm: HashAlgorithm,
        separator_convention: SeparatorConvention,
        boundary: BoundaryParams,
    ) -> Self
    {
        Self {
            kind,
            encoding_version,
            hash_algorithm,
            separator_convention,
            boundary,
        }
    }

    /// Builds the parameter set newly built trees use.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every field is that field's own `CURRENT` value, so the set
    ///   this build writes is named in one place.
    /// - provides: the parameter set a build accepts and produces, which
    ///   [`TreeParams::ensure_supported`] checks against field by field.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a fixed current-profile manifest and L3 against the
    ///   unsupported encoding distinguish drift in the emitted profile or
    ///   version. This does not establish the suitability of the chosen limits.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    /// - witness: `params::tests::the_current_parameters_are_supported`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.encoding_version.number().0 == EncodingVersion::CURRENT.number().0)]
    pub const fn current() -> Self
    {
        Self::new(
            TreeKind::CURRENT,
            EncodingVersion::CURRENT,
            HashAlgorithm::CURRENT,
            SeparatorConvention::CURRENT,
            BoundaryParams::current(),
        )
    }

    /// Returns the tree shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> TreeKind
    {
        self.kind
    }

    /// Returns the canonical encoding version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn encoding_version(&self) -> EncodingVersion
    {
        self.encoding_version
    }

    /// Returns the hash family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hash_algorithm(&self) -> HashAlgorithm
    {
        self.hash_algorithm
    }

    /// Returns the separator meaning.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn separator_convention(&self) -> SeparatorConvention
    {
        self.separator_convention
    }

    /// Returns the leaf boundary rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn boundary(&self) -> BoundaryParams
    {
        self.boundary
    }

    /// Returns the committed bytes of the leaf boundary rule.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the boundary rule's committed bytes, which are a function of
    ///   the rule alone and independent of any record.
    /// - provides: the boundary half of a manifest's digest preimage, so two
    ///   parties disagreeing on the rule cannot agree on a root.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the manifest golden and L3 on independently changed
    ///   mask widths and caps distinguish a default substituted for the carried
    ///   rule, omitted fields and changed framing.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    /// - witness: `params::tests::every_bound_field_moves_the_manifest_digest`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.as_ref().get(1) == Some(&u8::from(self.boundary.mask_bits()))
        && ret.as_ref().get(2..)
            == Some(u64::from(u32::from(self.boundary.record_cap())).to_le_bytes().as_slice()))]
    pub fn boundary_commitment(&self) -> ProfileCommitment
    {
        self.boundary.commitment()
    }

    /// Refuses a parameter set this build cannot honour.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.is_ok() == (self.kind == TreeKind::CURRENT &&
    ///   self.encoding_version == EncodingVersion::CURRENT &&
    ///   self.hash_algorithm == HashAlgorithm::CURRENT &&
    ///   self.separator_convention == SeparatorConvention::CURRENT)` — on
    ///   success every field names the value this build implements, so every
    ///   later step may assume it.
    /// - provides: the gate every encoder, decoder and verifier runs before
    ///   touching bytes, which is what keeps an unimplemented parameter a
    ///   refusal rather than a silently wrong tree.
    /// - fails: [`RecordTreeError::UnsupportedVersion`] for an encoding version
    ///   this build does not write, and
    ///   [`RecordTreeError::IncompatibleParameters`] for any other field.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::UnsupportedVersion`] — the encoding version is not
    /// the current one.
    /// [`RecordTreeError::IncompatibleParameters`] — a field names a value this
    /// build does not implement.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over both representable encoding versions observes
    ///   admission of the current version and the exact old-version refusal
    ///   through sealing. It distinguishes always-accept and always-refuse
    ///   gates; L0 excludes unsupported variants of the other closed
    ///   enumerations.
    /// - witness: `params::tests::the_current_parameters_are_supported`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == (self.kind == TreeKind::CURRENT
            && self.encoding_version == EncodingVersion::CURRENT
            && self.hash_algorithm == HashAlgorithm::CURRENT
            && self.separator_convention == SeparatorConvention::CURRENT))]
    pub fn ensure_supported(&self) -> Result<(), RecordTreeError>
    {
        if self.encoding_version != EncodingVersion::CURRENT {
            return Err(RecordTreeError::UnsupportedVersion {
                version: self.encoding_version.number(),
            });
        }

        if self.kind != TreeKind::CURRENT {
            return Err(RecordTreeError::IncompatibleParameters {
                context: "tree kind".into(),
            });
        }

        if self.hash_algorithm != HashAlgorithm::CURRENT {
            return Err(RecordTreeError::IncompatibleParameters {
                context: "hash algorithm".into(),
            });
        }

        if self.separator_convention != SeparatorConvention::CURRENT {
            return Err(RecordTreeError::IncompatibleParameters {
                context: "separator convention".into(),
            });
        }

        Ok(())
    }
}

impl Default for TreeParams
{
    /// Builds the parameter set newly built trees use.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly what [`TreeParams::current`] returns, so the default
    ///   and the build's own set cannot drift apart.
    /// - provides: the default a caller reaches without naming five fields.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on a manifest sealed with default parameters; the
    ///   independent digest golden distinguishes a default that drifts from the
    ///   committed current profile.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    #[inline]
    #[spec(ensures: |ret| ret == Self::current())]
    fn default() -> Self
    {
        Self::current()
    }
}

/// The manifest that names a tree: its parameters, its record count, and the
/// digest binding them to a root node.
///
/// # The digest is not an agreement decision
///
/// Two roots that differ prove their record sets differ. Two roots that agree
/// prove nothing on their own: a digest is a positive fast path, and an
/// agreement claim has to be settled by the deciding comparison over the record
/// sequences themselves. `PartialEq` on this type is identity of the
/// commitment — the right relation for "is this the root I was handed?" and the
/// wrong one for "do these two trees hold the same records?". The second
/// question has its own answer, on the tree.
///
/// # Specification
/// - requires: nothing.
/// - ensures: equality is byte identity of the manifest's fields.
/// - provides: the context every proof is verified against.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — equality relates two manifests, not one constructed
///   value; sealing and binding carry the executable predicates.
///
/// # Adequacy
/// - hypothesis: L0 derives fieldwise equality; L2 fixes one sealed identity
///   and L3 varies count, node bytes and boundary choices, observing differing
///   digests and the exact refusal for a foreign node. These bounded witnesses
///   do not prove collision resistance or record agreement.
/// - witness: `params::tests::the_manifest_digest_is_pinned`
/// - witness: `params::tests::every_bound_field_moves_the_manifest_digest`
/// - witness: `params::tests::binding_refuses_a_foreign_root_node`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TreeRoot
{
    /// The manifest digest.
    hash: NodeHash,
    /// The committed parameters.
    params: TreeParams,
    /// The committed record count.
    record_count: RecordCount,
}

impl TreeRoot
{
    /// Builds a root manifest from its parts, computing the manifest digest.
    ///
    /// # Specification
    /// - requires: `root_node_hash` is the identity of the node that is the
    ///   tree's root under `params`.
    /// - ensures: the digest is a function of the domain tag, every parameter
    ///   field, the record count and the root node identity — so a root cannot
    ///   be replayed under different parameters or a different count.
    /// - provides: the manifest a proof commits to. The executable
    ///   postcondition checks carried parameters and count; cross-input digest
    ///   binding is observed by the adequacy witnesses.
    /// - fails: [`RecordTreeError::UnsupportedVersion`] or
    ///   [`RecordTreeError::IncompatibleParameters`] when the parameters are
    ///   not ones this build honours, and
    ///   [`RecordTreeError::ArithmeticOverflow`] when the boundary commitment
    ///   exceeds the wire width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::UnsupportedVersion`] — unsupported encoding version.
    /// [`RecordTreeError::IncompatibleParameters`] — unsupported parameter.
    /// [`RecordTreeError::ArithmeticOverflow`] — the boundary commitment
    /// exceeds the wire width.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on one independent digest golden distinguishes encoding
    ///   drift; L3 varies count low and high bytes, node bytes, mask width and
    ///   cap independently, distinguishing omitted inputs. The old encoding
    ///   observes the exact admission failure; collision resistance is not
    ///   established.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    /// - witness: `params::tests::every_bound_field_moves_the_manifest_digest`
    /// - witness: `params::tests::the_current_parameters_are_supported`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |root|
        root.params == params && root.record_count == record_count))]
    pub fn seal(
        params: TreeParams,
        record_count: RecordCount,
        root_node_hash: NodeHash,
    ) -> Result<Self, RecordTreeError>
    {
        params.ensure_supported()?;

        let commitment = params.boundary_commitment();
        let mut bytes = WireBuffer::new();
        bytes.push_word(WireWord::from(u16::from(
            params.encoding_version().number(),
        )));
        bytes.push_tag(params.kind().tag());
        bytes.push_tag(params.hash_algorithm().tag());
        bytes.push_tag(params.separator_convention().tag());
        bytes.push_long(WireLong::from(u64::from(record_count)));
        bytes.push_length_prefixed(
            WireBytes::from(commitment.as_ref()),
            "boundary commitment length".into(),
        )?;
        bytes.push_hash(root_node_hash);

        Ok(Self {
            hash: digest(Domain::Root, bytes.as_bytes()),
            params,
            record_count,
        })
    }

    /// Recomputes the manifest digest and refuses a root that does not match.
    ///
    /// # Specification
    /// - requires: `root_node_hash` is the identity a proof claims as the
    ///   tree's root node.
    /// - ensures: `|ret| ret.is_ok() == Self::seal(self.params,
    ///   self.record_count, root_node_hash).is_ok_and(|recomputed|
    ///   recomputed.hash == self.hash)` — on success `self` is exactly the
    ///   manifest [`TreeRoot::seal`] would produce for its own parameters,
    ///   count and the given node identity — recomputation, never a comparison
    ///   of two carried digests.
    /// - provides: the binding check every proof verification opens with.
    /// - fails: [`RecordTreeError::HashMismatch`] when the recomputed manifest
    ///   differs, and the [`TreeRoot::seal`] failures for bad parameters.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::HashMismatch`] — the claimed root node does not
    /// produce this manifest.
    /// [`RecordTreeError::UnsupportedVersion`] — unsupported encoding version.
    /// [`RecordTreeError::IncompatibleParameters`] — unsupported parameter.
    /// [`RecordTreeError::ArithmeticOverflow`] — the boundary commitment
    /// exceeds the wire width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on one fixed parameter/count tuple observes its
    ///   matching node and a node differing in one byte, with the exact refusal
    ///   and both hash payloads. It distinguishes inverted comparisons and lost
    ///   mismatch identities, not every possible digest collision.
    /// - witness: `params::tests::binding_refuses_a_foreign_root_node`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok()
        == Self::seal(self.params, self.record_count, root_node_hash)
            .is_ok_and(|recomputed| recomputed.hash == self.hash))]
    pub fn ensure_binds(
        &self,
        root_node_hash: NodeHash,
    ) -> Result<(), RecordTreeError>
    {
        let recomputed = Self::seal(self.params, self.record_count, root_node_hash)?;

        if recomputed.hash != self.hash {
            return Err(RecordTreeError::HashMismatch {
                expected: self.hash,
                actual: recomputed.hash,
            });
        }

        Ok(())
    }

    /// Returns the manifest digest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn identity(&self) -> NodeHash
    {
        self.hash
    }

    /// Returns the committed parameters.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> TreeParams
    {
        self.params
    }

    /// Returns the committed record count.
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

#[cfg(test)]
mod tests
{
    use super::EncodingVersion;
    use super::TreeParams;
    use super::TreeRoot;
    use crate::boundary::BoundaryMaskBits;
    use crate::boundary::BoundaryParams;
    use crate::boundary::BoundaryProfile;
    use crate::bytes::NodeHash;
    use crate::error::RecordTreeError;
    use crate::error::WireVersion;
    use crate::record::RecordCount;

    /// A seed byte for a synthetic fixture identity.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct HashSeed(u8);

    /// A node identity built from one seed byte.
    ///
    /// # Specification
    /// - requires: nothing; every seed is admissible.
    /// - ensures: an identity whose first byte is the seed and whose remaining
    ///   bytes are zero, so distinct seeds give distinct identities.
    /// - provides: distinguishable fixture identities for digest and binding
    ///   observations, without claiming they have no preimage.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the manifest golden for seed 17 and L3 against seed
    ///   18 distinguish a changed first byte, nonzero tail or collapsed seeds.
    /// - witness: `params::tests::the_manifest_digest_is_pinned`
    /// - witness: `params::tests::binding_refuses_a_foreign_root_node`
    #[anodized::spec(ensures: |ret| ret.as_ref().first() == Some(&seed.0)
        && ret.as_ref().iter().skip(1).all(|byte| *byte == 0))]
    fn node_hash(seed: HashSeed) -> NodeHash
    {
        let mut bytes = [0_u8; 32_usize];
        bytes[0] = seed.0;

        NodeHash::from(bytes)
    }

    #[test]
    fn version_admits_only_the_current_number()
    {
        for raw in 0_u16 ..= u16::MAX {
            let number = WireVersion::from(raw);
            let expected = if raw == 2 {
                Ok(EncodingVersion::V2)
            }
            else {
                Err(RecordTreeError::UnsupportedVersion { version: number })
            };
            assert_eq!(EncodingVersion::from_number(number), expected);
        }
    }

    #[test]
    fn the_current_parameters_are_supported()
    {
        assert_eq!(TreeParams::current().ensure_supported(), Ok(()));
        let current = TreeParams::current();
        let previous = TreeParams::new(
            current.kind(),
            EncodingVersion::V1,
            current.hash_algorithm(),
            current.separator_convention(),
            current.boundary(),
        );
        assert_eq!(
            TreeRoot::seal(previous, RecordCount::ZERO, node_hash(HashSeed(17))),
            Err(RecordTreeError::UnsupportedVersion {
                version: WireVersion::from(1_u16)
            }),
        );
    }

    #[test]
    fn the_manifest_digest_is_pinned()
    {
        let root = TreeRoot::seal(
            TreeParams::default(),
            RecordCount::from(3_u64),
            node_hash(HashSeed(0x11_u8)),
        )
        .expect("the current parameters are supported");

        // Hand check of the version field: the manifest opens with the
        // encoding version, which is 2 and writes as a little-endian word,
        // low byte 0x02 then high byte 0x00, ahead of the kind, hash-algorithm
        // and separator tags.
        assert_eq!(
            alloc::format!("{}", root.identity()),
            "21108e2d96eadee04428a21ac7d578d6c18b0047d677818bc9b3ec28c2e1cf8e"
        );
    }

    #[test]
    fn every_bound_field_moves_the_manifest_digest()
    {
        let base = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(3_u64),
            node_hash(HashSeed(0x11_u8)),
        )
        .expect("the current parameters are supported");

        let other_count = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(4_u64),
            node_hash(HashSeed(0x11_u8)),
        )
        .expect("the current parameters are supported");
        assert_ne!(base.identity(), other_count.identity());

        let other_node = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(3_u64),
            node_hash(HashSeed(0x12_u8)),
        )
        .expect("the current parameters are supported");
        assert_ne!(base.identity(), other_node.identity());

        let other_boundary = TreeRoot::seal(
            TreeParams::new(
                TreeParams::current().kind(),
                TreeParams::current().encoding_version(),
                TreeParams::current().hash_algorithm(),
                TreeParams::current().separator_convention(),
                BoundaryParams::new(
                    BoundaryProfile::CURRENT,
                    BoundaryMaskBits::try_from(5_u8).expect("five is admissible"),
                    TreeParams::current().boundary().record_cap(),
                ),
            ),
            RecordCount::from(3_u64),
            node_hash(HashSeed(0x11_u8)),
        )
        .expect("the current parameters are supported");
        assert_ne!(base.identity(), other_boundary.identity());

        let high_count = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(0x0100_0000_0000_0003_u64),
            node_hash(HashSeed(0x11)),
        )
        .expect("the current parameters are supported");
        assert_ne!(base.identity(), high_count.identity());

        let other_tail = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(3_u64),
            NodeHash::from([0x11_u8; 32]),
        )
        .expect("the current parameters are supported");
        assert_ne!(base.identity(), other_tail.identity());

        let current = TreeParams::current();
        let capped = TreeParams::new(
            current.kind(),
            current.encoding_version(),
            current.hash_algorithm(),
            current.separator_convention(),
            BoundaryParams::new(
                current.boundary().profile(),
                current.boundary().mask_bits(),
                crate::boundary::BoundaryRecordCap::try_from(65_u32).expect("65 is admissible"),
            ),
        );
        let other_cap = TreeRoot::seal(capped, RecordCount::from(3_u64), node_hash(HashSeed(0x11)))
            .expect("the changed cap is supported");
        assert_ne!(base.identity(), other_cap.identity());
    }

    #[test]
    fn binding_refuses_a_foreign_root_node()
    {
        let root = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(3_u64),
            node_hash(HashSeed(0x11_u8)),
        )
        .expect("the current parameters are supported");

        assert_eq!(root.ensure_binds(node_hash(HashSeed(0x11_u8))), Ok(()));

        let foreign = TreeRoot::seal(
            TreeParams::current(),
            RecordCount::from(3_u64),
            node_hash(HashSeed(0x12_u8)),
        )
        .expect("the current parameters are supported");
        assert_eq!(
            root.ensure_binds(node_hash(HashSeed(0x12_u8))),
            Err(RecordTreeError::HashMismatch {
                expected: root.identity(),
                actual: foreign.identity(),
            })
        );
    }
}
