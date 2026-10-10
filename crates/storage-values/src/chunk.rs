//! The chunk image, its domain, and the store that holds chunks.
//!
//! A chunk is a **framed token body**, and the frame — domain first — is
//! inside the hashed preimage. That is what lets one backing object serve both
//! storage planes: a value chunk opens with [`CHUNK_DOMAIN`] where a record
//! plane node opens with its own header, so no byte string is a candidate for
//! both validators and none can be handed to the wrong one.
//!
//! # The frame
//!
//! ```text
//! image  := "gandr:storage-values:chunk:v1"
//!        || u16le chunk format version
//!        || u64le token count
//!        || u64le body length in bytes
//!        || body
//! digest := BLAKE3(image)
//! ```
//!
//! Every integer is little-endian at a fixed width, so a digest never inherits
//! a target's endianness or pointer width; the specification suite checks a
//! committed golden image and digest.
//!
//! # Verified chunks
//!
//! [`VerifiedChunk`] is obtainable only by [`verify_chunk_image`] — which
//! recomputes the digest and re-reads the frame, the body's records and their
//! count — or by [`frame_chunk`], which computed them. [`ChunkStore::insert`]
//! takes one and [`ChunkStore::load`] must return one, so both sides of every
//! store verify by construction: a store that returned bytes under a digest
//! they do not hash to cannot produce the value its signature demands.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_storage_chunker::TokenCount;

use crate::error::ChunkFrameField;
use crate::error::ValueError;
use crate::error::ValueQuantity;
use crate::ptr::ChunkDigest;
use crate::tokens::BodyFront;
use crate::tokens::split_record;
use crate::units::ChunkCount;
use crate::units::ChunkFormatVersion;
use crate::units::ChunkImage;
use crate::units::ChunkImageBuf;
use crate::units::TokenBody;

/// The domain every chunk image opens with, inside the hashed preimage.
pub const CHUNK_DOMAIN: &[u8] = b"gandr:storage-values:chunk:v1";

/// The frame header after the domain: a `u16` version and two `u64` fields.
const CHUNK_HEADER_LEN: usize = 0x12_usize;

/// A framed chunk image and the digest it is claimed to hash to, unverified.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StoredChunkRef<'image>
{
    /// The digest claimed for `image`.
    digest: ChunkDigest,
    /// The framed image bytes.
    image: ChunkImage<'image>,
}

impl<'image> StoredChunkRef<'image>
{
    /// Pairs a claimed digest with a framed chunk image.
    ///
    /// # Specification
    /// - requires: nothing; the claim is what [`verify_chunk_image`] checks.
    /// - ensures: the claim carries both unchanged.
    /// - provides: the shape a store backend hands to the verifier.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 a wrong digest and independently malformed frames are
    ///   refused by their exact fields after passing through the claim. These
    ///   distinguish substitution of either the offered digest or image.
    /// - witness: `tests::frame::each_frame_field_is_refused_by_name`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.digest == digest && ret.image == image)]
    pub fn new(
        digest: ChunkDigest,
        image: ChunkImage<'image>,
    ) -> Self
    {
        Self { digest, image }
    }

    /// Returns the claimed digest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> ChunkDigest
    {
        self.digest
    }

    /// Returns the framed image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn image(&self) -> ChunkImage<'image>
    {
        self.image
    }
}

/// A chunk image whose digest, frame, records and token count have been
/// checked.
///
/// # Specification
/// - requires: construction by verification or borrowing a locally framed
///   chunk.
/// - ensures: the image authenticates, its frame and record count agree, and
///   the body is the exact slice inside that image rather than an equal copy.
/// - provides: checked chunk material without a second owned body.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on empty and three-record bodies observes accepted
///   refinements, literal token counts and the exact borrowed body view.
///   Changed digests, cached counts and an equal body outside the frame are
///   rejected. L2 pins the nonempty frame image and digest; L3 names each
///   malformed frame field. Allocation and timing costs are not measured.
/// - witness: `chunk::tests::chunk_refinements_bind_the_body_view_count_and_digest`
/// - witness: `tests::frame::a_chunk_digest_matches_its_committed_golden`
/// - witness: `tests::frame::each_frame_field_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[spec(maintains: verify_chunk_image(StoredChunkRef::new(self.digest, self.image))
    .is_ok_and(|checked| checked.token_count == self.token_count
        && core::ptr::eq(core::ptr::from_ref(checked.body.as_ref()), core::ptr::from_ref(self.body.as_ref()))))]
pub struct VerifiedChunk<'image>
{
    /// The digest the image hashes to.
    digest: ChunkDigest,
    /// The framed image bytes.
    image: ChunkImage<'image>,
    /// The token body inside the frame.
    body: TokenBody<'image>,
    /// The number of records in the body.
    token_count: TokenCount,
}

impl<'image> VerifiedChunk<'image>
{
    /// Returns the digest the image hashes to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> ChunkDigest
    {
        self.digest
    }

    /// Returns the framed image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn image(&self) -> ChunkImage<'image>
    {
        self.image
    }

    /// Returns the token body inside the frame.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> TokenBody<'image>
    {
        self.body
    }

    /// Returns the number of records in the body.
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

/// An owned chunk image this crate framed, with its digest.
///
/// # Specification
/// - requires: construction by `frame_chunk`.
/// - ensures: the owned image authenticates and its declared record count
///   equals the retained count; it can be borrowed as verified material.
/// - provides: ownership of one canonical chunk image.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on empty and three-record bodies observes accepted
///   refinements, literal token counts and the exact borrowed body view.
///   Changed digests, cached counts and an equal body outside the frame are
///   rejected. L2 pins the nonempty frame image and digest; L3 names each
///   malformed frame field. Allocation and timing costs are not measured.
/// - witness: `chunk::tests::chunk_refinements_bind_the_body_view_count_and_digest`
/// - witness: `tests::frame::a_chunk_digest_matches_its_committed_golden`
/// - witness: `tests::frame::each_frame_field_is_refused_by_name`
#[derive(Clone, Debug, Eq, PartialEq)]
#[spec(maintains: verify_chunk_image(StoredChunkRef::new(self.digest, self.image.as_image()))
    .is_ok_and(|checked| checked.token_count == self.token_count))]
pub struct FramedChunk
{
    /// The digest the image hashes to.
    digest: ChunkDigest,
    /// The framed image.
    image: ChunkImageBuf,
    /// The number of records in the body.
    token_count: TokenCount,
}

impl FramedChunk
{
    /// Returns the digest the image hashes to.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> ChunkDigest
    {
        self.digest
    }

    /// Returns the framed image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn image(&self) -> ChunkImage<'_>
    {
        self.image.as_image()
    }

    /// Borrows the chunk as verified, without hashing it again.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the verified chunk carries this chunk's digest, image, token
    ///   count and the body after the frame header — what
    ///   [`verify_chunk_image`] would return for the same image.
    /// - provides: the insert path for a chunk this crate just framed, which
    ///   [`frame_chunk`] already hashed and scanned.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 empty and three-record images retain their literal
    ///   counts and the body view inside the frame. L1 a freshly framed image
    ///   survives store insertion and load; wrong fields make the refinement
    ///   false. These observations do not measure hashing or allocation cost.
    /// - witness: `chunk::tests::chunk_refinements_bind_the_body_view_count_and_digest`
    /// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| verify_chunk_image(StoredChunkRef::new(self.digest, self.image.as_image())) == Ok(ret))]
    pub fn as_verified(&self) -> VerifiedChunk<'_>
    {
        let image: &[u8] = self.image.as_ref();
        let header = CHUNK_DOMAIN.len().saturating_add(CHUNK_HEADER_LEN);
        let body = image.get(header ..).unwrap_or_default();

        VerifiedChunk {
            digest: self.digest,
            image: self.image.as_image(),
            body: TokenBody::from(body),
            token_count: self.token_count,
        }
    }
}

/// The verified backing store for value-plane chunks.
///
/// A sibling of the record plane's node store rather than a use of it: that
/// store decodes its bytes as nodes, which a chunk body is not. One backing
/// object may implement both.
///
/// # Specification
/// - requires: implementations verify loaded images before returning them.
/// - ensures: a fresh digest retains its offered image; an existing digest
///   retains its prior bytes, and every load rechecks their integrity.
/// - provides: content-addressed, first-write-wins storage, not a proof that
///   two offered images agree merely because their digests agree.
/// - panics: none.
/// - executable: none — required-method instrumentation adds implementation
///   hooks and associated constants, changing implementor obligations and
///   object compatibility. Concrete bodies carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 the concrete memory store refuses an absent digest, returns
///   a freshly inserted image, preserves existing bytes on reinsertion and
///   refuses a corrupted image on a fresh load. These observations separate
///   dropped writes, replacement on duplicate insertion and trusted stale
///   verification; they do not establish every external backend's behavior.
/// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
pub trait ChunkStore
{
    /// Inserts a verified chunk under its digest.
    ///
    /// # Specification
    /// - requires: nothing; the argument's type is the verification.
    /// - ensures: a newly inserted digest loads as the offered image while the
    ///   stored bytes remain unchanged. An existing digest retains its prior
    ///   bytes; reinsertion neither compares nor repairs them.
    /// - provides: the write half of the content-addressed store.
    /// - fails: [`ValueError`] when the backend refuses.
    /// - panics: none.
    /// - executable: none — this required method has no body; instrumentation
    ///   changes implementation hooks and object compatibility.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 the concrete memory store refuses an absent digest,
    ///   returns a freshly inserted image, preserves existing bytes on
    ///   reinsertion and refuses a corrupted image on a fresh load. These
    ///   observations separate dropped writes, replacement on duplicate
    ///   insertion and trusted stale verification; they do not establish every
    ///   external backend's behavior.
    /// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
    fn insert(
        &mut self,
        chunk: VerifiedChunk<'_>,
    ) -> Result<(), ValueError>;

    /// Loads the chunk stored under a digest, verifying it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the chunk hashes to `digest` and its frame reads —
    ///   the return type admits nothing else.
    /// - provides: the read half, verified on every load so bit rot or a bad
    ///   backend is caught here rather than inside a decoder.
    /// - fails: [`ValueError::UnknownChunk`] when nothing is held under the
    ///   digest, and [`verify_chunk_image`]'s refusals for what is held.
    /// - panics: none.
    /// - executable: none — this required method has no body; instrumentation
    ///   changes implementation hooks and object compatibility.
    ///
    /// # Errors
    /// [`ValueError`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 the concrete memory store refuses an absent digest,
    ///   returns a freshly inserted image, preserves existing bytes on
    ///   reinsertion and refuses a corrupted image on a fresh load. These
    ///   observations separate dropped writes, replacement on duplicate
    ///   insertion and trusted stale verification; they do not establish every
    ///   external backend's behavior.
    /// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
    fn load(
        &self,
        digest: ChunkDigest,
    ) -> Result<VerifiedChunk<'_>, ValueError>;
}

/// A deterministic in-memory [`ChunkStore`].
///
/// # Specification
/// - requires: backing bytes are not assumed to remain authentic.
/// - ensures: fresh insertion retains the image; duplicate insertion preserves
///   the prior bytes, and load verifies against the requested digest anew.
/// - provides: the deterministic memory implementation of `ChunkStore`.
/// - panics: none.
/// - executable: none — these are transition and fresh-verification laws.
///   Assuming all backing bytes are valid would exclude the corruption that
///   loading must refuse; the concrete methods check their own operations.
///
/// # Adequacy
/// - hypothesis: L3 the concrete memory store refuses an absent digest, returns
///   a freshly inserted image, preserves existing bytes on reinsertion and
///   refuses a corrupted image on a fresh load. These observations separate
///   dropped writes, replacement on duplicate insertion and trusted stale
///   verification; they do not establish every external backend's behavior.
/// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct InMemoryChunkStore
{
    /// Framed chunk images keyed by their digest.
    chunks: BTreeMap<ChunkDigest, ChunkImageBuf>,
}

impl InMemoryChunkStore
{
    /// Opens an empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            chunks: BTreeMap::new(),
        }
    }

    /// Returns the number of distinct chunks held.
    ///
    /// The structural-sharing observable: two commits of values sharing a
    /// subtree add the subtree's chunks once between them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chunk_count(&self) -> ChunkCount
    {
        ChunkCount::from(self.chunks.len())
    }
}

impl ChunkStore for InMemoryChunkStore
{
    /// Inserts a verified chunk, copying its image once if it is new.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh digest maps to the offered image; an existing digest
    ///   keeps its prior bytes, without assuming that they match the offer.
    /// - provides: the in-memory write half.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Errors
    /// None in practice; the signature is the trait's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 the concrete memory store refuses an absent digest,
    ///   returns a freshly inserted image, preserves existing bytes on
    ///   reinsertion and refuses a corrupted image on a fresh load. These
    ///   observations separate dropped writes, replacement on duplicate
    ///   insertion and trusted stale verification; they do not establish every
    ///   external backend's behavior.
    /// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
    #[inline]
    #[spec(captures: vacant = !self.chunks.contains_key(&chunk.digest()),
        ensures: |ret| ret.is_ok() && self.chunks.get(&chunk.digest())
            .is_some_and(|image| !vacant || image.as_ref() == chunk.image().as_ref()))]
    fn insert(
        &mut self,
        chunk: VerifiedChunk<'_>,
    ) -> Result<(), ValueError>
    {
        self.chunks
            .entry(chunk.digest())
            .or_insert_with(|| ChunkImageBuf::from(Box::<[u8]>::from(chunk.image().as_ref())));

        Ok(())
    }

    /// Loads and re-verifies the image held under a digest.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`ChunkStore::load`].
    /// - provides: the in-memory read half.
    /// - fails: [`ValueError::UnknownChunk`], and [`verify_chunk_image`]'s
    ///   refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 the concrete memory store refuses an absent digest,
    ///   returns a freshly inserted image, preserves existing bytes on
    ///   reinsertion and refuses a corrupted image on a fresh load. These
    ///   observations separate dropped writes, replacement on duplicate
    ///   insertion and trusted stale verification; they do not establish every
    ///   external backend's behavior.
    /// - witness: `chunk::tests::reinsertion_preserves_existing_bytes_and_load_rechecks_them`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|chunk| chunk.digest() == digest)
        && (self.chunks.contains_key(&digest) || ret == Err(ValueError::UnknownChunk { digest })))]
    fn load(
        &self,
        digest: ChunkDigest,
    ) -> Result<VerifiedChunk<'_>, ValueError>
    {
        let Some(image) = self.chunks.get(&digest)
        else {
            return Err(ValueError::UnknownChunk { digest });
        };

        verify_chunk_image(StoredChunkRef::new(digest, image.as_image()))
    }
}

/// Checks a claimed chunk: its digest, its frame, its records and their
/// count.
///
/// # Specification
/// - requires: nothing; every rejection is named.
/// - ensures: success exactly when the image hashes to the claimed digest,
///   opens with [`CHUNK_DOMAIN`], carries [`ChunkFormatVersion::V1`], declares
///   a body length equal to the bytes after the header, and that body is a
///   sequence of well-formed records numbering the declared token count; the
///   verified chunk then borrows its body out of the image.
/// - provides: the one verification both store halves run, so no implementation
///   can verify one side and not the other.
/// - fails: [`ValueError::DigestMismatch`] first, then
///   [`ValueError::MalformedChunk`] naming the first field that fails, in frame
///   order.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L3 only — each field is separated by an image wrong in that
///   field alone, and the domain by a record plane node image offered under its
///   own BLAKE3, which must be refused for its domain rather than a downstream
///   field.
/// - witness: `tests::frame::a_record_plane_node_image_is_refused_as_a_chunk`
/// - witness: `tests::frame::each_frame_field_is_refused_by_name`
#[inline]
#[spec(ensures: |ret| ret
    .as_ref()
    .ok()
    .is_none_or(|chunk| chunk.digest() == claim.digest() && chunk.image() == claim.image()))]
pub fn verify_chunk_image(claim: StoredChunkRef<'_>) -> Result<VerifiedChunk<'_>, ValueError>
{
    let image: &[u8] = claim.image().into();
    let actual = ChunkDigest::from(*blake3::hash(image).as_bytes());
    if actual != claim.digest() {
        return Err(ValueError::DigestMismatch {
            expected: claim.digest(),
            actual,
        });
    }

    let refused = |field: ChunkFrameField| ValueError::MalformedChunk { field };

    let Some(rest) = image.strip_prefix(CHUNK_DOMAIN)
    else {
        return Err(refused(ChunkFrameField::Domain));
    };
    let Some((version, rest)) = rest.split_first_chunk::<2>()
    else {
        return Err(refused(ChunkFrameField::Header));
    };
    if ChunkFormatVersion::from(u16::from_le_bytes(*version)) != ChunkFormatVersion::V1 {
        return Err(refused(ChunkFrameField::Version));
    }
    let Some((declared_count, rest)) = rest.split_first_chunk::<8>()
    else {
        return Err(refused(ChunkFrameField::Header));
    };
    let Some((declared_length, body)) = rest.split_first_chunk::<8>()
    else {
        return Err(refused(ChunkFrameField::Header));
    };
    if u64::try_from(body.len()).ok() != Some(u64::from_le_bytes(*declared_length)) {
        return Err(refused(ChunkFrameField::BodyLength));
    }

    let body = TokenBody::from(body);
    let token_count = count_records(body)?;
    if token_count != TokenCount::from(u64::from_le_bytes(*declared_count)) {
        return Err(refused(ChunkFrameField::TokenCount));
    }

    Ok(VerifiedChunk {
        digest: actual,
        image: claim.image(),
        body,
        token_count,
    })
}

/// Frames a token body into a chunk image and hashes it.
///
/// # Specification
/// - requires: nothing; a body that is not well-formed records is refused.
/// - ensures: on success the image is exactly the frame this module documents,
///   carrying the number of records in `body`, and the digest is BLAKE3 over
///   the whole image, domain included; [`verify_chunk_image`] accepts the pair.
/// - provides: the only way a chunk comes into existence, so the frame cannot
///   be rebuilt by a caller and drift from the verifier.
/// - fails: [`ValueError::MalformedChunk`] naming the records when `body` is
///   not a sequence of well-formed records, and an overflow refusal when a
///   length or count passes its width.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the framed image of a fixed body hashes to a
///   golden pinned in the suite, and reads back field by field — plus L3 for
///   the malformed-body refusal.
/// - witness: `tests::frame::a_chunk_digest_matches_its_committed_golden`
/// - witness: `tests::frame::a_malformed_body_is_never_framed`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|chunk| {
    verify_chunk_image(StoredChunkRef::new(chunk.digest(), chunk.image()))
        .is_ok_and(|verified| verified.body() == body)
}))]
pub fn frame_chunk(body: TokenBody<'_>) -> Result<FramedChunk, ValueError>
{
    let token_count = count_records(body)?;
    let bytes: &[u8] = body.into();
    let Ok(length) = u64::try_from(bytes.len())
    else {
        return Err(ValueError::ArithmeticOverflow {
            quantity: ValueQuantity::ByteLength,
        });
    };

    let capacity = CHUNK_DOMAIN
        .len()
        .checked_add(CHUNK_HEADER_LEN)
        .and_then(|header| header.checked_add(bytes.len()))
        .ok_or(ValueError::ArithmeticOverflow {
            quantity: ValueQuantity::ByteLength,
        });
    let mut image = Vec::with_capacity(capacity?);
    image.extend_from_slice(CHUNK_DOMAIN);
    image.extend_from_slice(u16::from(ChunkFormatVersion::V1).to_le_bytes().as_slice());
    image.extend_from_slice(u64::from(token_count).to_le_bytes().as_slice());
    image.extend_from_slice(length.to_le_bytes().as_slice());
    image.extend_from_slice(bytes);

    Ok(FramedChunk {
        digest: ChunkDigest::from(*blake3::hash(image.as_slice()).as_bytes()),
        image: ChunkImageBuf::from(image.into_boxed_slice()),
        token_count,
    })
}

/// Counts the records of a body, refusing one that is not well-formed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the number of records the body splits into with no
///   bytes left over.
/// - provides: the record scan both framing and verification share.
/// - fails: [`ValueError::MalformedChunk`] naming the records, and an overflow
///   refusal at the count's width.
/// - panics: none.
///
/// # Errors
/// [`ValueError`] — as listed above.
///
/// # Adequacy
/// - hypothesis: L3 empty and three-record bodies return literal counts;
///   invalid tags and truncated word or open records are refused as malformed
///   records. These separate off-by-one counts and accepted truncation.
///   Width-overflow arms are outside this finite corpus.
/// - witness: `chunk::tests::chunk_refinements_bind_the_body_view_count_and_digest`
/// - witness: `tests::frame::a_malformed_body_is_never_framed`
#[spec(ensures: |ret| ret
    .as_ref()
    .ok()
    .is_none_or(|count| u64::from(*count) <= u64::try_from(body.as_ref().len()).unwrap_or(u64::MAX)))]
fn count_records(body: TokenBody<'_>) -> Result<TokenCount, ValueError>
{
    let mut count = 0_u64;
    let mut remaining = body;

    loop {
        let front = split_record(remaining).map_err(|_fault| ValueError::MalformedChunk {
            field: ChunkFrameField::Records,
        });
        let BodyFront::Record(_record, rest) = front?
        else {
            return Ok(TokenCount::from(count));
        };
        let Some(next) = count.checked_add(1_u64)
        else {
            return Err(ValueError::ArithmeticOverflow {
                quantity: ValueQuantity::TokenCount,
            });
        };
        count = next;
        remaining = rest;
    }
}

#[cfg(test)]
mod tests
{
    use gandr_storage_chunker::TokenCount;

    use crate::ChunkDigest;
    use crate::ChunkStore as _;
    use crate::InMemoryChunkStore;
    use crate::TokenBody;
    use crate::ValueError;
    use crate::frame_chunk;

    #[test]
    fn reinsertion_preserves_existing_bytes_and_load_rechecks_them()
    {
        let first =
            frame_chunk(TokenBody::from([0x05_u8].as_slice())).expect("one close record frames");
        let other = frame_chunk(TokenBody::from([0x05_u8, 0x05_u8].as_slice()))
            .expect("two close records frame");
        let mut store = InMemoryChunkStore::new();
        assert_eq!(
            store.load(first.digest()),
            Err(ValueError::UnknownChunk {
                digest: first.digest()
            })
        );
        store
            .insert(first.as_verified())
            .expect("the fresh image stores");
        assert_eq!(store.load(first.digest()), Ok(first.as_verified()));
        let altered = other.digest();
        let _prior = store.chunks.insert(first.digest(), other.image);
        assert_eq!(store.insert(first.as_verified()), Ok(()));
        assert_eq!(
            store.load(first.digest()),
            Err(ValueError::DigestMismatch {
                expected: first.digest(),
                actual: altered,
            })
        );
    }

    #[test]
    fn chunk_refinements_bind_the_body_view_count_and_digest()
    {
        let compound = [
            0x01_u8, 0x2a_u8, 0x02_u8, 7_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0_u8, 0x05_u8,
        ];
        for (body, count) in [([].as_slice(), 0_u64), (compound.as_slice(), 3_u64)] {
            let mut framed =
                frame_chunk(TokenBody::from(body)).expect("the record sequence frames");
            assert!(anodized::types::Spec::predicate(&framed));
            let mut checked = framed.as_verified();
            assert_eq!(checked.token_count(), TokenCount::from(count));
            assert!(anodized::types::Spec::predicate(&checked));
            let expected_count = checked.token_count;
            checked.token_count = TokenCount::from(u64::MAX);
            assert!(!anodized::types::Spec::predicate(&checked));
            checked.token_count = expected_count;
            if !body.is_empty() {
                let view = checked.body;
                checked.body = TokenBody::from(body);
                assert!(!anodized::types::Spec::predicate(&checked));
                checked.body = view;
            }
            let mut digest = <[u8; 32]>::try_from(checked.digest.as_ref())
                .expect("the digest has its fixed width");
            digest[0_usize] ^= 1_u8;
            let changed_digest = ChunkDigest::from(digest);
            checked.digest = changed_digest;
            assert!(!anodized::types::Spec::predicate(&checked));
            framed.token_count = TokenCount::from(u64::MAX);
            assert!(!anodized::types::Spec::predicate(&framed));
            framed.token_count = expected_count;
            framed.digest = changed_digest;
            assert!(!anodized::types::Spec::predicate(&framed));
        }
    }
}
