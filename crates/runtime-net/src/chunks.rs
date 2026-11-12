//! The chunk wire: a committed value's chunks fetched by content from the
//! peer that holds them, on a connection of its own under [`CHUNKS_ALPN`],
//! apart from every stream a program holds.
//!
//! [`Chunks`] is the store a host commits a run's values into and its
//! endpoint serves them from; clones share it. A fetch asks once. The asker
//! sends the manifest of the value it wants, then the manifest of each value
//! whose chunks it holds whole, and finishes its side. The holder answers
//! with every chunk of the wanted value's closure that no held value's
//! closure contains, each under its digest, and finishes. Each is a part as
//! every wire frames one ([`Framed`]):
//!
//! ```text
//! request     := part(wanted) part(held)*
//! answer      := part(digest || image)*
//! ```
//!
//! The asker verifies every chunk against the digest it came under before it
//! inserts any, then walks the wanted value's closure over its store. One
//! round trip fetches a value of any depth, and a second fetch of an edited
//! value, naming the first as held, carries only the chunks the edit changed.
//!
//! # Boundaries
//!
//! - **Integrity, not validity.** A chunk that verifies is the bytes its digest
//!   names. That the value it encodes is one its reader may read at the type it
//!   expects rests on both ends running one program.
//! - **The holder answers what it can.** A holder that lacks a chunk of the
//!   wanted closure answers nothing, and the asker's walk refuses the value by
//!   the first chunk neither end holds. A held value whose closure the holder
//!   lacks is passed over, and the chunks it shares are carried again.
//! - **Held is the asker's word.** A value named held whose closure the asker
//!   lacks leaves its walk to refuse the chunk missing.
//! - **What verified is kept.** A chunk that does not verify refuses the answer
//!   before any chunk is inserted; a closure left incomplete keeps the chunks
//!   that arrived, each verified.
//! - **In memory, never evicted.** The holder keeps every chunk committed or
//!   fetched, and every dead copy, for as long as a clone of it lives.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: § 5's
//!   `CAMCommit` at one LAM and `CAMDeref` at another through one CAM; the
//!   wire fills the second end's part of that CAM.
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage
//!   programme, § storage-programme-worlds-sessions: a value migrates as a
//!   commit at its source and a deref at its destination, through one logical
//!   content-addressed store.
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: integrity never
//!   substitutes validity, § kernel-verdict-reuse: a chunk verified on receipt
//!   is integrity only, and no verdict crosses with it.
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — lineage: the store's single
//!   writer plan, which removes every lock around a chunk store: the holder's
//!   puts take `&self`, since two puts of one chunk publish one slot.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;

use anodized::spec;
use gandr_storage_values::CHUNK_DIGEST_LEN;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkImage;
use gandr_storage_values::ChunkImageBuf;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::StoredChunkRef;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::VerifiedChunk;
use gandr_storage_values::verify_chunk_image;

use crate::endpoint::Fault;
use crate::frame::Framed;
use crate::frame::Malformed;
use crate::frame::Oversized;
use crate::frame::Part;
use crate::frame::Parts;
use crate::peer::NodeId;

/// The protocol name a holder answers fetches under, offered beside
/// [`ALPN`](crate::ALPN) by every endpoint.
pub const CHUNKS_ALPN: &[u8] = b"gandr/chunks/0";

/// The chunks a host holds: what its run commits and fetches, and what its
/// endpoint serves.
///
/// Clones share one holder, and threads put into it and load from it through
/// `&self`, with no lock: `&Chunks` is a [`ChunkStore`].
#[derive(Clone, Debug, Default)]
#[repr(transparent)]
pub struct Chunks(Arc<Held>);

/// The images of a holder and the index of their slots.
///
/// The arena, a `boxcar::Vec`, grows by buckets and never moves an element,
/// so an image stays at its address for the life of the holder, and a load
/// lends it from there. The index, a `papaya::HashMap`, maps each digest to
/// its slot. A put probes the index, pushes the image on a miss, and then
/// publishes the slot. A read of the index happens after the write that it
/// reads, so a reader that finds a slot reads the whole image. Two puts of one
/// chunk that race both push, and the index keeps the first slot: the second
/// image stays in the arena, dead.
#[derive(Debug, Default)]
struct Held
{
    /// Each image, at a fixed address for the life of the holder.
    images: boxcar::Vec<ChunkImageBuf>,
    /// The slot of each digest's image in `images`, published after the
    /// image.
    slots: papaya::HashMap<ChunkDigest, usize>,
}

impl Chunks
{
    /// An empty holder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The count of distinct chunks the holder keeps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chunk_count(&self) -> ChunkCount
    {
        ChunkCount::from(self.0.slots.len())
    }

    /// Keep `chunk`, unless the holder keeps its digest already.
    ///
    /// # Specification
    /// - requires: nothing; the argument's type is the verification.
    /// - ensures: the index maps the chunk's digest to a slot of the arena. A
    ///   fresh digest maps to a copy of the offered image. A digest the index
    ///   holds keeps its slot. A put that loses a race for a fresh digest
    ///   leaves its copy in the arena, dead, and the index keeps the slot of
    ///   the winner.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: which of two racing puts
    ///   wins is the scheduler's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sixteen threads that put one chunk at once leave one
    ///   digest in the index, and every thread loads the same image.
    /// - witness: `tests::chunks::sixteen_puts_of_one_chunk_leave_one_digest_6899`
    fn put(
        &self,
        chunk: VerifiedChunk<'_>,
    )
    {
        let slots = self.0.slots.pin();
        let digest = chunk.digest();
        if slots.contains_key(&digest) {
            return;
        }
        let slot = self.0.images.push(ChunkImageBuf::from(Box::<[u8]>::from(
            chunk.image().as_ref(),
        )));
        // The push returns once the image is in place, so the slot publishes
        // after it. A lost race leaves the pushed image dead.
        drop(slots.try_insert(digest, slot));
    }

    /// The answer to `request` from this store: every chunk of the wanted
    /// closure that no held closure contains, in digest order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, one part per chunk of the wanted value's closure
    ///   outside the closures of the held values this store holds whole; no
    ///   part when this store lacks a chunk of the wanted closure.
    /// - fails: [`Unanswered::Malformed`] for a request this protocol does not
    ///   frame or that names no wanted value, [`Unanswered::Refused`] for a
    ///   manifest that does not decode or a held chunk that does not verify,
    ///   and [`Unanswered::Oversized`] for a chunk longer than a part.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: which chunks the asker
    ///   holds is the asker's, and the answer is checked where it is read.
    ///
    /// # Errors
    /// As the failures above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first fetch carries the whole closure, a second
    ///   naming the first as held carries exactly the chunks the edit added,
    ///   and a value the holder lacks is answered with no part.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    /// - witness: `tests::chunks::a_value_the_holder_lacks_is_refused_by_its_first_chunk`
    pub(super) fn answer(
        &self,
        request: &Framed,
    ) -> Result<Framed, Unanswered>
    {
        let mut parts = Parts(request.as_ref());
        let Some(wanted) = parts.next()
        else {
            return Err(Unanswered::Malformed);
        };
        let wanted = wanted?;
        let wanted = ValueManifest::decode(wanted.manifest())?;
        // A holder that lacks a chunk of the closure answers nothing; the
        // asker's walk names the chunk.
        let Ok(closure) = wanted.closure(&self)
        else {
            return Ok(Framed::default());
        };
        let mut held = BTreeSet::new();
        for part in parts {
            let part = part?;
            let manifest = ValueManifest::decode(part.manifest())?;
            // A held value whose closure this store lacks is passed over, and
            // the chunks it shares are carried.
            if let Ok(shared) = manifest.closure(&self) {
                held.extend(BTreeSet::from(shared));
            }
        }
        let mut answer = Framed::default();
        for &digest in closure.digests().difference(&held) {
            let chunk = self.load(digest)?;
            answer.push(&[Part(digest.as_ref()), Part(chunk.image().into())])?;
        }
        Ok(answer)
    }

    /// Verify every chunk `answer` carries from `peer`, insert them, and walk
    /// the closure of `wanted` over this store.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, this store holds `wanted`'s whole closure, and
    ///   the count is of the chunks the answer carried and their images' bytes.
    ///   A chunk that does not verify, or a part that does not frame, is
    ///   refused before any chunk is inserted.
    /// - fails: [`Fault::Malformed`] for an answer this protocol does not
    ///   frame; [`Fault::Refused`] for a chunk that does not verify against its
    ///   digest, and for the first chunk of the closure neither end holds.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: whether the chunks came
    ///   from `peer` is the connection's.
    ///
    /// # Errors
    /// As the failures above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a whole answer is kept and derefs equal; a tampered
    ///   chunk and a part shorter than a digest are refused with nothing kept;
    ///   a value the holder lacks is refused by its root chunk.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    /// - witness: `tests::chunks::an_answer_that_does_not_verify_or_frame_is_refused_before_any_chunk_is_kept`
    /// - witness: `tests::chunks::a_value_the_holder_lacks_is_refused_by_its_first_chunk`
    pub(super) fn admit(
        &self,
        peer: NodeId,
        wanted: &ValueManifest,
        answer: &Framed,
    ) -> Result<Fetched, Fault>
    {
        let refused = |refusal: ValueError| Fault::Refused { peer, refusal };
        let mut carried = Vec::new();
        let mut bytes = 0_u64;
        for part in Parts(answer.as_ref()) {
            let claim = part
                .and_then(Part::chunk)
                .map_err(|Malformed| Fault::Malformed { peer })?;
            let chunk = verify_chunk_image(claim).map_err(refused)?;
            let image: &[u8] = chunk.image().into();
            bytes = bytes.saturating_add(u64::try_from(image.len()).unwrap_or(u64::MAX));
            carried.push(chunk);
        }
        for &chunk in &carried {
            self.put(chunk);
        }
        wanted.closure(&self).map_err(refused)?;
        Ok(Fetched {
            chunks: ChunkCount::from(carried.len()),
            bytes,
        })
    }
}

impl ChunkStore for &Chunks
{
    /// Keep a verified chunk through the shared holder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`ChunkStore::insert`]: a fresh digest maps to the offered
    ///   image, and a held digest keeps its prior bytes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: which of two racing puts
    ///   wins is the scheduler's.
    ///
    /// # Errors
    /// None in practice; the signature is the trait's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sixteen threads that put one chunk at once leave one
    ///   digest, and a fetch keeps what it carried.
    /// - witness: `tests::chunks::sixteen_puts_of_one_chunk_leave_one_digest_6899`
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    #[inline]
    fn insert(
        &mut self,
        chunk: VerifiedChunk<'_>,
    ) -> Result<(), ValueError>
    {
        self.put(chunk);
        Ok(())
    }

    /// Load and verify again the image that the index publishes under
    /// `digest`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`ChunkStore::load`]. The lend reads the arena's slot,
    ///   which never moves, and never a guard of the index.
    /// - fails: [`ValueError::UnknownChunk`] when the index holds no slot for
    ///   `digest`, and [`verify_chunk_image`]'s refusals.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: the bytes are the
    ///   arena's, checked anew on each load.
    ///
    /// # Errors
    /// [`ValueError`] — as listed above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a load after a put reads the image put, and a holder
    ///   that lacks a chunk refuses it by its digest.
    /// - witness: `tests::chunks::sixteen_puts_of_one_chunk_leave_one_digest_6899`
    /// - witness: `tests::chunks::a_value_the_holder_lacks_is_refused_by_its_first_chunk`
    #[inline]
    fn load(
        &self,
        digest: ChunkDigest,
    ) -> Result<VerifiedChunk<'_>, ValueError>
    {
        let slot = self.0.slots.pin().get(&digest).copied();
        let Some(image) = slot.and_then(|slot| self.0.images.get(slot))
        else {
            return Err(ValueError::UnknownChunk { digest });
        };
        verify_chunk_image(StoredChunkRef::new(digest, image.as_image()))
    }
}

/// What one fetch carried.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fetched
{
    /// The chunks the answer carried, each verified and inserted.
    pub chunks: ChunkCount,
    /// The bytes of their images.
    pub bytes: u64,
}

impl Framed
{
    /// The request for `wanted`, naming each of `held` as held whole.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, a part for `wanted`'s image, then one for each of
    ///   `held`'s, in order.
    /// - fails: [`Fault::Oversized`] for a manifest image longer than a part.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Fault::Oversized`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a holder reads the wanted value and the held one from
    ///   a request, and carries only what the held one lacks.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |request| Parts(request.as_ref()).count() == held.len().saturating_add(1)))]
    pub(super) fn request(
        wanted: &ValueManifest,
        held: &[ValueManifest],
    ) -> Result<Self, Fault>
    {
        let mut request = Self::default();
        for manifest in core::iter::once(wanted).chain(held) {
            let image = manifest.encode();
            request.push(&[Part(image.as_ref())])?;
        }
        Ok(request)
    }
}

/// Why a holder refused a request.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unanswered
{
    /// A request this protocol does not frame, or one naming no wanted value.
    Malformed,
    /// A manifest that does not decode, or a held chunk that does not verify.
    Refused(ValueError),
    /// A chunk longer than a part.
    Oversized,
}

impl From<Malformed> for Unanswered
{
    /// A request that does not frame.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(Malformed: Malformed) -> Self
    {
        Self::Malformed
    }
}

impl From<ValueError> for Unanswered
{
    /// The value plane's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: ValueError) -> Self
    {
        Self::Refused(refusal)
    }
}

impl From<Oversized> for Unanswered
{
    /// A chunk too long for a part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_oversized: Oversized) -> Self
    {
        Self::Oversized
    }
}

impl<'bytes> Part<'bytes>
{
    /// The part read as a digest, then the chunk image it names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Malformed`] for a part shorter than a digest.
    fn chunk(self) -> Result<StoredChunkRef<'bytes>, Malformed>
    {
        let (digest, image) = self
            .0
            .split_first_chunk::<CHUNK_DIGEST_LEN>()
            .ok_or(Malformed)?;
        Ok(StoredChunkRef::new(
            ChunkDigest::from(*digest),
            ChunkImage::from(image),
        ))
    }
}
