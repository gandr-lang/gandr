//! The chunk wire: a committed value's chunks fetched by content from the
//! peer that holds them, on a connection of its own under [`CHUNKS_ALPN`],
//! apart from every stream a program holds.
//!
//! [`Chunks`] is the store a host commits a run's values into and its
//! endpoint serves them from; clones share it. A fetch asks once. The asker
//! sends the manifest of the value it wants, then the manifest of each value
//! whose chunks it holds whole, and finishes its side. The holder answers
//! with every chunk of the wanted value's closure that no held value's
//! closure contains, each under its digest, and finishes:
//!
//! ```text
//! request     := part(wanted) part(held)*
//! answer      := part(digest || image)*
//! part(bytes) := u32le length || bytes, at most MAX_FRAME bytes
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
//! - **In memory, never evicted.** The store holds every chunk committed or
//!   fetched for as long as a clone of it lives.
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

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

use anodized::spec;
use gandr_storage_values::CHUNK_DIGEST_LEN;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkImage;
use gandr_storage_values::ChunkStore as _;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::ManifestImage;
use gandr_storage_values::StoredChunkRef;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;
use gandr_storage_values::verify_chunk_image;

use crate::endpoint::Fault;
use crate::endpoint::MAX_FRAME;
use crate::peer::NodeId;

/// The protocol name a holder answers fetches under, offered beside
/// [`ALPN`](crate::ALPN) by every endpoint.
pub const CHUNKS_ALPN: &[u8] = b"gandr/chunks/0";

/// The bytes of a part's length prefix.
const PREFIX: usize = 4_usize;

/// The chunks a host holds: what its run commits and fetches, and what its
/// endpoint serves. Clones share one store.
#[derive(Clone, Debug, Default)]
#[repr(transparent)]
pub struct Chunks(Arc<Mutex<InMemoryChunkStore>>);

impl Chunks
{
    /// An empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The store, held alone until the guard drops.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the guard is the only access to the store while it lives. A
    ///   holder that panicked while it held the store left every chunk it
    ///   inserted whole, so the store is handed on as it left it.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: exclusivity is the
    ///   mutex's, and the guard holds nothing to check it against.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a holder's endpoint serves from the store its run
    ///   committed into, and an asker's fetch inserts into the store its run
    ///   derefs from.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, InMemoryChunkStore>
    {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
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
        let store = self.lock();
        // A holder that lacks a chunk of the closure answers nothing; the
        // asker's walk names the chunk.
        let Ok(closure) = wanted.closure(&*store)
        else {
            return Ok(Framed::default());
        };
        let mut held = BTreeSet::new();
        for part in parts {
            let part = part?;
            let manifest = ValueManifest::decode(part.manifest())?;
            // A held value whose closure this store lacks is passed over, and
            // the chunks it shares are carried.
            if let Ok(shared) = manifest.closure(&*store) {
                held.extend(BTreeSet::from(shared));
            }
        }
        let mut answer = Framed::default();
        for &digest in closure.digests().difference(&held) {
            let chunk = store.load(digest)?;
            answer.push(&[Part(digest.as_ref()), Part(chunk.image().into())])?;
        }
        drop(store);
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
        let mut store = self.lock();
        for &chunk in &carried {
            store.insert(chunk).map_err(refused)?;
        }
        wanted.closure(&*store).map_err(refused)?;
        drop(store);
        Ok(Fetched {
            chunks: ChunkCount::from(carried.len()),
            bytes,
        })
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

/// A request or an answer: parts, each a little-endian `u32` length, then
/// that many bytes, at most [`MAX_FRAME`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Framed(Vec<u8>);

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

    /// Append one part, `pieces` one after another, its length first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success, the bytes grew by the prefix and the pieces; on
    ///   failure, they are unchanged.
    /// - fails: [`Oversized`] for pieces longer than [`MAX_FRAME`] together.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Oversized`], carrying the part's length.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every part a request and an answer carry reads back
    ///   whole at the other end.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    #[spec(captures: before = self.0.len(), ensures: |ret| ret.is_ok() || self.0.len() == before)]
    fn push(
        &mut self,
        pieces: &[Part<'_>],
    ) -> Result<(), Oversized>
    {
        let length = pieces
            .iter()
            .fold(0_usize, |sum, piece| sum.saturating_add(piece.0.len()));
        let prefix = u32::try_from(length)
            .ok()
            .filter(|&prefix| prefix <= MAX_FRAME)
            .ok_or_else(|| Oversized(u64::try_from(length).unwrap_or(u64::MAX)))?;
        self.0.reserve(length.saturating_add(PREFIX));
        self.0.extend_from_slice(&prefix.to_le_bytes());
        for piece in pieces {
            self.0.extend_from_slice(piece.0);
        }
        Ok(())
    }
}

impl From<Vec<u8>> for Framed
{
    /// The parts `bytes` hold, read as they arrived.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for Framed
{
    /// The bytes, borrowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// A part longer than [`MAX_FRAME`], by its length in bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Oversized(u64);

impl From<Oversized> for Fault
{
    /// The endpoint's refusal of an oversized frame.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(Oversized(length): Oversized) -> Self
    {
        Self::Oversized { length }
    }
}

/// Bytes this protocol does not frame.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Malformed;

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
    fn from(Oversized(_): Oversized) -> Self
    {
        Self::Oversized
    }
}

/// The bytes of one part.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
struct Part<'bytes>(&'bytes [u8]);

impl<'bytes> Part<'bytes>
{
    /// The part read as a manifest image.
    ///
    /// # Specification
    /// trivial.
    fn manifest(self) -> ManifestImage<'bytes>
    {
        ManifestImage::from(self.0)
    }

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

/// The parts of a request or an answer not yet read, in order.
#[derive(Clone, Debug)]
#[repr(transparent)]
struct Parts<'bytes>(&'bytes [u8]);

impl<'bytes> Iterator for Parts<'bytes>
{
    type Item = Result<Part<'bytes>, Malformed>;

    /// The next part, or [`Malformed`] once for bytes that do not frame,
    /// after which nothing is read.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.0.is_empty() {
            return None;
        }
        let framed = self
            .0
            .split_first_chunk::<PREFIX>()
            .and_then(|(prefix, rest)| {
                let length = u32::from_le_bytes(*prefix);
                let length = usize::try_from(length)
                    .ok()
                    .filter(|_| length <= MAX_FRAME)?;
                rest.split_at_checked(length)
            });
        let Some((part, rest)) = framed
        else {
            self.0 = &[];
            return Some(Err(Malformed));
        };
        self.0 = rest;
        Some(Ok(Part(part)))
    }
}
