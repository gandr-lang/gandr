//! The order of a record set as its index tree stores it: a head, and a chain
//! of content-defined chunks, each under a key of its own.
//!
//! # The records
//!
//! ```text
//! key                                      value
//! 0x00                                     the head: the form, the count of places, the first chunk's key
//! 0x00, an image's identity, an occurrence  the key of the next chunk, or nothing for the last
//! ```
//!
//! | Key | Value |
//! | --- | ----- |
//! | [`ORDER_KEY`], one zero byte | the head: the set's form, one byte; the count of places, eight bytes little-endian; the key of the first chunk, [`CHUNK_KEY_LEN`] bytes, or nothing when the set has no place |
//! | a chunk's key: one zero byte, the identity of the chunk's image, and the chunk's occurrence, four bytes big-endian, so the keys of one image sort by occurrence | the key of the next chunk, or nothing for the last chunk |
//!
//! A chunk is a run of consecutive places. Its image holds, for each place,
//! the key of the place's record, [`RECORD_KEY_LEN`] bytes. In a named set
//! the place's content name follows the key, [`CONTENT_NAME_LEN`] bytes. The
//! image is a value leaf under its identity, as each declaration record is.
//! Equal images share one leaf. The occurrence of a chunk counts the chunks
//! with the same image that the chain reaches before it, so no two chunks
//! share a key.
//!
//! A chunk's key reads its own places alone, and an insertion before it moves
//! no byte of it. The chunk's record holds the key of the next chunk. So an
//! insertion rewrites the chunk it lands in, the record of the chunk before
//! it, and the head, which counts the places. Each other chunk keeps its key,
//! its record and its leaf.
//!
//! The value plane's chunker cuts the places. It reads one event at each
//! place, whose residue is the leading eight bytes of the place's record key.
//! It cuts where the residue divides by [`CHUNK_KAPPA`], or where the chunk
//! holds [`CHUNK_CAP`] places. A cut reads its own place alone, so an
//! insertion moves no cut past the chunk it lands in. A run at the cap is the
//! one exception: its forced cuts move to its next free cut. The reader runs
//! the same chunker and refuses a chain cut otherwise, so one set has one
//! stored order.
//!
//! **Choice.** The identity of its own image keys a chunk, and the chunk's
//! record holds the link to its successor. A chunk names each place by its
//! record's key and holds no slot. Over the corpus at `1bfaaa943`, 3% of the
//! places repeat a record. There, a chunk-local table of keys costs 8.5% more
//! than a key at each place. **Alternatives.** A key by the chunk's ordinal
//! moves the key of each chunk past an insertion. One record that lists each
//! chunk's key is rewritten whole by each edit. The value plane's chunk DAG of
//! a flat sequence holds each chunk's pointer in its root chunk, so an edit
//! rewrites that root. A link inside the image rewrites each chunk past an
//! edit. **Reversal.** A record plane past two levels, or a reader that reads
//! a place by its index without the walk, makes a sequence tree indexed by
//! counts worth its depth.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::num::NonZeroU64;

use anodized::spec;
use gandr_storage_chunker::BoundaryEvent;
use gandr_storage_chunker::BoundaryResidue;
use gandr_storage_chunker::CutDecision;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunker;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_records::BlockStore;
use gandr_storage_records::NamedValue;
use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordValue;
use gandr_storage_records::ValueLeafHasher;

use super::CONTENT_NAME_LEN;
use super::ContentName;
use super::FROM_BYTES;
use super::NAMED;
use super::Naming;
use super::ORDER_KEY;
use super::RECORD_KEY_LEN;
use super::RecordKey;
use crate::error::ArtifactError;

/// The chunker's expected number of places for each content-defined cut.
pub const CHUNK_KAPPA: NonZeroU64 = match NonZeroU64::new(128) {
    Some(kappa) => kappa,
    None => NonZeroU64::MIN,
};

/// The most places one chunk of an order holds: eight times [`CHUNK_KAPPA`],
/// so a cut at the cap stands at one chunk in about 2,981.
pub const CHUNK_CAP: NonZeroU64 = match NonZeroU64::new(1024) {
    Some(cap) => cap,
    None => NonZeroU64::MIN,
};

/// The byte width of a chunk's key: the order's key byte, the identity of the
/// chunk's image, and its occurrence.
pub const CHUNK_KEY_LEN: usize = 0x25_usize;

/// The byte width of the identity of a chunk's image.
const IDENTITY_LEN: usize = 0x20_usize;

/// The byte width of the head's count of places.
const COUNT_LEN: usize = 0x08_usize;

/// The chunker's constants that every order is cut under.
///
/// # Specification
/// trivial.
#[inline]
fn chunking() -> TypedChunkerParams
{
    TypedChunkerParams::new(Kappa::from(CHUNK_KAPPA), TokenCap::from(CHUNK_CAP))
}

/// The chunker's event at a place whose record has the key `key`: one token,
/// and the leading eight bytes of the key as the residue.
///
/// # Specification
/// trivial.
#[inline]
fn event(key: &RecordKey) -> BoundaryEvent
{
    let lead = key
        .as_ref()
        .first_chunk::<8>()
        .map_or(0_u64, |lead| u64::from_le_bytes(*lead));
    BoundaryEvent::new(TokenCount::from(1_u64), BoundaryResidue::from(lead))
}

/// A chunk's turn among the chunks of the same image, in the order of the
/// chain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Occurrence(u32);

/// The key of a chunk's record: the order's key byte, the identity of the
/// chunk's image, and its occurrence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ChunkKey([u8; CHUNK_KEY_LEN]);

impl AsRef<[u8]> for ChunkKey
{
    /// The key's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// The key of the chunk whose image has `identity`, at its `occurrence`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one zero byte, the identity's bytes, then the occurrence, four
///   bytes big-endian, so the keys of one image sort by occurrence.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every stored order reads back through these keys.
/// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
#[spec(ensures: |ret| ret.as_ref().first() == Some(&0_u8)
    && ret.as_ref().get(1 ..= IDENTITY_LEN) == Some(identity.as_ref()))]
#[inline]
#[expect(
    clippy::big_endian_bytes,
    reason = "a chunk key sorts by its bytes, so a big-endian occurrence puts each chunk directly after the chunk of the same image one occurrence before it"
)]
fn chunk_key(
    identity: NodeHash,
    occurrence: Occurrence,
) -> ChunkKey
{
    let mut key = [0_u8; CHUNK_KEY_LEN];
    key.iter_mut()
        .skip(1)
        .zip(
            identity
                .as_ref()
                .iter()
                .chain(occurrence.0.to_be_bytes().iter()),
        )
        .for_each(|(slot, &byte)| *slot = byte);
    ChunkKey(key)
}

/// One chunk of a stored order: its key, the key of the chunk after it, and
/// its image's leaf.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Chunk
{
    /// The chunk's key.
    key: ChunkKey,
    /// The key of the next chunk, or none for the last.
    next: Option<ChunkKey>,
    /// The chunk's image under the identity of its leaf.
    image: NamedValue,
    /// Whether no chunk before it in the chain has the same image, so this
    /// chunk's leaf is the one a store admits.
    first: bool,
}

/// The order of a record set as its index tree stores it: the head, and each
/// chunk's record and leaf.
///
/// # Specification
/// - requires: built by
///   [`ArtifactRecordSet::stored_order`](super::ArtifactRecordSet::stored_order).
/// - ensures: the chunks stand in ascending order of their keys, and the head
///   names the first chunk of the chain.
/// - panics: none.
/// - executable: none — the fields are private and set only by one constructor,
///   whose specification states them.
///
/// # Adequacy
/// - hypothesis: L2 — every set stored and read back is the set.
/// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
/// - witness: `tests::artifact_contract::an_insertion_rewrites_only_the_chunks_it_touches_7432`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StoredOrder
{
    /// The head's bytes: the form, the count of places and the first key.
    head: Vec<u8>,
    /// The chunks, ascending by key.
    chunks: Vec<Chunk>,
}

impl StoredOrder
{
    /// The stored order of `places`, each a record's key and, in a named set,
    /// the place's content name, in the set's form `naming`.
    ///
    /// # Specification
    /// - requires: each place carries a name exactly when `naming` is
    ///   [`Naming::Named`].
    /// - ensures: the chunks partition the places in order, each cut where
    ///   [`chunking`] cuts; the head holds the form, the count and the first
    ///   chunk's key; each chunk's record holds the next chunk's key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Cost
    /// - allocation: the chunks' images, growth within the places.
    /// - allocation: the chain and the head, growth within the places.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a set stored and read back is the set; L3 an
    ///   insertion rewrites the chunk it lands in, the record before it and the
    ///   head, and no other record.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    /// - witness: `tests::artifact_contract::an_insertion_rewrites_only_the_chunks_it_touches_7432`
    #[spec(ensures: |ret| ret.chunks.is_sorted_by(|lower, higher| lower.key < higher.key))]
    pub(super) fn of<Places>(
        naming: Naming,
        places: Places,
    ) -> Self
    where
        Places: IntoIterator<Item = (RecordKey, Option<ContentName>)>,
    {
        let mut chunker = TypedChunker::new(&chunking());
        let mut images: Vec<Vec<u8>> = Vec::new();
        let mut open: Vec<u8> = Vec::new();
        let mut count = 0_u64;
        for (key, name) in places {
            open.extend_from_slice(key.as_ref());
            if let Some(name) = name {
                open.extend_from_slice(name.as_ref());
            }
            count = count.saturating_add(1);
            if matches!(chunker.on_boundary(event(&key)), CutDecision::Cut(_)) {
                images.push(core::mem::take(&mut open));
            }
        }
        if !open.is_empty() {
            images.push(open);
        }
        let hasher = ValueLeafHasher::new();
        let mut seen: BTreeMap<NodeHash, u32> = BTreeMap::new();
        let mut chain: Vec<Chunk> = Vec::with_capacity(images.len());
        for image in images {
            let image = hasher.named(RecordValue::from(image.as_slice()));
            let occurrence = seen.entry(image.identity()).or_insert(0_u32);
            let key = chunk_key(image.identity(), Occurrence(*occurrence));
            let first = *occurrence == 0;
            *occurrence = occurrence.saturating_add(1);
            if let Some(before) = chain.last_mut() {
                before.next = Some(key);
            }
            chain.push(Chunk {
                key,
                next: None,
                image,
                first,
            });
        }
        let mut head = Vec::with_capacity(
            1_usize
                .saturating_add(COUNT_LEN)
                .saturating_add(CHUNK_KEY_LEN),
        );
        head.push(u8::from(naming));
        head.extend_from_slice(&count.to_le_bytes());
        if let Some(first) = chain.first() {
            head.extend_from_slice(first.key.as_ref());
        }
        chain.sort_unstable_by_key(|chunk| chunk.key);

        Self {
            head,
            chunks: chain,
        }
    }

    /// The head's record, then each chunk's record, ascending by key.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the head under [`ORDER_KEY`] first, then one record for each
    ///   chunk, strictly ascending by key.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the result is an iterator, which a postcondition
    ///   could not read without spending it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every stored order reads back through these records.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    pub(super) fn records(&self) -> impl Iterator<Item = RecordRef<'_>> + '_
    {
        core::iter::once(RecordRef::new(ORDER_KEY, self.head.as_slice())).chain(
            self.chunks.iter().map(|chunk| {
                RecordRef::new(
                    chunk.key.as_ref(),
                    chunk.next.as_ref().map_or(&[][..], AsRef::as_ref),
                )
            }),
        )
    }

    /// Admits the leaf of each distinct chunk image into `store`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success `store` holds the leaf of each chunk's image.
    /// - fails: [`ArtifactError::Records`] for a leaf the store does not admit.
    /// - panics: none.
    /// - executable: none — a postcondition that loaded every leaf would walk
    ///   the chain.
    ///
    /// # Errors
    /// [`ArtifactError::Records`] — the record plane refuses a leaf.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every stored read loads each leaf this writes.
    /// - witness: `tests::artifact_contract::tree_nodes_store_and_reopen`
    pub(super) fn write_leaves<S>(
        &self,
        store: &mut S,
    ) -> Result<(), ArtifactError>
    where
        S: BlockStore + ?Sized,
    {
        for chunk in self.chunks.iter().filter(|chunk| chunk.first) {
            store.admit_value(&chunk.image)?;
        }

        Ok(())
    }
}

/// What a stored order names: its form, and the key and the name at each
/// place.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ReadOrder
{
    /// The set's form.
    naming: Naming,
    /// The key of each place's record, in the order of the places.
    keys: Vec<RecordKey>,
    /// The content name of each place in a named set; empty otherwise.
    names: Vec<ContentName>,
}

impl ReadOrder
{
    /// The set's form, the key of each place's record, and the content name
    /// of each place in a named set.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn into_parts(self) -> (Naming, Vec<RecordKey>, Vec<ContentName>)
    {
        (self.naming, self.keys, self.names)
    }
}

/// The order that `head` and `chunks` store, each chunk image loaded from
/// `store`.
///
/// # Specification
/// - requires: `head` stands at position one of the index tree and `chunks`
///   from position two on, strictly ascending by key, as a record tree's
///   records are.
/// - ensures: on success the places of the chain, in order: each chunk the head
///   or a chunk before it names, its image whole places of the form's width,
///   cut where [`chunking`] cuts, and as many places as the head counts.
/// - provides: the read path's check of the chain. It is canonical: one set has
///   one stored order.
/// - fails: [`ArtifactError::MisplacedRecord`] for a chunk record whose key has
///   another shape, a chunk out of its occurrence's turn, or a chunk cut where
///   the chunker does not cut; [`ArtifactError::MalformedOrder`] at place zero
///   for a head with no form, no whole count or a first key of another width,
///   and otherwise at the first place a chunk does not hold whole, the place
///   where the chain comes back to a chunk, or the place where the places and
///   the count part; [`ArtifactError::UnheldRecord`] at the place where a key
///   of the chain names no chunk record; [`ArtifactError::UnplacedRecord`] for
///   a chunk record the chain does not reach; and [`ArtifactError::Records`]
///   for a leaf the store does not hold.
/// - panics: none.
///
/// # Cost
/// - allocation: the keys and names, growth within the chain's places.
/// - allocation: a mark for each chunk, growth within the chunk records.
///
/// # Errors
/// As listed above.
///
/// # Adequacy
/// - hypothesis: L3 — a forged head, a chunk cut short, a dangling link, a
///   chain that comes back, a chunk the chain does not reach, a count that
///   differs, a chunk cut where the chunker does not cut and a leaf the store
///   does not hold are each refused at their own position.
/// - witness: `tests::artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`
#[spec(ensures: |ret| match ret {
    Ok(ref read) => read.names.len() == match read.naming {
        Naming::Named => read.keys.len(),
        Naming::Bytes => 0,
    },
    Err(
        ArtifactError::MisplacedRecord { .. }
        | ArtifactError::MalformedOrder { .. }
        | ArtifactError::UnheldRecord { .. }
        | ArtifactError::UnplacedRecord { .. }
        | ArtifactError::Records { .. },
    ) => true,
    Err(_) => false,
})]
#[expect(
    clippy::big_endian_bytes,
    reason = "a chunk key sorts by its bytes, so the chunk of the same image one occurrence before stands directly before it, and the turn check reads one record"
)]
pub(super) fn read<S>(
    head: &Record,
    chunks: &[Record],
    store: &S,
) -> Result<ReadOrder, ArtifactError>
where
    S: BlockStore + ?Sized,
{
    let misplaced = |offset: usize| ArtifactError::MisplacedRecord {
        position: RecordIndex::from(offset.saturating_add(2_usize)),
    };
    let malformed = |place: usize| ArtifactError::MalformedOrder {
        place: RecordIndex::from(place),
    };
    let (naming, rest) = match <&[u8]>::from(head.value()).split_first() {
        Some((&NAMED, rest)) => (Naming::Named, rest),
        Some((&FROM_BYTES, rest)) => (Naming::Bytes, rest),
        _ => return Err(malformed(0_usize)),
    };
    let (&count, first) = rest
        .split_first_chunk::<COUNT_LEN>()
        .ok_or_else(|| malformed(0_usize))?;
    let count = usize::try_from(u64::from_le_bytes(count)).map_err(|_wide| malformed(0_usize))?;
    let mut next = match first.len() {
        0 => None,
        CHUNK_KEY_LEN => Some(first),
        _ => return Err(malformed(0_usize)),
    };
    if let Some(offset) = chunks.iter().position(|chunk| {
        let key = chunk.key();
        let key = key.as_ref();
        key.len() != CHUNK_KEY_LEN || key.first() != Some(&0_u8)
    }) {
        return Err(misplaced(offset));
    }
    let width = match naming {
        Naming::Named => RECORD_KEY_LEN.saturating_add(CONTENT_NAME_LEN),
        Naming::Bytes => RECORD_KEY_LEN,
    };
    // The count is the head's claim, so the read reserves nothing by it. The
    // places grow only as the chain's leaves hold them.
    let mut keys: Vec<RecordKey> = Vec::new();
    let mut names: Vec<ContentName> = Vec::new();
    let mut reached = alloc::vec![false; chunks.len()];
    let mut chunker = TypedChunker::new(&chunking());
    while let Some(key) = next {
        let place = keys.len();
        let at = chunks
            .binary_search_by(|chunk| chunk.key().as_ref().cmp(key))
            .map_err(|_absent| ArtifactError::UnheldRecord {
                place: RecordIndex::from(place),
            })?;
        let Some(seen) = reached.get_mut(at)
        else {
            return Err(ArtifactError::UnheldRecord {
                place: RecordIndex::from(place),
            });
        };
        if *seen {
            return Err(malformed(place));
        }
        *seen = true;
        let (identity, occurrence) = key
            .get(1 ..)
            .and_then(|rest| rest.split_first_chunk::<IDENTITY_LEN>())
            .and_then(|(&identity, occurrence)| {
                Some((
                    identity,
                    u32::from_be_bytes(*occurrence.first_chunk::<4>()?),
                ))
            })
            .ok_or_else(|| misplaced(at))?;
        // A chunk key sorts by its bytes, and its occurrence is big-endian. So
        // the chunk of the same image one occurrence before stands directly
        // before it, and the chain reached that chunk first.
        if let Some(before) = occurrence.checked_sub(1) {
            let earlier = chunk_key(NodeHash::from(identity), Occurrence(before));
            let turn = at
                .checked_sub(1)
                .and_then(|prior| Some((chunks.get(prior)?, *reached.get(prior)?)))
                .is_some_and(|(prior, was_reached)| {
                    was_reached && prior.key().as_ref() == earlier.as_ref()
                });
            if !turn {
                return Err(misplaced(at));
            }
        }
        let leaf = NamedValue::load(store, NodeHash::from(identity))?;
        let image = <&[u8]>::from(leaf.value());
        let whole = image.len().checked_div(width).unwrap_or_default();
        if image.is_empty() || image.len().checked_rem(width) != Some(0) {
            return Err(malformed(place.saturating_add(whole)));
        }
        let link = chunks
            .get(at)
            .map_or(&[][..], |chunk| <&[u8]>::from(chunk.value()));
        next = match link.len() {
            0 => None,
            CHUNK_KEY_LEN => Some(link),
            _ => return Err(malformed(place.saturating_add(whole))),
        };
        for (index, entry) in image.chunks_exact(width).enumerate() {
            if keys.len() >= count {
                return Err(malformed(count));
            }
            let (&record, name) = entry
                .split_first_chunk::<RECORD_KEY_LEN>()
                .ok_or_else(|| malformed(keys.len()))?;
            let record = RecordKey(NodeHash::from(record));
            keys.push(record);
            if matches!(naming, Naming::Named) {
                let &name = name
                    .first_chunk::<CONTENT_NAME_LEN>()
                    .ok_or_else(|| malformed(keys.len()))?;
                names.push(ContentName(name));
            }
            let cut = matches!(chunker.on_boundary(event(&record)), CutDecision::Cut(_));
            let closes = index.saturating_add(1) == whole;
            // A chunk closes where the chunker cuts. The last chunk alone may
            // close with no cut: it holds what the last cut left.
            if cut != closes && (cut || next.is_some()) {
                return Err(misplaced(at));
            }
        }
    }
    if keys.len() != count {
        return Err(malformed(keys.len().min(count)));
    }
    if let Some(unreached) = reached.iter().position(|&seen| !seen) {
        return Err(ArtifactError::UnplacedRecord {
            position: RecordIndex::from(unreached.saturating_add(2_usize)),
        });
    }

    Ok(ReadOrder {
        naming,
        keys,
        names,
    })
}
