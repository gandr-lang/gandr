//! The two planes on disk: a directory of segments each, every segment a log
//! of records that one writer appends to.
//!
//! A plane wants three things at once. Many threads put objects at the same
//! time. An object must be durable before a root names it. A reader
//! must find each object by its identity. A file for each object gives the
//! third, but each put then makes a directory entry and a rename, and the
//! kernel orders every such entry of one directory behind one lock. So the
//! plane makes no entry for a put. Each thread appends its puts to a segment
//! of its own shard, and the plane keeps an index from each identity to the
//! place of its record.
//!
//! # Items
//!
//! A record is a header and the object's bytes. The header holds a magic
//! number, the length of the bytes, the identity, the record's own place
//! (its segment and its offset) and a checksum over the header. A reader
//! checks the header against the place it read from before it trusts the
//! length, so a read of the wrong place is refused before the digest is
//! checked. Each load then verifies the bytes by the identity, as both plane
//! traits ask, so bytes changed on disk are refused by the plane's own fault.
//!
//! [`Batch::publish`] appends the records of one call in one positioned write
//! and marks the segment. A put syncs nothing. Before a naming, the register
//! syncs each marked segment once, so one sync covers every put since the
//! last naming. A write that fails leaves the shard's end where it was, and
//! the next batch writes over the torn tail.
//!
//! A shard seals its segment once the segment reaches the host's extent size
//! ([`Seal`]), and at the close of the plane. The seal appends a trailer, a
//! record that lists each record of the segment with its place, and a footer
//! that points at the trailer; no shard appends to the segment after. Each
//! fold of the roots folds the entries of each segment sealed since into the
//! plane's index, a persistent trie whose pages are records of the plane
//! (`index`). The roots log line names the trie's root and the segments it
//! covers. The open of a plane reads that line and no page and no trailer,
//! then the footer and the trailer of each other sealed segment, and scans the
//! headers only of a segment with no trailer, which a crash left open. A
//! load that the memory does not hold reads the pages on its path once. A
//! later record of one identity takes the index from an earlier one.
//!
//! # Boundaries
//!
//! A thread takes its shard by its ordinal in the process modulo 64, so two
//! threads past that width share a shard and take turns at its lock. Each
//! writer creates its segments exclusively, so two processes over one store
//! never append to one segment. A load of an identity that the index does
//! not hold reads the tails of the other writers' segments first, so an
//! object that another process put after this one opened is found. Two puts
//! of one object that race both append, and the index keeps the later: the
//! other record stays in its segment, dead.
//!
//! The open reads one line for the segments the index covers, and the
//! trailer of each segment sealed after the last fold. The index keeps each
//! page it read for the life of the plane.
//!
//! # References
//!
//! - `vault:01a1d8c5-08cb-7e12-a5d5-9a2ad3279160` — anchor: the IO layer (§
//!   io-layer-extents): a shard is a log of its own, and a put appends with no
//!   directory entry.
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — anchor: the store's single
//!   writer plan (§ Refinements): the shard is per producer, and the union of
//!   the shards is the index over their segments.
//! - `vault:01a1d90b-b64a-7248-8f6e-e792b6e8cb9f` — background: the IO layer's
//!   probe (§ the grid): a segment for each shard, whose sync covers many puts,
//!   is the fastest blocking form on each device measured.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::fs::File;
use std::io;
use std::io::Read as _;
use std::io::Seek as _;
#[cfg(unix)]
use std::os::unix::fs::FileExt as _;
#[cfg(target_os = "wasi")]
use std::os::wasi::fs::FileExt as _;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::PoisonError;

use anodized::spec;
use gandr_storage_records::BlockStore;
use gandr_storage_records::EncodedNode;
use gandr_storage_records::NodeHash;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::StoredNode;
use gandr_storage_records::verify_stored_node;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ChunkImage;
use gandr_storage_values::ChunkStore;
use gandr_storage_values::StoredChunkRef;
use gandr_storage_values::ValueError;
use gandr_storage_values::VerifiedChunk;
use gandr_storage_values::verify_chunk_image;
use quenchant_shape::shape::Maybe;

use crate::store::ImageBytes;
use crate::store::StoreError;

mod index;

use self::index::Key;
use self::index::PageName;
use self::index::PageRef;
use self::index::Placed;

/// How many shards the producers of one store append to. A thread takes the
/// shard of its ordinal modulo this, so the workers of a pool up to this width
/// each own a shard.
const SHARDS: usize = 64_usize;

/// How many identities a writer tries for a new segment before it gives up.
const SEGMENT_ATTEMPTS: usize = 64_usize;

/// The start of each segment's file name. The segment's identity follows as
/// 16 lowercase hexadecimal digits.
const SEGMENT_PREFIX: &str = "segment-";

/// The bytes of a record's header.
const HEADER: usize = 64_usize;

/// The bytes of a header that its checksum covers: all but the checksum.
const CHECKED: usize = 56_usize;

/// The bytes a record's header opens with.
const MAGIC: [u8; 4] = *b"gsg1";

/// The bytes a trailer's header opens with, in place of a record's magic.
const TRAILER_MAGIC: [u8; 4] = *b"gst1";

/// The bytes a page of the index's header opens with, in place of a record's
/// magic.
const PAGE_MAGIC: [u8; 4] = *b"gsp1";

/// The start of the word a roots log line names a plane's index by.
const INDEX_PREFIX: &str = "index:";

/// The domain a header's checksum is taken in, so it meets no other digest
/// of the store.
const HEADER_DOMAIN: &[u8] = b"gandr storage-store segment record header\0";

/// The domain a trailer's digest is taken in.
const TRAILER_DOMAIN: &[u8] = b"gandr storage-store segment trailer\0";

/// The bytes of one entry of a trailer: the identity, the record's offset as
/// eight little-endian bytes and its length as four.
const ENTRY: usize = 44_usize;

/// The bytes of a sealed segment's footer: the trailer's offset as eight
/// little-endian bytes, its length as four, four zero bytes, the magic and
/// four bytes of a checksum.
const FOOTER: usize = 24_usize;

/// The bytes a footer's checksum covers: the offset, the length and the zero
/// bytes.
const FOOTED: usize = 16_usize;

/// The magic of a footer.
const FOOTER_MAGIC: [u8; 4] = *b"gsf1";

/// The domain a footer's checksum is taken in.
const FOOTER_DOMAIN: &[u8] = b"gandr storage-store segment footer\0";

/// The bytes the open reads ahead of each header.
const SCAN_BUFFER: usize = 64_usize << 10_u32;

/// When a shard seals its open segment: it writes the segment's trailer and
/// footer, and appends no more to it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Seal
{
    /// At the close of the store alone, for a host that names no extent size.
    AtClose,
    /// Once the segment holds at least this many bytes, and at the close.
    At(SealBytes),
}

/// The extent size at which a segment seals, as the host measures it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SealBytes(pub core::num::NonZeroU64);

/// The ordinal that the next thread to publish in the process takes.
static ORDINALS: AtomicUsize = AtomicUsize::new(0_usize);

std::thread_local! {
    /// The shard of the calling thread: its ordinal modulo [`SHARDS`], taken
    /// at its first publication.
    static SHARD: usize = ORDINALS.fetch_add(1_usize, Ordering::Relaxed) % SHARDS;
}

/// The identity a plane names its objects by: 32 bytes, spelled as 64
/// lowercase hexadecimal digits.
pub trait ObjectName:
    Copy + Ord + core::hash::Hash + core::fmt::Display + From<[u8; 32]> + AsRef<[u8]> + Send + Sync
{
}

impl ObjectName for ChunkDigest
{
}

impl ObjectName for NodeHash
{
}

quenchant_shape::reason_enum! {
    /// Why a plane has no bytes for an identity.
    pub mod unheld {
        /// The plane's bytes for an identity are missing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No segment of the plane holds a record of that identity.
            Unlisted,
            /// The object's record cannot be read, or its header does not name
            /// the place it was read from.
            Unreadable,
            /// The text spells no identity: it is not exactly 64 lowercase
            /// hexadecimal digits.
            Unspelled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the bytes at a place hold no record.
    mod unrecorded {
        /// The bytes at a place are no record of the plane.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The header does not open with the magic, or its checksum does
            /// not hold.
            Unchecked,
            /// The header names another segment or another offset than the
            /// place it was read from.
            Misplaced,
        }
    }
}

/// An object's bytes, as its plane frames them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Image<'bytes>(pub &'bytes [u8]);

/// A file's name in a store's directory.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct FileName<'text>(pub &'text str);

/// A word of a roots log line.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Word<'line>(pub &'line str);

/// The bytes of one positioned write to a segment.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Written(Vec<u8>);

/// A segment's identity: unique in its plane, and ordered as the writers
/// created the segments.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SegmentId(u64);

impl SegmentId
{
    /// The name of the segment's file.
    ///
    /// # Specification
    /// trivial.
    fn file_name(self) -> String
    {
        format!("{SEGMENT_PREFIX}{:016x}", self.0)
    }

    /// The identity a file's name spells, or why it spells none.
    ///
    /// # Specification
    /// trivial.
    fn named(file: &std::ffi::OsStr) -> Maybe<Self, unheld::Absent>
    {
        file.to_str()
            .and_then(|text| text.strip_prefix(SEGMENT_PREFIX))
            .filter(|digits| {
                digits.len() == 16
                    && digits
                        .bytes()
                        .all(|digit| matches!(digit, b'0' ..= b'9' | b'a' ..= b'f'))
            })
            .and_then(|digits| u64::from_str_radix(digits, 16).ok())
            .map_or(Maybe::Absent(unheld::Absent::Unspelled), |id| {
                Maybe::Present(Self(id))
            })
    }
}

/// A byte offset into a segment.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Offset(u64);

impl Offset
{
    /// The offset just past a record of `length` bytes at `self`.
    ///
    /// # Specification
    /// trivial.
    fn after(
        self,
        length: Length,
    ) -> Self
    {
        Self(
            self.0
                .saturating_add(u64::try_from(HEADER).unwrap_or(u64::MAX))
                .saturating_add(u64::from(length.0)),
        )
    }
}

/// The length of a record's bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Length(u32);

impl Length
{
    /// The length of `image`, or the fault for an object of 4 GiB or more.
    ///
    /// # Specification
    /// trivial.
    fn of(image: Image<'_>) -> Result<Self, StoreError>
    {
        u32::try_from(image.0.len())
            .map(Self)
            .map_err(|_long| StoreError::Oversized {
                bytes: ImageBytes::of(image),
            })
    }
}

/// A slot of one of a plane's arenas.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot(usize);

/// Where a record stands: its segment's slot, its offset there, and the
/// length of its bytes.
#[derive(Clone, Copy, Debug)]
struct Place
{
    /// The slot of the record's segment in the plane's segments.
    segment: Slot,
    /// The offset of the record's header in the segment.
    offset: Offset,
    /// The length of the record's bytes.
    length: Length,
}

/// What a header stands before: an object's record, a sealed segment's
/// trailer, or a page of the plane's index.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// An object's bytes, under its identity.
    Record,
    /// The list of the segment's records, under the digest of the list.
    Trailer,
    /// A page of the plane's index, under the page's name.
    Page,
}

/// A record's header, as it stands before the record's bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Header<Name>
{
    /// What the header stands before.
    kind: Kind,
    /// The length of the record's bytes.
    length: Length,
    /// The identity of the object the record holds, or the digest of a
    /// trailer's entries.
    name: Name,
    /// The segment the record stands in.
    segment: SegmentId,
    /// The record's offset in its segment.
    offset: Offset,
}

/// A header's bytes: the magic, the length as four little-endian bytes, the
/// identity, the segment and the offset as eight little-endian bytes each,
/// and the first eight bytes of the checksum over them.
#[repr(transparent)]
struct HeaderBytes([u8; HEADER]);

/// A header's first [`CHECKED`] bytes, the bytes its checksum covers.
#[repr(transparent)]
struct Checked([u8; CHECKED]);

/// The first eight bytes of the checksum over a header's checked bytes.
#[repr(transparent)]
struct Checksum([u8; 8]);

/// The checksum over a header's checked bytes.
///
/// # Specification
/// trivial.
fn checksum(checked: &Checked) -> Checksum
{
    let mut hasher = blake3::Hasher::new();
    let _domain = hasher.update(HEADER_DOMAIN);
    let _checked = hasher.update(&checked.0);
    let mut sum = [0_u8; 8];
    hasher.finalize_xof().fill(&mut sum);
    Checksum(sum)
}

/// The digest of a trailer's entries.
///
/// # Specification
/// trivial.
fn trailer_digest(entries: Image<'_>) -> TrailerDigest
{
    let mut hasher = blake3::Hasher::new();
    let _domain = hasher.update(TRAILER_DOMAIN);
    let _entries = hasher.update(entries.0);
    TrailerDigest(*hasher.finalize().as_bytes())
}

/// A footer's bytes: the trailer's offset and length, the magic, and the
/// first eight bytes of a checksum over the offset and the length.
#[repr(transparent)]
struct FooterBytes([u8; FOOTER]);

impl FooterBytes
{
    /// The footer that points at a trailer of `length` at `offset`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        offset: Offset,
        length: Length,
    ) -> Self
    {
        let mut bytes = [0_u8; FOOTER];
        let (footed, rest) = bytes.split_at_mut(FOOTED);
        let (at, long) = footed.split_at_mut(8);
        at.copy_from_slice(&offset.0.to_le_bytes());
        let (long, _pad) = long.split_at_mut(4);
        long.copy_from_slice(&length.0.to_le_bytes());
        let sum = footer_checksum(Image(footed));
        let (magic, check) = rest.split_at_mut(FOOTER_MAGIC.len());
        magic.copy_from_slice(&FOOTER_MAGIC);
        check.copy_from_slice(sum.0.get(.. check.len()).unwrap_or_default());
        Self(bytes)
    }

    /// The trailer's offset and length these bytes point at, when their magic
    /// and their checksum hold.
    ///
    /// # Specification
    /// trivial.
    fn trailer(&self) -> Maybe<(Offset, Length), unrecorded::Absent>
    {
        let unchecked = Maybe::Absent(unrecorded::Absent::Unchecked);
        let Some((footed, rest)) = self.0.split_first_chunk::<FOOTED>()
        else {
            return unchecked;
        };
        let Some((magic, check)) = rest.split_first_chunk::<4>()
        else {
            return unchecked;
        };
        if *magic != FOOTER_MAGIC
            || footer_checksum(Image(footed)).0.get(.. check.len()) != Some(check)
        {
            return unchecked;
        }
        let Some((at, long)) = footed.split_first_chunk::<8>()
        else {
            return unchecked;
        };
        let Some((long, _pad)) = long.split_first_chunk::<4>()
        else {
            return unchecked;
        };
        Maybe::Present((
            Offset(u64::from_le_bytes(*at)),
            Length(u32::from_le_bytes(*long)),
        ))
    }
}

/// The checksum over a footer's first [`FOOTED`] bytes.
///
/// # Specification
/// trivial.
fn footer_checksum(footed: Image<'_>) -> Checksum
{
    let mut hasher = blake3::Hasher::new();
    let _domain = hasher.update(FOOTER_DOMAIN);
    let _footed = hasher.update(footed.0);
    let mut sum = [0_u8; 8];
    hasher.finalize_xof().fill(&mut sum);
    Checksum(sum)
}

impl<Name> Header<Name>
where
    Name: ObjectName,
{
    /// The bytes the header is written as.
    ///
    /// # Specification
    /// trivial.
    fn bytes(self) -> HeaderBytes
    {
        let mut checked = Checked([0_u8; CHECKED]);
        let (magic, rest) = checked.0.split_at_mut(MAGIC.len());
        magic.copy_from_slice(match self.kind {
            Kind::Record => &MAGIC,
            Kind::Trailer => &TRAILER_MAGIC,
            Kind::Page => &PAGE_MAGIC,
        });
        let (length, rest) = rest.split_at_mut(4);
        length.copy_from_slice(&self.length.0.to_le_bytes());
        let (name, rest) = rest.split_at_mut(32);
        name.copy_from_slice(self.name.as_ref());
        let (segment, offset) = rest.split_at_mut(8);
        segment.copy_from_slice(&self.segment.0.to_le_bytes());
        offset.copy_from_slice(&self.offset.0.to_le_bytes());
        let mut bytes = [0_u8; HEADER];
        let (head, check) = bytes.split_at_mut(CHECKED);
        head.copy_from_slice(&checked.0);
        check.copy_from_slice(&checksum(&checked).0);
        HeaderBytes(bytes)
    }
}

impl HeaderBytes
{
    /// The header these bytes spell, read at `segment` and `offset`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the header the bytes spell, when they open with the magic,
    ///   their checksum holds and they name `segment` and `offset`; `Unchecked`
    ///   for bytes that fail the magic or the checksum, and `Misplaced` for a
    ///   header of another place.
    /// - provides: the one check every read and every scan makes before it
    ///   trusts a length.
    /// - fails: never; bytes that are no header are the typed absence.
    /// - panics: none.
    /// - executable: none — the outcome is a pure function of the bytes, and
    ///   its witness is the record that a scan or a load refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a torn tail is cut at its first bad header, and a
    ///   record changed on disk is refused.
    /// - witness: `tests::store::a_torn_segment_tail_is_cut_on_opening_7462`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    fn header<Name>(
        &self,
        segment: SegmentId,
        offset: Offset,
    ) -> Maybe<Header<Name>, unrecorded::Absent>
    where
        Name: ObjectName,
    {
        let unchecked = Maybe::Absent(unrecorded::Absent::Unchecked);
        let Some((checked, check)) = self.0.split_first_chunk::<CHECKED>()
        else {
            return unchecked;
        };
        if check != checksum(&Checked(*checked)).0.as_slice() {
            return unchecked;
        }
        let Some((magic, rest)) = checked.split_first_chunk::<4>()
        else {
            return unchecked;
        };
        let Some((length, rest)) = rest.split_first_chunk::<4>()
        else {
            return unchecked;
        };
        let Some((name, rest)) = rest.split_first_chunk::<32>()
        else {
            return unchecked;
        };
        let Some((at_segment, rest)) = rest.split_first_chunk::<8>()
        else {
            return unchecked;
        };
        let Some((at_offset, _rest)) = rest.split_first_chunk::<8>()
        else {
            return unchecked;
        };
        let kind = match *magic {
            MAGIC => Kind::Record,
            TRAILER_MAGIC => Kind::Trailer,
            PAGE_MAGIC => Kind::Page,
            _ => return unchecked,
        };
        let header = Header {
            kind,
            length: Length(u32::from_le_bytes(*length)),
            name: Name::from(*name),
            segment: SegmentId(u64::from_le_bytes(*at_segment)),
            offset: Offset(u64::from_le_bytes(*at_offset)),
        };
        if header.segment != segment || header.offset != offset {
            return Maybe::Absent(unrecorded::Absent::Misplaced);
        }
        Maybe::Present(header)
    }
}

/// The bytes of a record as a read gave them, its header first, or the kind
/// of the failure.
#[repr(transparent)]
#[derive(Debug)]
struct Read(Result<Box<[u8]>, io::ErrorKind>);

/// Who appends to a segment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Writer
{
    /// A shard of this process, which indexes each record as it appends it.
    Own,
    /// Another writer, whose records a scan indexes.
    Other,
}

/// One segment a plane knows: its identity, its file and how far the plane
/// has indexed it.
#[derive(Debug)]
struct Segment
{
    /// The segment's identity.
    id: SegmentId,
    /// The file, open to read, and to write for a segment of this writer.
    file: File,
    /// Whose appends the segment takes.
    writer: Writer,
    /// The offset up to which the plane indexed the segment's records, for
    /// another writer's segment.
    scanned: AtomicU64,
    /// Whether a batch wrote to the segment since its last sync.
    dirty: AtomicBool,
    /// Where the segment's trailer stands, once the segment is sealed.
    sealed: OnceLock<Sealed>,
}

/// The digest of a trailer's entries, which its header names in place of an
/// identity.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TrailerDigest([u8; 32]);

/// A sealed segment and the place of its trailer, as a root names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Sealed
{
    /// The segment.
    segment: SegmentId,
    /// The offset of the trailer's header.
    offset: Offset,
    /// The length of the trailer's entries.
    length: Length,
    /// The digest of the entries.
    digest: TrailerDigest,
}

/// What a roots log line names of one plane: its index's root, and the
/// sealed segments with their trailers' places. When the line names an
/// index, the index covers each segment it lists.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Named
{
    /// The sealed segments, in order of their identities.
    sealed: Vec<Sealed>,
    /// The root of the index that covers them.
    index: Option<PageRef>,
}

/// The entries of the sealed segments that an index does not cover, and
/// those segments.
#[derive(Debug, Default)]
struct Uncovered
{
    /// Each entry, with its segment's identity.
    entries: Vec<(Key, Placed)>,
    /// The segments.
    since: Vec<Sealed>,
}

/// Whether a plane owes a close.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Closing
{
    /// No segment stands open, and the index covers each sealed segment.
    Closed,
    /// A segment stands open, or a sealed segment stands outside the index.
    Owed,
}

/// The index's root, and the sealed segments whose records it maps.
#[derive(Debug, Default)]
struct Covered
{
    /// The root, or none before the first fold that wrote a page.
    root: Option<PageRef>,
    /// The segments the index covers, by their identities.
    segments: BTreeMap<SegmentId, Sealed>,
}

/// One entry of a trailer: a record's identity and its place in the segment.
#[derive(Clone, Copy, Debug)]
struct Entry
{
    /// The identity's bytes.
    name: [u8; 32],
    /// The offset of the record's header.
    offset: Offset,
    /// The length of the record's bytes.
    length: Length,
}

/// One record a plane indexed.
#[derive(Debug)]
struct Filed<Name>
{
    /// The identity of the object the record holds.
    name: Name,
    /// Where the record stands.
    place: Place,
    /// The record's bytes as the first load read them.
    read: OnceLock<Read>,
    /// Whether a load refused the bytes: `true` once one did.
    refused: AtomicBool,
}

impl<Name> Filed<Name>
{
    /// The record of `name` at `place`, not read yet.
    ///
    /// # Specification
    /// trivial.
    const fn at(
        name: Name,
        place: Place,
    ) -> Self
    {
        Self {
            name,
            place,
            read: OnceLock::new(),
            refused: AtomicBool::new(false),
        }
    }
}

/// The open segment of a shard and the offset of its end.
#[derive(Clone, Copy, Debug)]
struct Open
{
    /// The slot of the segment in the plane's segments.
    segment: Slot,
    /// The offset past the last record the shard appended.
    end: Offset,
}

/// A shard's open segment, or none before its first batch and after a seal,
/// and the entries of the records the shard appended to it.
#[derive(Debug)]
struct Tail
{
    /// The open segment.
    open: Option<Open>,
    /// One entry for each record of the open segment, in order.
    entries: Vec<Entry>,
}

/// What a plane holds under a name, for an insertion to read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Holding
{
    /// The plane indexes the object, and no load refused it or failed to read
    /// it.
    Held,
    /// The plane indexes the object, and a load refused it or could not read
    /// it, so an insertion writes it afresh.
    Refused,
    /// The plane does not index the object.
    Unlisted,
}

/// A directory of segments, each a log of records, and the index from each
/// identity to its record.
///
/// The arenas grow by buckets and never move an element, so a record's bytes
/// stay at their address for the life of the plane, and a load lends them
/// from there. A writer pushes a record into the arena and then publishes
/// its slot in the index. So a reader that finds a slot finds the whole
/// record.
#[derive(Debug)]
pub struct Directory<Name>
where
    Name: ObjectName,
{
    /// The directory.
    path: PathBuf,
    /// Each segment the plane knows, at a fixed slot.
    segments: boxcar::Vec<Segment>,
    /// The slot of each segment, by its identity.
    known: papaya::HashMap<SegmentId, Slot>,
    /// Each record the plane indexed, at a fixed slot.
    objects: boxcar::Vec<Filed<Name>>,
    /// The slot of the latest record of each identity.
    index: papaya::HashMap<Name, Slot>,
    /// The open segment of each shard.
    shards: [Mutex<Tail>; SHARDS],
    /// When a shard seals its open segment.
    seal: Seal,
    /// The identity the next new segment tries first.
    next: AtomicU64,
    /// The lock a scan of the other writers' tails holds, so one scan runs at
    /// a time.
    catching: Mutex<()>,
    /// The index's root and the sealed segments it covers, as the folds
    /// change them, one at a time.
    covered: Mutex<Covered>,
    /// The index's root as each load reads it, with no lock.
    root: arc_swap::ArcSwapOption<PageRef>,
    /// The slot of each page of the index read, by its name.
    pages: papaya::HashMap<PageName, Slot>,
    /// Each page of the index read, at a fixed slot.
    paged: boxcar::Vec<Box<[u8]>>,
}

impl<Name> Directory<Name>
where
    Name: ObjectName,
{
    /// The directory at `path`, made when missing, and every record its
    /// segments hold indexed: under the index that `named` names for each
    /// segment it covers, else from the trailer of each segment that `named`
    /// lists; then from the footer and the trailer of each other sealed
    /// segment, then by a scan of each segment that has none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a directory at `path`; each record of each segment indexed
    ///   under its identity: a segment that `named`'s index covers through the
    ///   index, another sealed segment's from its trailer when the trailer's
    ///   digest holds, and any other segment's up to its first header that does
    ///   not check or record that does not fit; every other file ignored. Each
    ///   shard seals its segment as `seal` asks.
    /// - provides: a plane's index as the store opens.
    /// - fails: [`StoreError::Io`] when the directory cannot be made or listed,
    ///   or a segment cannot be opened or read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: the open reads no page of the index and no trailer of a
    ///   segment it covers; one trailer for each other sealed segment, and each
    ///   header of a segment that has no trailer; no record's bytes.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing root is made, a committed value loads after
    ///   reopening, a torn tail is cut, and a store opens from its root's
    ///   trailers, or from its index alone.
    /// - witness: `tests::store::a_missing_root_directory_is_made_on_opening`
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_torn_segment_tail_is_cut_on_opening_7462`
    /// - witness: `tests::store::a_store_opens_from_the_trailers_its_root_names_7481`
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    /// - witness: `plane::tests::a_plane_opens_from_its_index_and_reads_no_trailer`
    pub(crate) fn open(
        path: PathBuf,
        seal: Seal,
        named: &Named,
    ) -> Result<Self, StoreError>
    {
        std::fs::create_dir_all(&path).map_err(|error| StoreError::io(&path, &error))?;
        let plane = Self {
            path,
            segments: boxcar::Vec::new(),
            known: papaya::HashMap::new(),
            objects: boxcar::Vec::new(),
            index: papaya::HashMap::new(),
            shards: [const {
                Mutex::new(Tail {
                    open: None,
                    entries: Vec::new(),
                })
            }; SHARDS],
            seal,
            next: AtomicU64::new(0_u64),
            catching: Mutex::new(()),
            covered: Mutex::new(Covered {
                root: named.index,
                segments: BTreeMap::new(),
            }),
            root: arc_swap::ArcSwapOption::from(named.index.map(Arc::new)),
            pages: papaya::HashMap::new(),
            paged: boxcar::Vec::new(),
        };
        let mut covered = BTreeMap::new();
        for sealed in &named.sealed {
            let file = plane.path.join(sealed.segment.file_name());
            let Ok(opened) = File::open(&file)
            else {
                continue;
            };
            let slot = plane.known_segment(sealed.segment, opened);
            let Some(segment) = plane.segments.get(slot.0)
            else {
                continue;
            };
            if named.index.is_some() {
                // The index covers the segment: a load finds its records
                // through the index, so the open reads nothing of it.
                let _sealed = segment.sealed.set(*sealed);
                let _covered = covered.insert(sealed.segment, *sealed);
            }
            else {
                let _read = plane.trailer(slot, segment, *sealed)?;
            }
        }
        plane
            .covered
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .segments = covered;
        plane.catch_up()?;
        Ok(plane)
    }

    /// The slot of the segment `id` of another writer, open as `file`, pushed
    /// into the plane's segments and its identity made known.
    ///
    /// # Specification
    /// trivial.
    fn known_segment(
        &self,
        id: SegmentId,
        file: File,
    ) -> Slot
    {
        let slot = Slot(self.segments.push(Segment {
            id,
            file,
            writer: Writer::Other,
            scanned: AtomicU64::new(0_u64),
            dirty: AtomicBool::new(false),
            sealed: OnceLock::new(),
        }));
        let _known = self.known.pin().insert(id, slot);
        let _past = self
            .next
            .fetch_max(id.0.saturating_add(1_u64), Ordering::Relaxed);
        slot
    }

    /// Index every record of the other writers' segments that the plane has
    /// not indexed: each new segment of the directory whole, and the tail of
    /// each segment it knows past the last record it indexed there.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every record that another writer's segment holds
    ///   up to its first header that does not check is indexed, and the next
    ///   new segment takes an identity past every segment's.
    /// - provides: the open's index, and a load's view of what another process
    ///   put since.
    /// - fails: [`StoreError::Io`] when the directory cannot be listed or a
    ///   segment cannot be opened or read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value one store commits derefs from a second store
    ///   that opened before the commit.
    /// - witness: `tests::store::a_store_finds_what_another_put_after_it_opened_7462`
    fn catch_up(&self) -> Result<(), StoreError>
    {
        let _one = self.catching.lock().unwrap_or_else(PoisonError::into_inner);
        let path = &self.path;
        let entries = std::fs::read_dir(path).map_err(|error| StoreError::io(path, &error))?;
        let mut found = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|error| StoreError::io(path, &error))?;
            if let Maybe::Present(id) = SegmentId::named(&entry.file_name()) {
                found.push(id);
            }
        }
        found.sort_unstable();
        let known = self.known.pin();
        for id in found {
            let _past = self
                .next
                .fetch_max(id.0.saturating_add(1_u64), Ordering::Relaxed);
            if known.contains_key(&id) {
                continue;
            }
            let file = path.join(id.file_name());
            let opened = File::open(&file).map_err(|error| StoreError::io(&file, &error))?;
            let slot = self.known_segment(id, opened);
            if let Some(segment) = self.segments.get(slot.0)
                && let Maybe::Present(sealed) = self.footer(segment)?
            {
                let _read = self.trailer(slot, segment, sealed)?;
            }
        }
        for (at, segment) in &self.segments {
            if segment.writer == Writer::Other && segment.sealed.get().is_none() {
                self.scan(Slot(at), segment)?;
            }
        }
        Ok(())
    }

    /// Index each record of `segment` past the last one the plane indexed
    /// there, up to its first header that does not check or record that does
    /// not fit in the file.
    ///
    /// # Specification
    /// - requires: `segment` stands at `slot` of the plane's segments, and the
    ///   caller holds the scan's lock.
    /// - ensures: on success each record read is indexed under its identity, a
    ///   later one replacing an earlier, and the segment's scanned offset is
    ///   past the last.
    /// - provides: the read of one segment's new records.
    /// - fails: [`StoreError::Io`] when the segment cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: the scan reads each header through one buffer and skips
    ///   each record's bytes.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, and a torn
    ///   tail is cut at its first bad header.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_torn_segment_tail_is_cut_on_opening_7462`
    fn scan(
        &self,
        slot: Slot,
        segment: &Segment,
    ) -> Result<(), StoreError>
    {
        let file = self.path.join(segment.id.file_name());
        let io = |error: io::Error| StoreError::io(&file, &error);
        let size = segment.file.metadata().map_err(io)?.len();
        let mut at = Offset(segment.scanned.load(Ordering::Relaxed));
        let mut reader = io::BufReader::with_capacity(SCAN_BUFFER, &segment.file);
        let _start = reader.seek(io::SeekFrom::Start(at.0)).map_err(io)?;
        let index = self.index.pin();
        loop {
            let mut bytes = [0_u8; HEADER];
            match reader.read_exact(&mut bytes) {
                Ok(()) => {},
                Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => break,
                Err(error) => return Err(io(error)),
            }
            let Maybe::Present(header) = HeaderBytes(bytes).header::<Name>(segment.id, at)
            else {
                break;
            };
            let end = at.after(header.length);
            if end.0 > size {
                break;
            }
            if header.kind == Kind::Trailer {
                // A trailer ends the segment's records: past it stand the
                // footer, and torn bytes at most.
                let _sealed = segment.sealed.set(Sealed {
                    segment: segment.id,
                    offset: at,
                    length: header.length,
                    digest: TrailerDigest(header.name.as_ref().try_into().unwrap_or([0_u8; 32])),
                });
                at = Offset(size);
                break;
            }
            reader
                .seek_relative(i64::from(header.length.0))
                .map_err(io)?;
            // A page of the index is no object: the scan passes over it.
            if header.kind == Kind::Record {
                let place = Place {
                    segment: slot,
                    offset: at,
                    length: header.length,
                };
                let filed = Slot(self.objects.push(Filed::at(header.name, place)));
                let _indexed = index.insert(header.name, filed);
            }
            at = end;
        }
        segment.scanned.store(at.0, Ordering::Relaxed);
        Ok(())
    }

    /// Index each record that the trailer `sealed` lists, when the trailer
    /// stands where `sealed` says and its entries' digest holds.
    ///
    /// # Specification
    /// - requires: `segment` stands at `slot` of the plane's segments, and is
    ///   the segment that `sealed` names.
    /// - ensures: `Present(sealed)` when the trailer's header checks at its
    ///   place, names the length and the digest of `sealed`, and its entries
    ///   hash to that digest: then each entry is indexed under its identity,
    ///   the segment is sealed and its scan is done. `Unchecked` otherwise,
    ///   with nothing indexed.
    /// - provides: the open of a sealed segment, which reads its trailer and no
    ///   header of a record.
    /// - fails: [`StoreError::Io`] when the segment's size cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one positioned read of the trailer's header and entries.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store opens from the trailers its root names, and a
    ///   torn trailer leaves the segment to the scan.
    /// - witness: `tests::store::a_store_opens_from_the_trailers_its_root_names_7481`
    /// - witness: `tests::store::a_torn_trailer_leaves_its_segment_to_the_scan_7481`
    fn trailer(
        &self,
        slot: Slot,
        segment: &Segment,
        sealed: Sealed,
    ) -> Result<Maybe<Sealed, unrecorded::Absent>, StoreError>
    {
        let entries = match self.listing(segment, sealed)? {
            Maybe::Present(entries) => entries,
            Maybe::Absent(absent) => return Ok(Maybe::Absent(absent)),
        };
        let index = self.index.pin();
        for entry in entries {
            let place = Place {
                segment: slot,
                offset: entry.offset,
                length: entry.length,
            };
            let name = Name::from(entry.name);
            let filed = Slot(self.objects.push(Filed::at(name, place)));
            let _indexed = index.insert(name, filed);
        }
        let _sealed = segment.sealed.set(sealed);
        segment
            .scanned
            .store(sealed.offset.after(sealed.length).0, Ordering::Relaxed);
        Ok(Maybe::Present(sealed))
    }

    /// The entries that the trailer `sealed` lists, when the trailer stands
    /// where `sealed` says and its entries' digest holds.
    ///
    /// # Specification
    /// - requires: `segment` is the segment that `sealed` names.
    /// - ensures: the entries in order when the trailer's header checks at its
    ///   place, names the length and the digest of `sealed`, and its entries
    ///   hash to that digest; `Unchecked` otherwise.
    /// - provides: the read of a trailer that the open and each fold of the
    ///   index make.
    /// - fails: [`StoreError::Io`] when the segment's size cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one positioned read of the trailer's header and entries.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store opens from the trailers its root names, a
    ///   torn trailer leaves the segment to the scan, and a store opens from
    ///   its index.
    /// - witness: `tests::store::a_store_opens_from_the_trailers_its_root_names_7481`
    /// - witness: `tests::store::a_torn_trailer_leaves_its_segment_to_the_scan_7481`
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    fn listing(
        &self,
        segment: &Segment,
        sealed: Sealed,
    ) -> Result<Maybe<Vec<Entry>, unrecorded::Absent>, StoreError>
    {
        let file = self.path.join(segment.id.file_name());
        let size = segment
            .file
            .metadata()
            .map_err(|error| StoreError::io(&file, &error))?
            .len();
        let unchecked = Ok(Maybe::Absent(unrecorded::Absent::Unchecked));
        let body = usize::try_from(sealed.length.0).unwrap_or(usize::MAX);
        let mut bytes = vec![0_u8; body.saturating_add(HEADER)];
        if sealed.offset.after(sealed.length).0 > size
            || segment
                .file
                .read_exact_at(&mut bytes, sealed.offset.0)
                .is_err()
        {
            return unchecked;
        }
        let Some((head, entries)) = bytes.split_first_chunk::<HEADER>()
        else {
            return unchecked;
        };
        let Maybe::Present(header) = HeaderBytes(*head).header::<Name>(segment.id, sealed.offset)
        else {
            return unchecked;
        };
        if header.kind != Kind::Trailer
            || header.length != sealed.length
            || header.name.as_ref() != sealed.digest.0.as_slice()
            || trailer_digest(Image(entries)) != sealed.digest
            || entries.len() % ENTRY != 0
        {
            return unchecked;
        }
        let mut listed = Vec::with_capacity(entries.len().checked_div(ENTRY).unwrap_or_default());
        for entry in entries.as_chunks::<ENTRY>().0 {
            let Some((name, rest)) = entry.split_first_chunk::<32>()
            else {
                continue;
            };
            let Some((offset, rest)) = rest.split_first_chunk::<8>()
            else {
                continue;
            };
            let Some((length, _rest)) = rest.split_first_chunk::<4>()
            else {
                continue;
            };
            listed.push(Entry {
                name: *name,
                offset: Offset(u64::from_le_bytes(*offset)),
                length: Length(u32::from_le_bytes(*length)),
            });
        }
        Ok(Maybe::Present(listed))
    }

    /// The trailer that the footer of `segment` points at, with the digest
    /// its header names, or none when the segment ends in no footer that
    /// checks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the trailer's place and digest when the segment's last
    ///   [`FOOTER`] bytes open no torn tail, their checksum holds and the
    ///   header they point at checks as a trailer; `Unchecked` otherwise.
    /// - provides: the open of a sealed segment that no root names.
    /// - fails: [`StoreError::Io`] when the segment's size cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: two positioned reads, the footer's and the trailer
    ///   header's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store whose roots log is lost rebuilds its index
    ///   from the footers and the trailers.
    /// - witness: `tests::store::a_store_with_no_roots_log_reads_its_trailers_7481`
    fn footer(
        &self,
        segment: &Segment,
    ) -> Result<Maybe<Sealed, unrecorded::Absent>, StoreError>
    {
        let unchecked = Ok(Maybe::Absent(unrecorded::Absent::Unchecked));
        let file = self.path.join(segment.id.file_name());
        let size = segment
            .file
            .metadata()
            .map_err(|error| StoreError::io(&file, &error))?
            .len();
        let Some(at) = size.checked_sub(u64::try_from(FOOTER).unwrap_or(u64::MAX))
        else {
            return unchecked;
        };
        let mut bytes = [0_u8; FOOTER];
        if segment.file.read_exact_at(&mut bytes, at).is_err() {
            return unchecked;
        }
        let Maybe::Present((offset, length)) = FooterBytes(bytes).trailer()
        else {
            return unchecked;
        };
        let mut head = [0_u8; HEADER];
        if segment.file.read_exact_at(&mut head, offset.0).is_err() {
            return unchecked;
        }
        match HeaderBytes(head).header::<Name>(segment.id, offset) {
            Maybe::Present(header) if header.kind == Kind::Trailer && header.length == length => {
                Ok(Maybe::Present(Sealed {
                    segment: segment.id,
                    offset,
                    length,
                    digest: TrailerDigest(header.name.as_ref().try_into().unwrap_or([0_u8; 32])),
                }))
            },
            Maybe::Present(_) | Maybe::Absent(_) => unchecked,
        }
    }

    /// The bytes that seal the segment `id` at `end`: the trailer that lists
    /// `entries`, then the footer that points at it.
    ///
    /// # Specification
    /// trivial.
    fn sealing(
        id: SegmentId,
        end: Offset,
        entries: &[Entry],
        bytes: &mut Written,
    ) -> Result<Sealed, StoreError>
    {
        let mut body = Vec::with_capacity(entries.len().saturating_mul(ENTRY));
        for entry in entries {
            body.extend_from_slice(&entry.name);
            body.extend_from_slice(&entry.offset.0.to_le_bytes());
            body.extend_from_slice(&entry.length.0.to_le_bytes());
        }
        let length = Length::of(Image(&body))?;
        let digest = trailer_digest(Image(&body));
        let header = Header {
            kind: Kind::Trailer,
            length,
            name: Name::from(digest.0),
            segment: id,
            offset: end,
        };
        bytes.0.extend_from_slice(&header.bytes().0);
        bytes.0.extend_from_slice(&body);
        bytes.0.extend_from_slice(&FooterBytes::of(end, length).0);
        Ok(Sealed {
            segment: id,
            offset: end,
            length,
            digest,
        })
    }

    /// Each segment the plane knows as sealed, with its trailer's place, in
    /// order of the segments' identities.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn sealed(&self) -> Vec<Sealed>
    {
        let mut sealed: Vec<Sealed> = self
            .segments
            .iter()
            .filter_map(|(_at, segment)| segment.sealed.get().copied())
            .collect();
        sealed.sort_unstable_by_key(|each| each.segment);
        sealed
    }

    /// The record the plane indexes under `name`, after a scan of the other
    /// writers' tails when the index holds none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the latest record indexed under `name`; `Unlisted` when no
    ///   segment holds one after the scan, `Unreadable` when the scan fails.
    /// - provides: the lookup every load makes.
    /// - fails: never; a missing object is the typed absence.
    /// - panics: none.
    /// - executable: none — the index is shared with the other threads.
    /// - intension: a held name costs one probe of the index and no system
    ///   call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value derefs in the store that committed it, after
    ///   reopening, and in a second store that opened before the commit.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_store_finds_what_another_put_after_it_opened_7462`
    fn found(
        &self,
        name: Name,
    ) -> Maybe<&Filed<Name>, unheld::Absent>
    {
        let first = self.resident(name);
        if let Maybe::Present(filed) = first {
            return Maybe::Present(filed);
        }
        if self.catch_up().is_err() {
            return Maybe::Absent(unheld::Absent::Unreadable);
        }
        match self.indexed(name) {
            Maybe::Present(filed) => Maybe::Present(filed),
            Maybe::Absent(_) => first,
        }
    }

    /// The record the index holds under `name`, with no scan.
    ///
    /// # Specification
    /// trivial.
    fn indexed(
        &self,
        name: Name,
    ) -> Maybe<&Filed<Name>, unheld::Absent>
    {
        self.index
            .pin()
            .get(&name)
            .and_then(|&slot| self.objects.get(slot.0))
            .map_or(Maybe::Absent(unheld::Absent::Unlisted), Maybe::Present)
    }

    /// The record that the memory or the index on disk holds under `name`,
    /// with no scan. A record the index on disk gives is kept in the memory.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the latest record the memory holds under `name`, else the
    ///   record the index maps `name` to; `Unlisted` when neither holds one,
    ///   and `Unreadable` when a page on the path cannot be read or does not
    ///   check.
    /// - provides: the lookup of every load and every insertion.
    /// - fails: never; a missing object is the typed absence.
    /// - panics: none.
    /// - executable: none — the index is shared with the other threads.
    /// - intension: a held name costs one probe of the memory; another costs a
    ///   walk of the index, which reads each page on its path once for the life
    ///   of the plane.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store reopened from its index loads each object and
    ///   writes no object again.
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    fn resident(
        &self,
        name: Name,
    ) -> Maybe<&Filed<Name>, unheld::Absent>
    {
        if let Maybe::Present(filed) = self.indexed(name) {
            return Maybe::Present(filed);
        }
        let root = self.root.load().as_deref().copied();
        let Some(root) = root
        else {
            return Maybe::Absent(unheld::Absent::Unlisted);
        };
        let key = Key(name.as_ref().try_into().unwrap_or([0_u8; 32]));
        let placed = match index::find(self, root, key) {
            Ok(Maybe::Present(placed)) => placed,
            Ok(Maybe::Absent(absent)) => return Maybe::Absent(absent),
            Err(_) => return Maybe::Absent(unheld::Absent::Unreadable),
        };
        let Some(&segment) = self.known.pin().get(&placed.segment)
        else {
            return Maybe::Absent(unheld::Absent::Unreadable);
        };
        let filed = Slot(self.objects.push(Filed::at(name, Place {
            segment,
            offset: placed.offset,
            length: placed.length,
        })));
        // A record that a batch indexed since stays: it is the later one.
        let _kept = self.index.pin().try_insert(name, filed);
        self.indexed(name)
    }

    /// The bytes of the page `at` refers to, read once and kept.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the page's bytes when its header checks at its place as a
    ///   page of its name and length, and the bytes hash to its name.
    /// - provides: each read of the index.
    /// - fails: [`StoreError::Io`] when the page's segment is unknown after a
    ///   scan of the other writers' segments, or the page cannot be read or
    ///   does not check.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one positioned read for a page no load read before; none
    ///   after.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store reopened from its index loads each object.
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    fn page(
        &self,
        at: PageRef,
    ) -> Result<Image<'_>, StoreError>
    {
        if let Some(page) = self
            .pages
            .pin()
            .get(&at.name)
            .and_then(|&slot| self.paged.get(slot.0))
        {
            return Ok(Image(page));
        }
        let refused = |kind: io::ErrorKind| {
            StoreError::io(
                &self.path.join(at.at.segment.file_name()),
                &io::Error::from(kind),
            )
        };
        if self.known.pin().get(&at.at.segment).is_none() {
            self.catch_up()?;
        }
        let Some(segment) = self
            .known
            .pin()
            .get(&at.at.segment)
            .and_then(|&slot| self.segments.get(slot.0))
        else {
            return Err(refused(io::ErrorKind::NotFound));
        };
        let length = usize::try_from(at.at.length.0).unwrap_or(usize::MAX);
        let mut bytes = vec![0_u8; length.saturating_add(HEADER)];
        segment
            .file
            .read_exact_at(&mut bytes, at.at.offset.0)
            .map_err(|error| refused(error.kind()))?;
        let Some((head, body)) = bytes.split_first_chunk::<HEADER>()
        else {
            return Err(refused(io::ErrorKind::InvalidData));
        };
        match HeaderBytes(*head).header::<Name>(segment.id, at.at.offset) {
            Maybe::Present(header)
                if header.kind == Kind::Page
                    && header.length == at.at.length
                    && header.name.as_ref() == at.name.0.as_slice()
                    && index::named(Image(body)) == at.name => {},
            Maybe::Present(_) | Maybe::Absent(_) => {
                return Err(refused(io::ErrorKind::InvalidData));
            },
        }
        let slot = Slot(self.paged.push(Box::from(body)));
        let _kept = self.pages.pin().try_insert(at.name, slot);
        self.paged
            .get(slot.0)
            .map(|page| Image(page))
            .ok_or_else(|| refused(io::ErrorKind::NotFound))
    }

    /// Fold the entries of each segment sealed since the last fold into the
    /// index, and give what a roots log line names of the plane.
    ///
    /// # Specification
    /// - requires: the caller is the one writer of the roots.
    /// - ensures: on success the index maps every record of each segment it
    ///   covers, and covers each segment the plane knows as sealed whose
    ///   trailer checks; the names give the index's root and exactly the
    ///   segments it covers. Each page the fold wrote waits for
    ///   [`Directory::sync`].
    /// - provides: the plane's half of each fold of the roots.
    /// - fails: [`StoreError::Io`] when a trailer or a page cannot be read, no
    ///   segment can be created, or the pages cannot be written.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one read of the trailer of each newly sealed segment, one
    ///   positioned write of the new pages, and one page for each node on the
    ///   path of a new entry.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store opens from its index and reads no trailer,
    ///   and a crash after each step of a fold leaves roots that load.
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    /// - witness: `tests::store::a_crash_after_each_step_of_a_fold_leaves_roots_that_load_7459`
    pub(crate) fn fold_index(&self) -> Result<Named, StoreError>
    {
        let mut covered = self.covered.lock().unwrap_or_else(PoisonError::into_inner);
        let Uncovered { mut entries, since } = self.uncovered(&covered)?;
        if !entries.is_empty() {
            covered.root = self.paged_into(covered.root, &mut entries)?;
            self.root.store(covered.root.map(Arc::new));
        }
        for sealed in since {
            let _covered = covered.segments.insert(sealed.segment, sealed);
        }
        Ok(Named {
            sealed: covered.segments.values().copied().collect(),
            index: covered.root,
        })
    }

    /// The entries of each segment the plane knows as sealed that `covered`
    /// does not cover, and those segments.
    ///
    /// # Specification
    /// - requires: the caller holds the index's lock, as `covered`.
    /// - ensures: each entry of each uncovered segment whose trailer checks,
    ///   with the segment's identity, and each such segment; a trailer that
    ///   does not check leaves its segment out, to the footer and the scan of
    ///   the next open.
    /// - provides: the read of [`Directory::fold_index`] and
    ///   [`Directory::close_index`].
    /// - fails: [`StoreError::Io`] when a segment's size cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store opens from its index and reads no trailer.
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    fn uncovered(
        &self,
        covered: &Covered,
    ) -> Result<Uncovered, StoreError>
    {
        let mut entries = Vec::new();
        let mut since = Vec::new();
        for sealed in self.sealed() {
            if covered.segments.contains_key(&sealed.segment) {
                continue;
            }
            let Some(segment) = self
                .known
                .pin()
                .get(&sealed.segment)
                .and_then(|&slot| self.segments.get(slot.0))
            else {
                continue;
            };
            if let Maybe::Present(listed) = self.listing(segment, sealed)? {
                entries.extend(listed.into_iter().map(|entry| {
                    (Key(entry.name), Placed {
                        segment: sealed.segment,
                        offset: entry.offset,
                        length: entry.length,
                    })
                }));
                since.push(sealed);
            }
        }
        Ok(Uncovered { entries, since })
    }

    /// Fold `entries` into the index whose root is `root`, and append the new
    /// pages to the open segment of the calling thread's shard in one write.
    ///
    /// # Specification
    /// trivial.
    fn paged_into(
        &self,
        root: Option<PageRef>,
        entries: &mut Vec<(Key, Placed)>,
    ) -> Result<Option<PageRef>, StoreError>
    {
        let shard = SHARD.with(|shard| *shard);
        let [ref first, ..] = self.shards;
        let tail = self.shards.get(shard).unwrap_or(first);
        let mut open = tail.lock().unwrap_or_else(PoisonError::into_inner);
        self.paged_in(&mut open, root, entries)
    }

    /// Fold `entries` into the index whose root is `root`, and append the new
    /// pages to the open segment of `open`, a new one when it has none, in
    /// one write.
    ///
    /// # Specification
    /// - requires: the caller holds the index's lock and the lock of `open`'s
    ///   shard.
    /// - ensures: on success the new root, its pages written to the file system
    ///   and the segment marked for the next sync. On failure the shard's end
    ///   stays where it was.
    /// - provides: the write of [`Directory::fold_index`] and
    ///   [`Directory::close_index`].
    /// - fails: [`StoreError::Io`] when a page cannot be read, no segment can
    ///   be created, or the write fails.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store opens from its index and reads no trailer.
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    fn paged_in(
        &self,
        open: &mut Tail,
        root: Option<PageRef>,
        entries: &mut Vec<(Key, Placed)>,
    ) -> Result<Option<PageRef>, StoreError>
    {
        let at = self.tail(open.open)?;
        open.open = Some(at);
        let Some(segment) = self.segments.get(at.segment.0)
        else {
            return Err(StoreError::io(
                &self.path,
                &io::Error::from(io::ErrorKind::NotFound),
            ));
        };
        let mut sink = PageSink {
            segment: segment.id,
            start: at.end,
            bytes: Written::default(),
        };
        let root = index::fold(self, &mut sink, root, entries)?;
        let file = self.path.join(segment.id.file_name());
        segment
            .file
            .write_all_at(&sink.bytes.0, at.end.0)
            .map_err(|error| StoreError::io(&file, &error))?;
        segment.dirty.store(true, Ordering::Release);
        open.open = Some(Open {
            segment: at.segment,
            end: sink.end(),
        });
        Ok(root)
    }

    /// The bytes of the record of `name` at `place`, its header first, as one
    /// positioned read gives them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the record's bytes when its header checks and names `name`,
    ///   its length and `place`; `InvalidData` otherwise, and the read's own
    ///   failure when the file cannot be read.
    /// - provides: the one read of a record's bytes.
    /// - fails: never; a failure is the kind the read gives.
    /// - panics: none.
    /// - executable: none — the bytes are the file system's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, and a
    ///   record changed on disk is refused.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    fn read(
        &self,
        name: Name,
        place: Place,
    ) -> Read
    {
        let Some(segment) = self.segments.get(place.segment.0)
        else {
            return Read(Err(io::ErrorKind::NotFound));
        };
        let record = usize::try_from(place.length.0)
            .unwrap_or(usize::MAX)
            .saturating_add(HEADER);
        let mut bytes = vec![0_u8; record].into_boxed_slice();
        if let Err(error) = segment.file.read_exact_at(&mut bytes, place.offset.0) {
            return Read(Err(error.kind()));
        }
        let Some(head) = bytes.first_chunk::<HEADER>()
        else {
            return Read(Err(io::ErrorKind::InvalidData));
        };
        match HeaderBytes(*head).header::<Name>(segment.id, place.offset) {
            Maybe::Present(header)
                if header.kind == Kind::Record
                    && header.name == name
                    && header.length == place.length =>
            {
                Read(Ok(bytes))
            },
            Maybe::Present(_) | Maybe::Absent(_) => Read(Err(io::ErrorKind::InvalidData)),
        }
    }

    /// The bytes of the object `name`, read from its record the first time a
    /// load asks for them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the object's bytes as the first load in the process read
    ///   them; `Unlisted` for a name no segment holds, `Unreadable` for a
    ///   record that could not be read when first asked for.
    /// - provides: the plane's half of the one read both planes verify.
    /// - fails: never; a missing object is the typed absence.
    /// - panics: none.
    /// - executable: none — the bytes are the file system's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, and bytes
    ///   changed on disk are refused.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    fn listed(
        &self,
        name: Name,
    ) -> Maybe<Image<'_>, unheld::Absent>
    {
        let filed = match self.found(name) {
            Maybe::Present(filed) => filed,
            Maybe::Absent(absent) => return Maybe::Absent(absent),
        };
        filed
            .read
            .get_or_init(|| self.read(filed.name, filed.place))
            .0
            .as_ref()
            .ok()
            .and_then(|bytes| bytes.get(HEADER ..))
            .map_or(Maybe::Absent(unheld::Absent::Unreadable), |bytes| {
                Maybe::Present(Image(bytes))
            })
    }

    /// Mark the indexed object `name` refused, so the next batch that takes
    /// `name` writes it afresh.
    ///
    /// # Specification
    /// - requires: a load refused the bytes the plane gave for `name` as not
    ///   the object `name` names.
    /// - ensures: the latest record of `name` stands refused; a name the index
    ///   does not hold changes nothing.
    /// - provides: the refusal a later insertion reads.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the standing is an atomic flag that an insertion
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chunk changed on disk is refused, committed again
    ///   and read back after reopening.
    /// - witness: `tests::store::a_refused_chunk_is_written_afresh_by_the_next_commit_4074`
    fn refuse(
        &self,
        name: Name,
    )
    {
        if let Maybe::Present(filed) = self.resident(name) {
            filed.refused.store(true, Ordering::Relaxed);
        }
    }

    /// What the plane holds under `name`, for an insertion to read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Held` for an indexed object that no load refused and that no
    ///   load failed to read, `Refused` for another indexed object, `Unlisted`
    ///   for a name the index does not hold.
    /// - provides: whether an insertion of `name` writes its bytes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the standing is an atomic flag and a cell that
    ///   loads on other threads set.
    /// - intension: one probe of the index and no system call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value committed again writes no record, and a
    ///   refused chunk is written afresh.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_refused_chunk_is_written_afresh_by_the_next_commit_4074`
    fn holding(
        &self,
        name: Name,
    ) -> Holding
    {
        let Maybe::Present(filed) = self.resident(name)
        else {
            return Holding::Unlisted;
        };
        if filed.refused.load(Ordering::Relaxed)
            || filed.read.get().is_some_and(|read| read.0.is_err())
        {
            return Holding::Refused;
        }
        Holding::Held
    }

    /// The open segment of a shard, a new one when the shard has none: before
    /// its first batch, or after its last segment sealed.
    ///
    /// # Specification
    /// - requires: `open` is the shard's open segment, read under the shard's
    ///   lock.
    /// - ensures: on success the shard's open segment, or a new empty one; a
    ///   new segment's file and its directory entry are durable.
    /// - provides: where a batch appends.
    /// - fails: [`StoreError::Io`] when no new segment can be created or its
    ///   directory cannot be synced.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sixteen writers append to their own segments, and a
    ///   committed value derefs after reopening.
    /// - witness: `tests::store::sixteen_writers_append_to_their_own_segments_7462`
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    fn tail(
        &self,
        open: Option<Open>,
    ) -> Result<Open, StoreError>
    {
        if let Some(open) = open {
            return Ok(open);
        }
        let path = &self.path;
        for _attempt in 0_usize .. SEGMENT_ATTEMPTS {
            let id = SegmentId(self.next.fetch_add(1_u64, Ordering::Relaxed));
            let file = path.join(id.file_name());
            let created = std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&file);
            let opened = match created {
                Ok(opened) => opened,
                Err(ref error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(ref error) => return Err(StoreError::io(&file, error)),
            };
            File::open(path)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| StoreError::io(path, &error))?;
            let slot = Slot(self.segments.push(Segment {
                id,
                file: opened,
                writer: Writer::Own,
                scanned: AtomicU64::new(0_u64),
                dirty: AtomicBool::new(false),
                sealed: OnceLock::new(),
            }));
            let _known = self.known.pin().insert(id, slot);
            return Ok(Open {
                segment: slot,
                end: Offset(0_u64),
            });
        }
        Err(StoreError::io(
            path,
            &io::Error::from(io::ErrorKind::AlreadyExists),
        ))
    }

    /// Sync each segment of this writer that a batch wrote to since its last
    /// sync.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every record that a batch of this process wrote
    ///   before the call is durable on the device. A segment whose sync fails
    ///   stays marked, so the next sync tries it again.
    /// - provides: the step a naming takes before it names what the batches
    ///   wrote, so a root never names an object a crash can lose.
    /// - fails: [`StoreError::Io`] when a segment cannot be synced.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one data sync for each marked segment, at most one for each
    ///   shard's open segment and each segment sealed since.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a crash at each point of a naming and a fold leaves
    ///   roots whose objects load.
    /// - witness: `tests::store::a_crash_after_each_step_of_a_fold_leaves_roots_that_load_7459`
    pub(crate) fn sync(&self) -> Result<(), StoreError>
    {
        for (_at, segment) in &self.segments {
            if segment.writer != Writer::Own || !segment.dirty.swap(false, Ordering::AcqRel) {
                continue;
            }
            if let Err(error) = segment.file.sync_data() {
                segment.dirty.store(true, Ordering::Release);
                return Err(StoreError::io(
                    &self.path.join(segment.id.file_name()),
                    &error,
                ));
            }
        }
        Ok(())
    }
}

impl Sealed
{
    /// The word a roots log line spells the sealed segment with: its
    /// identity in hexadecimal, the trailer's offset and length in decimal,
    /// and the trailer's digest in hexadecimal, joined by colons.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn spelled(&self) -> String
    {
        let mut word = format!(
            "{:016x}:{}:{}:",
            self.segment.0, self.offset.0, self.length.0
        );
        for byte in self.digest.0 {
            let _written = core::fmt::Write::write_fmt(&mut word, format_args!("{byte:02x}"));
        }
        word
    }

    /// The sealed segment that `word` spells, as [`Sealed::spelled`] writes
    /// it, or none for any other word.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn parsed(word: Word<'_>) -> Maybe<Self, unrecorded::Absent>
    {
        let unchecked = Maybe::Absent(unrecorded::Absent::Unchecked);
        let mut parts = word.0.split(':');
        let (Some(segment), Some(offset), Some(length), Some(digest), None) = (
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
        )
        else {
            return unchecked;
        };
        let (Ok(segment), Ok(offset), Ok(length)) = (
            u64::from_str_radix(segment, 16),
            offset.parse::<u64>(),
            length.parse::<u32>(),
        )
        else {
            return unchecked;
        };
        let Maybe::Present(digest) = hexadecimal::<ChunkDigest>(FileName(digest))
        else {
            return unchecked;
        };
        Maybe::Present(Self {
            segment: SegmentId(segment),
            offset: Offset(offset),
            length: Length(length),
            digest: TrailerDigest(digest.as_ref().try_into().unwrap_or([0_u8; 32])),
        })
    }
}

impl Named
{
    /// The words a roots log line names the plane with: the index's word
    /// first, then each sealed segment's, each word after a space.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn spelled(&self) -> String
    {
        let mut words = String::new();
        if let Some(root) = self.index {
            let _written = core::fmt::Write::write_fmt(
                &mut words,
                format_args!(
                    " {INDEX_PREFIX}{}:{:016x}:{}:{}",
                    ChunkDigest::from(root.name.0),
                    root.at.segment.0,
                    root.at.offset.0,
                    root.at.length.0
                ),
            );
        }
        for sealed in &self.sealed {
            words.push(' ');
            words.push_str(&sealed.spelled());
        }
        words
    }

    /// Read `word` of a roots log line into the plane's names: the index's
    /// root, or one more sealed segment; a word that spells neither changes
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn read(
        &mut self,
        word: Word<'_>,
    )
    {
        let Some(index) = word.0.strip_prefix(INDEX_PREFIX)
        else {
            if let Maybe::Present(sealed) = Sealed::parsed(word) {
                self.sealed.push(sealed);
            }
            return;
        };
        let mut parts = index.split(':');
        let (Some(name), Some(segment), Some(offset), Some(length), None) = (
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
            parts.next(),
        )
        else {
            return;
        };
        if let (Maybe::Present(name), Ok(segment), Ok(offset), Ok(length)) = (
            hexadecimal::<ChunkDigest>(FileName(name)),
            u64::from_str_radix(segment, 16),
            offset.parse::<u64>(),
            length.parse::<u32>(),
        ) {
            self.index = Some(PageRef {
                name: PageName(name.as_ref().try_into().unwrap_or([0_u8; 32])),
                at: Placed {
                    segment: SegmentId(segment),
                    offset: Offset(offset),
                    length: Length(length),
                },
            });
        }
    }
}

/// The pages of one fold of the index, each placed after the one before in
/// one shard's open segment.
#[derive(Debug)]
struct PageSink
{
    /// The segment the pages go to.
    segment: SegmentId,
    /// The offset of the first page's header: the shard's end.
    start: Offset,
    /// The headers and the bytes of the pages placed so far.
    bytes: Written,
}

impl PageSink
{
    /// The offset past the last page placed.
    ///
    /// # Specification
    /// trivial.
    fn end(&self) -> Offset
    {
        Offset(
            self.start
                .0
                .saturating_add(u64::try_from(self.bytes.0.len()).unwrap_or(u64::MAX)),
        )
    }
}

impl index::Sink for PageSink
{
    /// Place `page` after the pages before it, under a header of its own.
    ///
    /// # Specification
    /// trivial.
    fn put(
        &mut self,
        page: Image<'_>,
        name: PageName,
    ) -> Result<PageRef, StoreError>
    {
        let length = Length::of(page)?;
        let offset = self.end();
        let header = Header {
            kind: Kind::Page,
            length,
            name: ChunkDigest::from(name.0),
            segment: self.segment,
            offset,
        };
        self.bytes.0.extend_from_slice(&header.bytes().0);
        self.bytes.0.extend_from_slice(page.0);
        Ok(PageRef {
            name,
            at: Placed {
                segment: self.segment,
                offset,
                length,
            },
        })
    }
}

impl<Name> index::Pages for Directory<Name>
where
    Name: ObjectName,
{
    /// The page `at` refers to, as [`Directory::page`] reads it.
    ///
    /// # Specification
    /// trivial.
    fn node(
        &self,
        at: PageRef,
    ) -> Result<index::Node<'_>, StoreError>
    {
        match index::node(self.page(at)?) {
            Maybe::Present(node) => Ok(node),
            Maybe::Absent(_) => Err(StoreError::io(
                &self.path.join(at.at.segment.file_name()),
                &io::Error::from(io::ErrorKind::InvalidData),
            )),
        }
    }
}

impl<Name> Drop for Directory<Name>
where
    Name: ObjectName,
{
    /// The close of the plane: each shard seals its open segment, as
    /// [`Directory::seal_open`] seals it.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.seal_open();
    }
}

impl<Name> Directory<Name>
where
    Name: ObjectName,
{
    /// Each shard seals its open segment with its trailer and footer, and
    /// syncs it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each open segment of this process ends in a trailer that
    ///   lists its records and a footer, durable on the device, so the next
    ///   open reads the trailer and scans no header. A seal that fails leaves
    ///   the segment as it stood, and the next open scans it.
    /// - provides: the seal at the close, which a host with no extent size
    ///   relies on alone, and which the register's close folds into the index.
    /// - fails: never; a failed seal costs the next open a scan.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one positioned write and one data sync for each open
    ///   segment.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store closed with no extent size opens from its
    ///   trailers, and a closed store's index covers each segment it sealed.
    /// - witness: `tests::store::a_store_with_no_roots_log_reads_its_trailers_7481`
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    pub(crate) fn seal_open(&self)
    {
        let mut bytes = Written::default();
        for shard in &self.shards {
            let mut tail = shard.lock().unwrap_or_else(PoisonError::into_inner);
            let _sealed = self.sealed_tail(&mut tail, &mut bytes);
        }
    }

    /// Seal the open segment of `tail`, if it has one: append its trailer and
    /// footer through `bytes`, and sync it.
    ///
    /// # Specification
    /// trivial.
    fn sealed_tail(
        &self,
        tail: &mut Tail,
        bytes: &mut Written,
    ) -> Option<Sealed>
    {
        let open = tail.open.take()?;
        let entries = core::mem::take(&mut tail.entries);
        let segment = self.segments.get(open.segment.0)?;
        bytes.0.clear();
        let sealed = Self::sealing(segment.id, open.end, &entries, bytes).ok()?;
        if segment.file.write_all_at(&bytes.0, open.end.0).is_err()
            || segment.file.sync_data().is_err()
        {
            return None;
        }
        let _sealed = segment.sealed.set(sealed);
        Some(sealed)
    }

    /// Whether the plane owes a close: an open segment, or a sealed segment
    /// that its index does not cover.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn closing(&self) -> Closing
    {
        let open = self.shards.iter().any(|shard| {
            shard
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .open
                .is_some()
        });
        let covered = self.covered.lock().unwrap_or_else(PoisonError::into_inner);
        let uncovered = self.segments.iter().any(|(_at, segment)| {
            segment
                .sealed
                .get()
                .is_some_and(|sealed| !covered.segments.contains_key(&sealed.segment))
        });
        if open || uncovered {
            Closing::Owed
        }
        else {
            Closing::Closed
        }
    }

    /// The close of the index: fold the entries of each segment sealed since
    /// the last fold and of each open segment into the index, write the new
    /// pages into an open segment, then seal every open segment, all under
    /// the shards' locks; and give what a roots log line names of the plane.
    ///
    /// # Specification
    /// - requires: the caller is the one writer of the roots, at its close.
    /// - ensures: on success the index maps every record of each segment the
    ///   plane knows as sealed, and covers each such segment whose trailer
    ///   checks and each segment this call sealed; no segment stays open. A
    ///   batch that waits for a shard's lock appends after the call to a new
    ///   segment, which the index does not cover.
    /// - provides: the plane's half of the close of the roots.
    /// - fails: as [`Directory::fold_index`].
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: as [`Directory::fold_index`], and one write and one data
    ///   sync for each open segment.
    ///
    /// # Errors
    /// As [`Directory::fold_index`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closed store's last line names every segment that
    ///   holds records, under its index.
    /// - witness: `tests::store::a_store_opens_from_its_index_and_reads_no_trailer_7531`
    pub(crate) fn close_index(&self) -> Result<Named, StoreError>
    {
        let mut covered = self.covered.lock().unwrap_or_else(PoisonError::into_inner);
        let mut tails: Vec<std::sync::MutexGuard<'_, Tail>> = self
            .shards
            .iter()
            .map(|shard| shard.lock().unwrap_or_else(PoisonError::into_inner))
            .collect();
        let Uncovered {
            mut entries,
            mut since,
        } = self.uncovered(&covered)?;
        for tail in &tails {
            let Some(segment) = tail.open.and_then(|open| self.segments.get(open.segment.0))
            else {
                continue;
            };
            entries.extend(tail.entries.iter().map(|entry| {
                (Key(entry.name), Placed {
                    segment: segment.id,
                    offset: entry.offset,
                    length: entry.length,
                })
            }));
        }
        if !entries.is_empty() {
            // The pages go to the calling thread's open segment, else to any
            // open one, so the seal below covers them.
            let shard = SHARD.with(|shard| *shard);
            let target = tails
                .get(shard)
                .filter(|tail| tail.open.is_some())
                .map(|_tail| shard)
                .or_else(|| tails.iter().position(|tail| tail.open.is_some()))
                .unwrap_or(shard);
            let Some(tail) = tails.get_mut(target)
            else {
                return Err(StoreError::io(
                    &self.path,
                    &io::Error::from(io::ErrorKind::NotFound),
                ));
            };
            covered.root = self.paged_in(tail, covered.root, &mut entries)?;
            self.root.store(covered.root.map(Arc::new));
        }
        let mut bytes = Written::default();
        for tail in &mut tails {
            since.extend(self.sealed_tail(tail, &mut bytes));
        }
        for sealed in since {
            let _covered = covered.segments.insert(sealed.segment, sealed);
        }
        Ok(Named {
            sealed: covered.segments.values().copied().collect(),
            index: covered.root,
        })
    }
}

/// One call's section over a plane: the objects it took, to publish when the
/// call ends.
#[derive(Debug)]
pub struct Batch<'plane, Name>
where
    Name: ObjectName,
{
    /// The plane the call reads and writes.
    plane: &'plane Directory<Name>,
    /// The objects the call took and did not publish yet.
    taken: BTreeMap<Name, Box<[u8]>>,
}

impl<'plane, Name> Batch<'plane, Name>
where
    Name: ObjectName,
{
    /// A call's batch over `plane`, holding nothing.
    ///
    /// # Specification
    /// trivial.
    const fn over(plane: &'plane Directory<Name>) -> Self
    {
        Self {
            plane,
            taken: BTreeMap::new(),
        }
    }

    /// The bytes under `name`: taken by the call, or read from the plane's
    /// record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the bytes the call took under `name`, else the bytes of the
    ///   latest record of `name` as the process first read them; the reason
    ///   when neither gives bytes.
    /// - provides: the one read both planes verify.
    /// - fails: never; a missing object is the typed absence.
    /// - panics: none.
    /// - executable: none — the bytes are the file system's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs before and after reopening,
    ///   and bytes changed on disk are refused.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    fn image(
        &self,
        name: Name,
    ) -> Maybe<Image<'_>, unheld::Absent>
    {
        if let Some(bytes) = self.taken.get(&name) {
            return Maybe::Present(Image(bytes));
        }
        self.plane.listed(name)
    }

    /// Take `bytes` under `name`, to be written when the batch publishes,
    /// unless the plane holds `name` already.
    ///
    /// # Specification
    /// - requires: `bytes` are verified as the object `name` names.
    /// - ensures: a name the call took, or the plane holds unrefused and
    ///   readable, keeps what it holds; another name, or one a load refused or
    ///   could not read, is taken as `bytes`.
    /// - provides: the insertion both plane traits make.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the standing is the index's, which other threads
    ///   share.
    /// - intension: an insertion costs one probe of the index and no system
    ///   call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs before and after reopening,
    ///   committing it again writes no record, and a refused chunk is written
    ///   afresh by the next commit.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_refused_chunk_is_written_afresh_by_the_next_commit_4074`
    fn take(
        &mut self,
        name: Name,
        bytes: Image<'_>,
    )
    {
        if self.taken.contains_key(&name) {
            return;
        }
        match self.plane.holding(name) {
            Holding::Held => return,
            Holding::Refused | Holding::Unlisted => {},
        }
        let _taken = self.taken.insert(name, Box::from(bytes.0));
    }

    /// Append each object the batch took to the open segment of the calling
    /// thread's shard, in one write, and mark the segment for the next sync.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success each object the batch took is a record of a
    ///   segment of the shard, written to the file system and indexed under its
    ///   name, so a read after the call finds it, and the segment waits for
    ///   [`Directory::sync`]. A batch that took nothing touches no file. On
    ///   failure the shard's end stays where it was, so the next batch writes
    ///   over what this one tore.
    /// - provides: the end of every facade operation that inserts, and the
    ///   union of the thread's shard into the plane: one index entry an object.
    /// - fails: [`StoreError::Io`] when no segment can be created or the write
    ///   fails; [`StoreError::Oversized`] for an object of 4 GiB or more.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: one positioned write for the batch, and a directory sync
    ///   for each new segment. A put syncs nothing: the naming that names it
    ///   syncs each segment marked since the last naming.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, which reads
    ///   only what was written; sixteen writers of one value leave each digest
    ///   readable; sixteen writers of distinct values append to their own
    ///   segments and make no other entry.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::sixteen_writers_of_one_value_leave_one_object_per_digest_6899`
    /// - witness: `tests::store::sixteen_writers_append_to_their_own_segments_7462`
    fn publish(self) -> Result<(), StoreError>
    {
        if self.taken.is_empty() {
            return Ok(());
        }
        let shard = SHARD.with(|shard| *shard);
        let [ref first, ..] = self.plane.shards;
        let tail = self.plane.shards.get(shard).unwrap_or(first);
        let mut open = tail.lock().unwrap_or_else(PoisonError::into_inner);
        let at = self.plane.tail(open.open)?;
        // A new segment stays the shard's, so a failed write leaves no
        // segment behind that no shard appends to.
        open.open = Some(at);
        let Some(segment) = self.plane.segments.get(at.segment.0)
        else {
            return Err(StoreError::io(
                &self.plane.path,
                &io::Error::from(io::ErrorKind::NotFound),
            ));
        };
        let mut bytes = Written(Vec::with_capacity(
            self.taken.values().fold(0_usize, |sum, image| {
                sum.saturating_add(image.len()).saturating_add(HEADER)
            }),
        ));
        let mut places = Vec::with_capacity(self.taken.len());
        let listed = open.entries.len();
        let mut end = at.end;
        for (&name, image) in &self.taken {
            let length = match Length::of(Image(image)) {
                Ok(length) => length,
                Err(error) => {
                    open.entries.truncate(listed);
                    return Err(error);
                },
            };
            let header = Header {
                kind: Kind::Record,
                length,
                name,
                segment: segment.id,
                offset: end,
            };
            bytes.0.extend_from_slice(&header.bytes().0);
            bytes.0.extend_from_slice(image);
            places.push((name, Place {
                segment: at.segment,
                offset: end,
                length,
            }));
            open.entries.push(Entry {
                name: name.as_ref().try_into().unwrap_or([0_u8; 32]),
                offset: end,
                length,
            });
            end = end.after(length);
        }
        // The batch that takes the segment to the host's extent size seals it
        // in the same write.
        let sealed = match self.plane.seal {
            Seal::At(SealBytes(limit)) if end.0 >= limit.get() => {
                match Directory::<Name>::sealing(segment.id, end, &open.entries, &mut bytes) {
                    Ok(sealed) => Some(sealed),
                    Err(error) => {
                        open.entries.truncate(listed);
                        return Err(error);
                    },
                }
            },
            Seal::At(_) | Seal::AtClose => None,
        };
        let file = self.plane.path.join(segment.id.file_name());
        if let Err(error) = segment.file.write_all_at(&bytes.0, at.end.0) {
            open.entries.truncate(listed);
            return Err(StoreError::io(&file, &error));
        }
        // Set after the write, so a sync that clears the mark first still
        // covers the bytes, or the mark stands for the next sync.
        segment.dirty.store(true, Ordering::Release);
        if let Some(sealed) = sealed {
            let _sealed = segment.sealed.set(sealed);
            open.open = None;
            open.entries.clear();
        }
        else {
            open.open = Some(Open {
                segment: at.segment,
                end,
            });
        }
        drop(open);
        let index = self.plane.index.pin();
        for (name, place) in places {
            let slot = Slot(self.plane.objects.push(Filed::at(name, place)));
            let _indexed = index.insert(name, slot);
        }
        Ok(())
    }
}

/// The identity exactly 64 lowercase hexadecimal digits spell, or none for
/// any other text.
///
/// # Specification
/// trivial.
pub fn hexadecimal<Name>(text: FileName<'_>) -> Maybe<Name, unheld::Absent>
where
    Name: ObjectName,
{
    let spelled = || {
        if text.0.len() != 64 {
            return None;
        }
        let mut bytes = [0_u8; 32];
        for (index, byte) in bytes.iter_mut().enumerate() {
            let at = index.saturating_mul(2);
            let pair = text.0.get(at .. at.saturating_add(2))?;
            if !pair
                .bytes()
                .all(|digit| matches!(digit, b'0' ..= b'9' | b'a' ..= b'f'))
            {
                return None;
            }
            *byte = u8::from_str_radix(pair, 16).ok()?;
        }
        Some(bytes)
    };
    spelled().map_or(Maybe::Absent(unheld::Absent::Unspelled), |bytes| {
        Maybe::Present(Name::from(bytes))
    })
}

/// The value plane on disk: each chunk image a record of a segment, indexed
/// by its digest.
#[repr(transparent)]
#[derive(Debug)]
pub struct ChunkDirectory(Directory<ChunkDigest>);

impl ChunkDirectory
{
    /// The value plane at `path`, as [`Directory::open`] opens it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn open(
        path: PathBuf,
        seal: Seal,
        named: &Named,
    ) -> Result<Self, StoreError>
    {
        Directory::open(path, seal, named).map(Self)
    }

    /// Sync the value plane's segments, as [`Directory::sync`] syncs them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn sync(&self) -> Result<(), StoreError>
    {
        self.0.sync()
    }

    /// Fold the value plane's newly sealed segments into its index, as
    /// [`Directory::fold_index`] folds them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn fold_index(&self) -> Result<Named, StoreError>
    {
        self.0.fold_index()
    }

    /// Close the value plane's index, as [`Directory::close_index`] closes
    /// it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn close_index(&self) -> Result<Named, StoreError>
    {
        self.0.close_index()
    }

    /// Whether the value plane owes a close, as [`Directory::closing`] reads
    /// it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn closing(&self) -> Closing
    {
        self.0.closing()
    }
}

/// One call's batch over the value plane.
#[repr(transparent)]
#[derive(Debug)]
pub struct ChunkBatch<'plane>(Batch<'plane, ChunkDigest>);

impl<'plane> ChunkBatch<'plane>
{
    /// A call's batch over `plane`, holding nothing.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn over(plane: &'plane ChunkDirectory) -> Self
    {
        Self(Batch::over(&plane.0))
    }

    /// Write each chunk the batch took, as [`Batch::publish`] does.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn publish(self) -> Result<(), StoreError>
    {
        self.0.publish()
    }

    /// The bytes of the image held under `digest`, as [`Batch::image`] reads
    /// them, with no second verification.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn size(
        &self,
        digest: ChunkDigest,
    ) -> Maybe<ImageBytes, unheld::Absent>
    {
        match self.0.image(digest) {
            Maybe::Present(image) => Maybe::Present(ImageBytes::of(image)),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        }
    }
}

impl ChunkStore for ChunkBatch<'_>
{
    /// Takes a verified chunk, to be written when the commit ends.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the chunk's digest is held, by the bytes held before or by
    ///   the chunk's image.
    /// - provides: the value plane's write half on disk.
    /// - fails: never; the file is written by the facade, which names its
    ///   failure.
    /// - panics: none.
    /// - executable: none — the held bytes are the batch's and the directory's.
    ///
    /// # Errors
    /// None; the signature is the trait's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs back after reopening.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    #[inline]
    fn insert(
        &mut self,
        chunk: VerifiedChunk<'_>,
    ) -> Result<(), ValueError>
    {
        self.0.take(chunk.digest(), Image(chunk.image().as_ref()));
        Ok(())
    }

    /// Loads and verifies the image held under a digest.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`ChunkStore::load`]; an image that the batch did not
    ///   take, that no segment holds after a scan of the other writers' tails,
    ///   or whose record cannot be read, is unknown.
    /// - provides: the value plane's read half on disk.
    /// - fails: [`ValueError::UnknownChunk`], and [`verify_chunk_image`]'s
    ///   refusals for bytes changed on disk, which mark a listed chunk refused
    ///   so its next insertion writes it afresh.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, and an
    ///   image changed on disk is refused by its digest.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    /// - witness: `tests::store::a_refused_chunk_is_written_afresh_by_the_next_commit_4074`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|chunk| chunk.digest() == digest))]
    fn load(
        &self,
        digest: ChunkDigest,
    ) -> Result<VerifiedChunk<'_>, ValueError>
    {
        let Maybe::Present(Image(bytes)) = self.0.image(digest)
        else {
            return Err(ValueError::UnknownChunk { digest });
        };
        verify_chunk_image(StoredChunkRef::new(digest, ChunkImage::from(bytes)))
            .inspect_err(|_refusal| self.0.plane.refuse(digest))
    }
}

/// The record plane on disk: each node a record of a segment, indexed by its
/// identity.
#[repr(transparent)]
#[derive(Debug)]
pub struct NodeDirectory(Directory<NodeHash>);

impl NodeDirectory
{
    /// The record plane at `path`, as [`Directory::open`] opens it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn open(
        path: PathBuf,
        seal: Seal,
        named: &Named,
    ) -> Result<Self, StoreError>
    {
        Directory::open(path, seal, named).map(Self)
    }

    /// Sync the record plane's segments, as [`Directory::sync`] syncs them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn sync(&self) -> Result<(), StoreError>
    {
        self.0.sync()
    }

    /// Fold the record plane's newly sealed segments into its index, as
    /// [`Directory::fold_index`] folds them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn fold_index(&self) -> Result<Named, StoreError>
    {
        self.0.fold_index()
    }

    /// Close the record plane's index, as [`Directory::close_index`] closes
    /// it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn close_index(&self) -> Result<Named, StoreError>
    {
        self.0.close_index()
    }

    /// Whether the record plane owes a close, as [`Directory::closing`]
    /// reads it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn closing(&self) -> Closing
    {
        self.0.closing()
    }
}

/// One call's batch over the record plane: what a reader of a stored tree
/// loads nodes through.
#[repr(transparent)]
#[derive(Debug)]
pub struct NodeBatch<'plane>(Batch<'plane, NodeHash>);

impl<'plane> NodeBatch<'plane>
{
    /// A call's batch over `plane`, holding nothing.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn over(plane: &'plane NodeDirectory) -> Self
    {
        Self(Batch::over(&plane.0))
    }

    /// Write each node the batch took, as [`Batch::publish`] does.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn publish(self) -> Result<(), StoreError>
    {
        self.0.publish()
    }
}

impl BlockStore for NodeBatch<'_>
{
    /// Admits verified node bytes, to be written when the operation ends.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own precondition.
    /// - ensures: on success the node's identity is held, by the bytes held
    ///   before or by the node's, which were verified first; a refused node
    ///   leaves the batch as it was.
    /// - provides: the record plane's admission on disk.
    /// - fails: propagates [`verify_stored_node`]'s refusal unchanged.
    /// - panics: none.
    /// - executable: none — the held bytes are the batch's and the directory's.
    ///
    /// # Errors
    /// [`RecordTreeError`], as [`verify_stored_node`] refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written tree opens from the plane after reopening.
    /// - witness: `tests::store::a_written_tree_opens_from_the_record_plane_after_reopening`
    #[inline]
    fn insert(
        &mut self,
        node: StoredNode<'_>,
    ) -> Result<(), RecordTreeError>
    {
        verify_stored_node(node)?;
        self.0.take(node.identity(), Image(node.bytes().as_ref()));
        Ok(())
    }

    /// Returns the verified bytes held under an identity.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`BlockStore::load`]; a node that the batch did not take,
    ///   that no segment holds after a scan of the other writers' tails, or
    ///   whose record cannot be read, is unknown.
    /// - provides: the record plane's verified load on disk.
    /// - fails: [`RecordTreeError::UnknownNode`], and [`verify_stored_node`]'s
    ///   refusals for bytes changed on disk, which mark a listed node refused
    ///   so its next insertion writes it afresh.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written tree opens after reopening and in the store
    ///   that wrote it, and a node changed on disk is refused.
    /// - witness: `tests::store::a_written_tree_opens_from_the_record_plane_after_reopening`
    /// - witness: `tests::store::a_written_tree_opens_from_the_store_that_wrote_it_6899`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|node| node.identity() == hash))]
    fn load(
        &self,
        hash: NodeHash,
    ) -> Result<StoredNode<'_>, RecordTreeError>
    {
        let Maybe::Present(Image(bytes)) = self.0.image(hash)
        else {
            return Err(RecordTreeError::UnknownNode { hash });
        };
        let node = StoredNode::new(hash, EncodedNode::from(bytes));
        verify_stored_node(node).inspect_err(|_refusal| self.0.plane.refuse(hash))?;
        Ok(node)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_storage_values::ChunkDigest;
    use quenchant_shape::shape::Maybe;

    use super::Batch;
    use super::Directory;
    use super::Image;
    use super::Named;
    use super::Seal;
    use super::SealBytes;

    /// A plane opened from its index reads no trailer and scans no segment
    /// that the index covers. With each such trailer and each first header
    /// changed on disk, neither a trailer nor a scan finds a record, and each
    /// record past the first of its segment still loads through the index.
    #[test]
    fn a_plane_opens_from_its_index_and_reads_no_trailer()
    {
        let path = std::env::temp_dir().join(format!("gandr-plane-index-{}", std::process::id()));
        let _gone = std::fs::remove_dir_all(&path);
        // A seal at one byte seals each batch's segment.
        let seal = Seal::At(SealBytes(core::num::NonZeroU64::MIN));
        let names: Vec<ChunkDigest> = (0_u8 .. 8_u8)
            .map(|at| ChunkDigest::from([at; 32]))
            .collect();
        let named = {
            let plane = Directory::<ChunkDigest>::open(path.clone(), seal, &Named::default())
                .expect("the plane opens");
            for run in names.chunks(4_usize) {
                let mut batch = Batch::over(&plane);
                for &name in run {
                    batch.take(name, Image(name.as_ref()));
                }
                batch.publish().expect("a batch appends");
            }
            let named = plane.fold_index().expect("the index folds");
            plane.sync().expect("the plane syncs");
            named
        };
        assert!(named.index.is_some(), "the fold names a root");
        assert_eq!(
            named.sealed.len(),
            2_usize,
            "the index covers both segments"
        );
        for sealed in &named.sealed {
            let file = path.join(sealed.segment.file_name());
            let mut bytes = std::fs::read(&file).expect("the segment reads");
            // The trailer's last entry byte, then the first header's checksum.
            for at in [bytes.len().checked_sub(25_usize), Some(60_usize)]
                .into_iter()
                .flatten()
            {
                let byte = bytes.get_mut(at).expect("the byte stands");
                *byte ^= 0xFF_u8;
            }
            std::fs::write(&file, &bytes).expect("the segment is changed");
        }
        let plane = Directory::<ChunkDigest>::open(path.clone(), seal, &named)
            .expect("the plane opens again");
        for (at, &name) in names.iter().enumerate() {
            let listed = plane.listed(name);
            if at % 4_usize == 0_usize {
                assert!(
                    matches!(listed, Maybe::Absent(_)),
                    "a changed first record is refused"
                );
                continue;
            }
            let Maybe::Present(image) = listed
            else {
                panic!("record {at} loads through the index: {listed:?}");
            };
            assert_eq!(image.0, name.as_ref(), "record {at} reads its bytes");
        }
        drop(plane);
        let _gone = std::fs::remove_dir_all(&path);
    }
}
