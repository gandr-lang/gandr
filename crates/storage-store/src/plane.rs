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
//! last naming. A write that
//! fails leaves the shard's end where it was, and the next batch writes over
//! the torn tail. The open of a plane reads every segment's headers in order
//! of the segments' identities, and stops each segment at its first header
//! that does not check. A later record of one identity takes the index from
//! an earlier one.
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
//! The open reads the header of every record, so its cost grows with the
//! store. A root that carries the index removes that cost.
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
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::fs::File;
use std::io;
use std::io::Read as _;
use std::io::Seek as _;
use std::os::unix::fs::FileExt as _;
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

/// How many shards the producers of one store append to. A thread takes the
/// shard of its ordinal modulo this, so the workers of a pool up to this width
/// each own a shard.
const SHARDS: usize = 64_usize;

/// The size past which a shard opens a new segment for its next batch.
const SEGMENT_LIMIT: u64 = 64_u64 << 20_u32;

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

/// The domain a header's checksum is taken in, so it meets no other digest
/// of the store.
const HEADER_DOMAIN: &[u8] = b"gandr storage-store segment record header\0";

/// The bytes the open reads ahead of each header.
const SCAN_BUFFER: usize = 64_usize << 10_u32;

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

/// A record's header, as it stands before the record's bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Header<Name>
{
    /// The length of the record's bytes.
    length: Length,
    /// The identity of the object the record holds.
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
        magic.copy_from_slice(&MAGIC);
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
        if *magic != MAGIC {
            return unchecked;
        }
        let header = Header {
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

/// A shard's open segment, or none before its first batch.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Tail(Option<Open>);

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
    /// The identity the next new segment tries first.
    next: AtomicU64,
    /// The lock a scan of the other writers' tails holds, so one scan runs at
    /// a time.
    catching: Mutex<()>,
}

impl<Name> Directory<Name>
where
    Name: ObjectName,
{
    /// The directory at `path`, made when missing, and every record its
    /// segments hold indexed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a directory at `path`; each record of each segment indexed
    ///   under its identity, up to the segment's first header that does not
    ///   check or record that does not fit, the segments read in order of their
    ///   identities; every other file ignored.
    /// - provides: a plane's index as the store opens.
    /// - fails: [`StoreError::Io`] when the directory cannot be made or listed,
    ///   or a segment cannot be opened or read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: the open reads each record's header and no record's bytes.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing root is made, a committed value loads after
    ///   reopening, and a torn tail is cut.
    /// - witness: `tests::store::a_missing_root_directory_is_made_on_opening`
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_torn_segment_tail_is_cut_on_opening_7462`
    pub fn open(path: PathBuf) -> Result<Self, StoreError>
    {
        std::fs::create_dir_all(&path).map_err(|error| StoreError::io(&path, &error))?;
        let plane = Self {
            path,
            segments: boxcar::Vec::new(),
            known: papaya::HashMap::new(),
            objects: boxcar::Vec::new(),
            index: papaya::HashMap::new(),
            shards: [const { Mutex::new(Tail(None)) }; SHARDS],
            next: AtomicU64::new(0_u64),
            catching: Mutex::new(()),
        };
        plane.catch_up()?;
        Ok(plane)
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
            let slot = Slot(self.segments.push(Segment {
                id,
                file: opened,
                writer: Writer::Other,
                scanned: AtomicU64::new(0_u64),
                dirty: AtomicBool::new(false),
            }));
            let _known = known.insert(id, slot);
        }
        for (at, segment) in &self.segments {
            if segment.writer == Writer::Other {
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
            reader
                .seek_relative(i64::from(header.length.0))
                .map_err(io)?;
            let place = Place {
                segment: slot,
                offset: at,
                length: header.length,
            };
            let filed = Slot(self.objects.push(Filed::at(header.name, place)));
            let _indexed = index.insert(header.name, filed);
            at = end;
        }
        segment.scanned.store(at.0, Ordering::Relaxed);
        Ok(())
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
        if let Maybe::Present(filed) = self.indexed(name) {
            return Maybe::Present(filed);
        }
        if self.catch_up().is_err() {
            return Maybe::Absent(unheld::Absent::Unreadable);
        }
        self.indexed(name)
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
            Maybe::Present(header) if header.name == name && header.length == place.length => {
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
        if let Maybe::Present(filed) = self.indexed(name) {
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
        let Maybe::Present(filed) = self.indexed(name)
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

    /// The open segment of a shard, a new one when the shard has none or its
    /// segment is past [`SEGMENT_LIMIT`].
    ///
    /// # Specification
    /// - requires: `open` is the shard's tail, read under the shard's lock.
    /// - ensures: on success a segment of this process with its end below the
    ///   limit, or a new empty one; a new segment's file and its directory
    ///   entry are durable.
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
        open: Tail,
    ) -> Result<Open, StoreError>
    {
        if let Tail(Some(open)) = open
            && open.end.0 < SEGMENT_LIMIT
        {
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
        let at = self.plane.tail(*open)?;
        // A new segment stays the shard's, so a failed write leaves no
        // segment behind that no shard appends to.
        *open = Tail(Some(at));
        let Some(segment) = self.plane.segments.get(at.segment.0)
        else {
            return Err(StoreError::io(
                &self.plane.path,
                &io::Error::from(io::ErrorKind::NotFound),
            ));
        };
        let mut bytes = Vec::with_capacity(self.taken.values().fold(0_usize, |sum, image| {
            sum.saturating_add(image.len()).saturating_add(HEADER)
        }));
        let mut places = Vec::with_capacity(self.taken.len());
        let mut end = at.end;
        for (&name, image) in &self.taken {
            let length = Length::of(Image(image))?;
            let header = Header {
                length,
                name,
                segment: segment.id,
                offset: end,
            };
            bytes.extend_from_slice(&header.bytes().0);
            bytes.extend_from_slice(image);
            places.push((name, Place {
                segment: at.segment,
                offset: end,
                length,
            }));
            end = end.after(length);
        }
        let file = self.plane.path.join(segment.id.file_name());
        segment
            .file
            .write_all_at(&bytes, at.end.0)
            .map_err(|error| StoreError::io(&file, &error))?;
        // Set after the write, so a sync that clears the mark first still
        // covers the bytes, or the mark stands for the next sync.
        segment.dirty.store(true, Ordering::Release);
        *open = Tail(Some(Open {
            segment: at.segment,
            end,
        }));
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
    pub(crate) fn open(path: PathBuf) -> Result<Self, StoreError>
    {
        Directory::open(path).map(Self)
    }

    /// Sync the value plane's segments, as [`Directory::sync`] syncs them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn sync(&self) -> Result<(), StoreError>
    {
        self.0.sync()
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
    pub(crate) fn open(path: PathBuf) -> Result<Self, StoreError>
    {
        Directory::open(path).map(Self)
    }

    /// Sync the record plane's segments, as [`Directory::sync`] syncs them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn sync(&self) -> Result<(), StoreError>
    {
        self.0.sync()
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
