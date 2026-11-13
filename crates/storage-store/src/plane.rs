//! The two planes on disk: a directory of objects each, one file per object,
//! named by its identity in lowercase hexadecimal.
//!
//! A plane lists its directory when the store opens and never lists it again,
//! so a store shares its planes between threads with no lock. Each object
//! listed holds its bytes under a [`OnceLock`]: the first load in the process
//! reads its file, and each later load borrows those bytes, as both plane
//! traits ask.
//!
//! Each call that reads or writes a plane holds a [`Batch`] over it: the
//! section of the plane that the call owns. A load that the listing does not
//! answer reads the object's file by its name, once in the call, and the batch
//! keeps the bytes for the call's life. An insertion goes into the batch, and
//! [`Batch::publish`] writes each object that the batch took when the call
//! ends: neither plane trait can name a file system's failure, and the facade
//! can. A publication writes a temporary file in the shard of the calling
//! thread and renames it onto its name in the plane, so a reader never meets
//! half an object. Two batches that take one object write the same bytes, so
//! the rename publishes one object. Every load verifies what it read, so bytes
//! changed on disk are refused by the plane's own fault. A listed object that
//! a load refused stands refused, and the next batch that takes its name
//! writes the object over the file.
//!
//! # Boundaries
//!
//! An object that a batch publishes after the store opened is not listed, so
//! each call that loads it reads its file again. A batch takes an unlisted
//! object only when no file stands under its name: one existence probe by its
//! digest. So a file that changes on disk after the store opened stays as it
//! is until a store that lists it refuses it.
//!
//! A thread takes its shard by its ordinal in the process modulo 64, so two
//! threads past that width share a shard, and two processes over one store
//! share each shard. Each temporary takes its name by exclusive creation, so a
//! shared shard costs contention and never a collision. A crash between a
//! temporary's creation and its rename leaves the temporary in its shard, and
//! no listing reads it.
//!
//! # References
//!
//! - `vault:01a178aa-4bbc-7842-9a60-d11551c41e06` — background: § The real leak
//!   was in the filesystem — an object's temporary has one owner, the guard of
//!   the writer it publishes through.
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — anchor: the store's single
//!   writer plan (§ Refinements) — the shard is per producer, the batch that a
//!   call holds given an owner, and the union of shards is renames by digest,
//!   one an object, before any reader that the call orders after it.

use alloc::collections::BTreeMap;
use core::cell::Cell;
use core::cell::OnceCell;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_publish::Contents;
use gandr_core_publish::Step;
use gandr_core_publish::publish_staged;
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

/// The most tables of reads by name that one call holds. Table `n` holds
/// [`FIRST_SLOTS`] times two to the `n` slots, so the last table holds far
/// more objects than a plane does.
const TABLES: usize = 40_usize;

/// The slots of a call's first table of reads by name.
const FIRST_SLOTS: usize = 16_usize;

/// How many shards the producers of one store stage their objects in. A
/// thread takes the shard of its ordinal modulo this, so the workers of a pool
/// up to this width each own a shard.
const SHARDS: usize = 64_usize;

/// The directory beside a store's planes that holds its shards.
const SHARD_ROOT: &str = "shards";

/// The ordinal that the next thread to publish in the process takes.
static ORDINALS: AtomicUsize = AtomicUsize::new(0_usize);

std::thread_local! {
    /// The shard of the calling thread: its ordinal modulo [`SHARDS`], taken
    /// at its first publication.
    static SHARD: usize = ORDINALS.fetch_add(1_usize, Ordering::Relaxed) % SHARDS;
}

/// The identity a plane names its objects by: 32 bytes, spelled as 64
/// lowercase hexadecimal digits.
pub trait ObjectName: Copy + Ord + core::fmt::Display + From<[u8; 32]> + AsRef<[u8]>
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
            /// The plane lists no object of that identity, and no file stands
            /// under its name.
            Unlisted,
            /// The object's file cannot be read.
            Unreadable,
            /// The text spells no identity: it is not exactly 64 lowercase
            /// hexadecimal digits.
            Unspelled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a table of a call's reads by name gives no slot for a name.
    mod probed {
        /// The table gives no slot for the name.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The probe met an empty slot, or went through the whole table,
            /// before the name.
            Vacant,
            /// The table holds three objects in four slots, so it takes no
            /// more.
            Full,
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

/// What a plane holds under a name, for an insertion to read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Holding
{
    /// The plane lists the object, and no load refused it or failed to read
    /// it.
    Held,
    /// The plane lists the object, and a load refused it or could not read
    /// it, so an insertion writes it afresh.
    Refused,
    /// The plane does not list the object.
    Unlisted,
}

/// The bytes of a file as a read gave them, or the kind of the failure.
#[repr(transparent)]
#[derive(Debug)]
struct Read(Result<Box<[u8]>, io::ErrorKind>);

/// The bytes of the file at `file`, or the kind of the failure that stopped
/// the read.
///
/// # Specification
/// trivial.
fn read(file: &Path) -> Read
{
    Read(
        std::fs::read(file)
            .map(Vec::into_boxed_slice)
            .map_err(|error| error.kind()),
    )
}

/// One object a plane listed at open.
#[derive(Debug)]
struct Filed
{
    /// The file's bytes as the first load read them.
    read: OnceLock<Read>,
    /// Whether a load refused the bytes: `true` once one did.
    refused: AtomicBool,
}

impl Filed
{
    /// An object listed and not read yet.
    ///
    /// # Specification
    /// trivial.
    const fn unread() -> Self
    {
        Self {
            read: OnceLock::new(),
            refused: AtomicBool::new(false),
        }
    }
}

/// A directory of objects, each a file named by its identity, listed once.
#[derive(Debug)]
pub struct Directory<Name>
{
    /// The directory.
    path: PathBuf,
    /// The directory of the store's shards, beside the plane's.
    shards: PathBuf,
    /// The directory of each shard, made by the first publication through
    /// it, so a later batch allocates no path for it.
    staged: [OnceLock<PathBuf>; SHARDS],
    /// Every object the directory held when the plane opened, by identity.
    objects: BTreeMap<Name, Filed>,
}

impl<Name> Directory<Name>
where
    Name: ObjectName,
{
    /// The directory at `path`, made when missing, and every object it holds
    /// listed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a directory at `path`; each file named by 64 lowercase
    ///   hexadecimal digits listed as the object of that identity, unread and
    ///   unrefused; every other file ignored.
    /// - provides: a plane's listing as the store opens.
    /// - fails: [`StoreError::Io`] when the directory cannot be made or listed.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing root is made, and a committed value loads
    ///   after reopening.
    /// - witness: `tests::store::a_missing_root_directory_is_made_on_opening`
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    pub fn open(path: PathBuf) -> Result<Self, StoreError>
    {
        std::fs::create_dir_all(&path).map_err(|error| StoreError::io(&path, &error))?;
        let entries = std::fs::read_dir(&path).map_err(|error| StoreError::io(&path, &error))?;
        let mut objects = BTreeMap::new();
        for entry in entries {
            let entry = entry.map_err(|error| StoreError::io(&path, &error))?;
            let Maybe::Present(name) = named::<Name>(&entry.file_name())
            else {
                continue;
            };
            let _listed = objects.insert(name, Filed::unread());
        }
        let shards = path.with_file_name(SHARD_ROOT);
        Ok(Self {
            path,
            shards,
            staged: [const { OnceLock::new() }; SHARDS],
            objects,
        })
    }

    /// The file an object of identity `name` stands in.
    ///
    /// # Specification
    /// trivial.
    fn file(
        &self,
        name: Name,
    ) -> PathBuf
    {
        self.path.join(name.to_string())
    }

    /// The bytes of the listed object `name`, read from its file the first
    /// time a load asks for them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the file's bytes as the first load in the process read them;
    ///   `Unlisted` for a name the plane does not list, `Unreadable` for a file
    ///   that could not be read when first asked for.
    /// - provides: the listing's half of the one read both planes verify.
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
        let Some(filed) = self.objects.get(&name)
        else {
            return Maybe::Absent(unheld::Absent::Unlisted);
        };
        filed
            .read
            .get_or_init(|| read(&self.file(name)))
            .0
            .as_ref()
            .map_or(Maybe::Absent(unheld::Absent::Unreadable), |bytes| {
                Maybe::Present(Image(bytes))
            })
    }

    /// Mark the listed object `name` refused, so the next batch that takes
    /// `name` writes it afresh.
    ///
    /// # Specification
    /// - requires: a load refused the bytes the plane gave for `name` as not
    ///   the object `name` names.
    /// - ensures: a listed object under `name` stands refused; an unlisted name
    ///   changes nothing.
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
        if let Some(filed) = self.objects.get(&name) {
            filed.refused.store(true, Ordering::Relaxed);
        }
    }

    /// What the plane holds under `name`, for an insertion to read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Held` for a listed object that no load refused and that no
    ///   load failed to read, `Refused` for another listed object, `Unlisted`
    ///   for a name the plane does not list.
    /// - provides: whether an insertion of `name` writes its bytes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the standing is an atomic flag and a cell that
    ///   loads on other threads set.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value committed again writes no file, and a refused
    ///   chunk is written afresh.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_refused_chunk_is_written_afresh_by_the_next_commit_4074`
    fn holding(
        &self,
        name: Name,
    ) -> Holding
    {
        let Some(filed) = self.objects.get(&name)
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
}

/// One object a call read by its name.
#[derive(Debug)]
struct Learned<Name>
{
    /// The object's identity.
    name: Name,
    /// The file's bytes, or the kind of the failure that stopped the read.
    read: Read,
}

/// How many slots a table of reads by name holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Slots(usize);

/// Where the probe of a name starts in a table: the first eight bytes of its
/// identity, which a digest spreads evenly.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Start(usize);

impl Start
{
    /// Where the probe of `name` starts.
    ///
    /// # Specification
    /// trivial.
    fn of<Name>(name: Name) -> Self
    where
        Name: ObjectName,
    {
        Self(
            name.as_ref()
                .iter()
                .take(8_usize)
                .fold(0_usize, |start, &byte| {
                    start.wrapping_shl(8_u32) | usize::from(byte)
                }),
        )
    }
}

/// A table of a call's reads by name: open addressing, probed in order, and
/// filled to three objects in four slots at most.
#[derive(Debug)]
struct Table<Name>
{
    /// The slots, a power of two of them.
    slots: Box<[OnceCell<Learned<Name>>]>,
    /// How many slots hold an object.
    filled: Cell<usize>,
}

impl<Name> Table<Name>
where
    Name: ObjectName,
{
    /// An empty table of `slots` slots.
    ///
    /// # Specification
    /// trivial.
    fn sized(slots: Slots) -> Self
    {
        Self {
            slots: core::iter::repeat_with(OnceCell::new)
                .take(slots.0)
                .collect(),
            filled: Cell::new(0_usize),
        }
    }

    /// The slot of `name` in the table: the one that holds it, else the empty
    /// one its probe from `start` meets first.
    ///
    /// # Specification
    /// - requires: the table's slots are a power of two.
    /// - ensures: the slot holding `name`, or the first empty slot the probe
    ///   meets; `Vacant` when the probe goes through every slot and meets
    ///   neither.
    /// - provides: the one probe that finding and taking share.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the slots are cells that an earlier probe filled.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call that reads more objects by name than the first
    ///   table holds reads each of them back, verified, so each probe finds the
    ///   slot of its own name and no other.
    /// - witness: `tests::store::a_written_tree_opens_from_the_store_that_wrote_it_6899`
    fn slot(
        &self,
        name: Name,
        start: Start,
    ) -> Maybe<&OnceCell<Learned<Name>>, probed::Absent>
    {
        let mask = self.slots.len().saturating_sub(1_usize);
        for offset in 0_usize .. self.slots.len() {
            let Some(slot) = self.slots.get(start.0.wrapping_add(offset) & mask)
            else {
                break;
            };
            match slot.get() {
                None => return Maybe::Present(slot),
                Some(learned) if learned.name == name => return Maybe::Present(slot),
                Some(_) => {},
            }
        }
        Maybe::Absent(probed::Absent::Vacant)
    }

    /// The object `name` that the table holds.
    ///
    /// # Specification
    /// - requires: as [`Table::slot`].
    /// - ensures: the object under `name`; `Vacant` when the table holds none.
    /// - provides: a lookup of a read by name.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Table::slot`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Table::slot`].
    /// - witness: `tests::store::a_written_tree_opens_from_the_store_that_wrote_it_6899`
    fn found(
        &self,
        name: Name,
        start: Start,
    ) -> Maybe<&Learned<Name>, probed::Absent>
    {
        match self.slot(name, start) {
            Maybe::Present(slot) => slot
                .get()
                .map_or(Maybe::Absent(probed::Absent::Vacant), Maybe::Present),
            Maybe::Absent(absent) => Maybe::Absent(absent),
        }
    }

    /// The empty slot that takes `name`, counted as filled.
    ///
    /// # Specification
    /// - requires: as [`Table::slot`], and the table holds no object under
    ///   `name`.
    /// - ensures: an empty slot, with one more slot counted filled; `Full` when
    ///   three slots in four hold an object, `Vacant` when the probe meets no
    ///   empty slot.
    /// - provides: the slot a new read by name goes into.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Table::slot`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call that reads more objects by name than three
    ///   slots in four of the first table reads the rest into the next table,
    ///   and reads each back.
    /// - witness: `tests::store::a_written_tree_opens_from_the_store_that_wrote_it_6899`
    fn vacant(
        &self,
        name: Name,
        start: Start,
    ) -> Maybe<&OnceCell<Learned<Name>>, probed::Absent>
    {
        let filled = self.filled.get();
        if filled.saturating_mul(4_usize) >= self.slots.len().saturating_mul(3_usize) {
            return Maybe::Absent(probed::Absent::Full);
        }
        match self.slot(name, start) {
            Maybe::Present(slot) if slot.get().is_none() => {
                self.filled.set(filled.saturating_add(1_usize));
                Maybe::Present(slot)
            },
            Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(probed::Absent::Vacant),
        }
    }
}

/// The objects one call read by their names: tables of open addressing, each
/// twice the size of the one before, in the order they filled.
#[repr(transparent)]
#[derive(Debug)]
struct Reads<Name>
{
    /// The tables, each made when the ones before it are full.
    tables: [OnceCell<Table<Name>>; TABLES],
}

impl<Name> Reads<Name>
where
    Name: ObjectName,
{
    /// No object read.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            tables: [const { OnceCell::new() }; TABLES],
        }
    }

    /// The bytes of the object `name` in `plane`'s directory, read from its
    /// file the first time the call asks for them.
    ///
    /// # Specification
    /// - requires: `plane` does not list `name`.
    /// - ensures: the bytes of the file under `name` as the call's first read
    ///   of it gave them; `Unlisted` when no file stands under the name,
    ///   `Unreadable` when it cannot be read.
    /// - provides: a load of an object that a batch published after the store
    ///   opened.
    /// - fails: never; a missing object is the typed absence.
    /// - panics: none.
    /// - executable: none — the bytes are the file system's.
    /// - intension: the call reads each file once. A lookup probes one table
    ///   for each table the call made, and each table is twice the size of the
    ///   one before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value derefs back in the store that committed it,
    ///   and a record tree that a store wrote opens from the same store.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_written_tree_opens_from_the_store_that_wrote_it_6899`
    fn image<'call>(
        &'call self,
        plane: &Directory<Name>,
        name: Name,
    ) -> Maybe<Image<'call>, unheld::Absent>
    {
        let start = Start::of(name);
        for table in self.tables.iter().map_while(OnceCell::get) {
            if let Maybe::Present(learned) = table.found(name, start) {
                return image(&learned.read);
            }
        }
        let mut pending = Some(read(&plane.file(name)));
        let mut slots = FIRST_SLOTS;
        for table in &self.tables {
            let table = table.get_or_init(|| Table::sized(Slots(slots)));
            slots = slots.saturating_mul(2_usize);
            let Maybe::Present(slot) = table.vacant(name, start)
            else {
                continue;
            };
            let Some(bytes) = pending.take()
            else {
                break;
            };
            return image(&slot.get_or_init(|| Learned { name, read: bytes }).read);
        }
        Maybe::Absent(unheld::Absent::Unreadable)
    }
}

/// Why a read by name gave no bytes: no file under the name, or a file that
/// cannot be read.
///
/// # Specification
/// trivial.
fn absent(kind: io::ErrorKind) -> unheld::Absent
{
    if kind == io::ErrorKind::NotFound {
        unheld::Absent::Unlisted
    }
    else {
        unheld::Absent::Unreadable
    }
}

/// The bytes a read by name gave, or why it gave none.
///
/// # Specification
/// trivial.
fn image(read: &Read) -> Maybe<Image<'_>, unheld::Absent>
{
    read.0.as_ref().map_or_else(
        |&kind| Maybe::Absent(absent(kind)),
        |bytes| Maybe::Present(Image(bytes)),
    )
}

/// One call's section over a plane: the objects it took, to publish when the
/// call ends, and the objects it read by name.
#[derive(Debug)]
pub struct Batch<'plane, Name>
{
    /// The plane the call reads and writes.
    plane: &'plane Directory<Name>,
    /// The objects the call read by name.
    reads: Reads<Name>,
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
            reads: Reads::new(),
            taken: BTreeMap::new(),
        }
    }

    /// The bytes under `name`: taken by the call, listed by the plane, or
    /// read from the file by name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the bytes the call took under `name`, else the listed
    ///   object's, else the bytes of the file under `name` as the call first
    ///   read them; the reason when none of the three gives bytes.
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
        match self.plane.listed(name) {
            Maybe::Present(image) => Maybe::Present(image),
            Maybe::Absent(unheld::Absent::Unlisted) => self.reads.image(self.plane, name),
            Maybe::Absent(absent @ (unheld::Absent::Unreadable | unheld::Absent::Unspelled)) => {
                Maybe::Absent(absent)
            },
        }
    }

    /// Take `bytes` under `name`, to be written when the batch publishes,
    /// unless the plane holds `name` already.
    ///
    /// # Specification
    /// - requires: `bytes` are verified as the object `name` names.
    /// - ensures: a name the call took, or the plane lists unrefused and
    ///   readable, or that has a file though the plane does not list it, keeps
    ///   what it holds; another name, or one a load refused or could not read,
    ///   is taken as `bytes`.
    /// - provides: the insertion both plane traits make.
    /// - fails: never; a failed existence probe takes the bytes.
    /// - panics: none.
    /// - executable: none — the existence probe is the file system's.
    /// - intension: a name the plane lists costs no system call; an unlisted
    ///   name costs one existence probe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs before and after reopening,
    ///   committing it again writes no file, and a refused chunk is written
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
            Holding::Unlisted
                if std::fs::exists(self.plane.file(name)).is_ok_and(|exists| exists) =>
            {
                return;
            },
            Holding::Refused | Holding::Unlisted => {},
        }
        let _taken = self.taken.insert(name, Box::from(bytes.0));
    }

    /// Write each object the batch took to its file, through the shard of the
    /// calling thread.
    ///
    /// A shard is a directory of the calling thread's own beside the planes,
    /// and each publication goes through `gandr_core_publish` with its
    /// temporary there. So the plane's directory sees one rename for each
    /// object, and the creation of each temporary touches only the thread's
    /// shard. The producers of a pool contend on no directory to create a
    /// temporary. The union of the shards is set union by digest, and that one
    /// rename is all of it. An object is in the plane before the call that put
    /// it returns, so a read after that call finds the object in the plane.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success each object the batch took is a file of the
    ///   plane's directory under its name, and no temporary of it stays in the
    ///   shard of the calling thread. A batch that took nothing touches no
    ///   directory.
    /// - provides: the end of every facade operation that inserts, and the
    ///   union of the thread's shard into the plane: one rename an object.
    /// - fails: [`StoreError::Io`] for the first file that cannot be written,
    ///   or for a shard directory that cannot be made; the objects after it are
    ///   not written.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, which reads
    ///   only what was written; sixteen writers of one value leave one file per
    ///   chunk; and sixteen writers of distinct values leave every object in
    ///   the plane and each shard empty.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::sixteen_writers_of_one_value_leave_one_object_per_digest_6899`
    /// - witness: `tests::store::sixteen_writers_stage_in_their_shards_and_leave_each_empty_7204`
    fn publish(self) -> Result<(), StoreError>
    {
        if self.taken.is_empty() {
            return Ok(());
        }
        let shard = SHARD.with(|shard| *shard);
        // The ordinal is taken modulo the table's length, so the table holds
        // the slot; the shards' root stands in only to keep the call total.
        let staging: &Path = self
            .plane
            .staged
            .get(shard)
            .map_or(&self.plane.shards, |slot| {
                slot.get_or_init(|| self.plane.shards.join(shard.to_string()))
            });
        for (name, bytes) in &self.taken {
            match publish_staged(staging, &self.plane.path, name, Contents(bytes)) {
                Err(ref fault)
                    if fault.step == Step::Create && fault.kind == io::ErrorKind::NotFound =>
                {
                    std::fs::create_dir_all(staging)
                        .map_err(|error| StoreError::io(staging, &error))?;
                    publish_staged(staging, &self.plane.path, name, Contents(bytes))
                        .map_err(StoreError::from)?;
                },
                published => published.map_err(StoreError::from)?,
            }
        }
        Ok(())
    }
}

/// The identity a file's name spells, or none for any other name.
///
/// # Specification
/// trivial.
fn named<Name>(file: &std::ffi::OsStr) -> Maybe<Name, unheld::Absent>
where
    Name: ObjectName,
{
    file.to_str()
        .map_or(Maybe::Absent(unheld::Absent::Unspelled), |text| {
            hexadecimal(FileName(text))
        })
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

/// The value plane on disk: each chunk image a file named by its digest.
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
    ///   take, that the directory does not list and that no file holds, or
    ///   whose file cannot be read, is unknown.
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

/// The record plane on disk: each node a file named by its identity.
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
    ///   that the directory does not list and that no file holds, or whose file
    ///   cannot be read, is unknown.
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
