//! Named roots: a small record tree on the record plane, each record a name
//! and the content pointer it names, and a journal of the namings since.
//!
//! A root names where something stands in the store by a name of the
//! consumer's own, as `lock/<package address>` or `verdict/<key>`. The tree's
//! records are each name's bytes keyed to the pointer's digest and then its
//! offset as four little-endian bytes; the file `roots` at the store's root
//! holds the tree's root node identity in lowercase hexadecimal. Reading the
//! tree loads that node and its leaves from the record plane, which verifies
//! each, then builds the tree again from their records and refuses a tree
//! whose root node is not the one the file names.
//!
//! The file `roots.journal` holds the namings since the tree. [`Kept`] reads
//! it, appends to it and folds it into the tree, so a naming costs amortised
//! constant time.
//!
//! # Boundaries
//!
//! A root is local to the store it is set in: a content pointer crosses hosts,
//! and a name is what one host's consumer chose. A root states where a value
//! stands, never that it is valid.
//!
//! An entry is appended unsynced, as a publication renames unsynced: a crash
//! may lose the last namings, and never makes a root name a pointer no naming
//! gave it.

use alloc::collections::BTreeMap;
use std::fs::File;
use std::io;
use std::io::Read as _;
use std::io::Seek as _;
use std::io::Write as _;
use std::path::Path;

use anodized::spec;
use gandr_core_publish::Contents;
use gandr_core_publish::publish;
use gandr_storage_records::BlockStore as _;
use gandr_storage_records::DecodeWork;
use gandr_storage_records::DecodedNode;
use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use gandr_storage_records::decode_node;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::TokenOffset;
use quenchant_shape::shape::Maybe;

use crate::plane::FileName;
use crate::plane::NodeDirectory;
use crate::plane::hexadecimal;
use crate::store::RootsFault;
use crate::store::StoreError;

/// The file at a store's root naming its roots tree's root node.
pub const ROOTS: &str = "roots";

/// The file at a store's root journaling the namings since its roots tree.
pub const JOURNAL: &str = "roots.journal";

/// The bytes a root's pointer is recorded as: its digest, then its offset.
const POINTER_LEN: usize = 36_usize;

/// The bytes a journal opens with.
const MAGIC: [u8; 8] = *b"gandr-rj";

/// The bytes of a journal's header: the magic, the tree's root node and the
/// generation.
const HEADER_LEN: usize = 48_usize;

/// Where a journal's first entry stands: just past its header.
const FIRST_ENTRY: u64 = 48_u64;

/// The bytes of an entry's name length.
const LENGTH_LEN: usize = 4_usize;

/// The bytes of an entry's digest.
const DIGEST_LEN: usize = 32_usize;

/// The domain an entry's digest is taken in, so it meets no other digest of
/// the store.
const ENTRY_DOMAIN: &[u8] = b"gandr storage-store roots journal entry\0";

/// The fewest entries a journal folds at.
const FOLD_FLOOR: usize = 64_usize;

/// A root's name, chosen by the consumer that sets it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RootName(String);

impl RootName
{
    /// The root named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(name: String) -> Self
    {
        Self(name)
    }
}

impl AsRef<str> for RootName
{
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl core::fmt::Display for RootName
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(&self.0)
    }
}

quenchant_shape::reason_enum! {
    /// Why a store names no root by a name.
    pub mod unrooted {
        /// The store's roots hold no root of the name.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No root of the name is set.
            Unset,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a store's directory names no roots tree.
    mod untreed {
        /// The reason no tree is named.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No roots file stands.
            Unwritten,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a journal opens with no header.
    mod unheaded {
        /// The reason no header is read.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The journal holds fewer bytes than a header.
            Short,
            /// Its first bytes are not a journal's magic.
            Foreign,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a journal's bytes from an offset on decode no entry.
    mod unentered {
        /// The reason no entry is read.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No bytes are left: the journal ends there.
            Ended,
            /// The bytes are no whole entry whose digest verifies: a naming
            /// stopped while it appended.
            Torn,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a naming takes no journal entry.
    mod unjournaled {
        /// The reason the naming folds instead.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The name is longer than four bytes count.
            Long,
        }
    }
}

/// A store's named roots.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Roots(BTreeMap<RootName, ContentPtr>);

impl Roots
{
    /// The pointer the root `name` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn root(
        &self,
        name: &RootName,
    ) -> Maybe<ContentPtr, unrooted::Absent>
    {
        self.0
            .get(name)
            .map_or(Maybe::Absent(unrooted::Absent::Unset), |&pointer| {
                Maybe::Present(pointer)
            })
    }

    /// Each root's name, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn names(&self) -> impl Iterator<Item = &RootName>
    {
        self.0.keys()
    }

    /// The roots the tree whose root node is `tree` holds, its nodes learned
    /// from `nodes` by name.
    ///
    /// # Specification
    /// - requires: `nodes` is the record plane of the store at `directory`.
    /// - ensures: on success the records of the tree whose root node is `tree`,
    ///   each a name and a pointer, when that node and its leaves load verified
    ///   from `nodes` and build again to `tree`. Only the tree's own nodes are
    ///   learned and read.
    /// - provides: the tree every full reading starts from.
    /// - fails: [`StoreError::Record`] for a node the plane cannot find or
    ///   refuses, and [`StoreError::Roots`] for anything else that is not a
    ///   roots tree.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root set reads back after reopening, and a second
    ///   store reads the first's tree after a fold.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    /// - witness: `tests::store::two_stores_keep_each_other_s_roots_across_a_fold_4081`
    fn tree(
        directory: &Path,
        nodes: &mut NodeDirectory,
        tree: NodeHash,
    ) -> Result<Self, StoreError>
    {
        let path = directory.join(ROOTS);
        let unrooted = |fault: RootsFault| StoreError::Roots {
            path: path.clone(),
            fault,
        };
        let records = leaves(nodes, tree)?;
        let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
        let built = RecordTree::build(&refs, TreeParams::current()).map_err(StoreError::Record)?;
        if built.root_node_hash() != tree {
            return Err(unrooted(RootsFault::Unbuilt));
        }
        let mut roots = BTreeMap::new();
        for record in &records {
            let key = record.key();
            let name = core::str::from_utf8(key.as_ref())
                .map_err(|_utf8| unrooted(RootsFault::Unnamed))?;
            let name = RootName(String::from(name));
            let pointer = pointed(record, &name).map_err(unrooted)?;
            let _named = roots.insert(name, pointer);
        }
        Ok(Self(roots))
    }

    /// Write the roots as a tree into `nodes` and name its root node in the
    /// [`ROOTS`] file of `directory`.
    ///
    /// # Specification
    /// - requires: `nodes` is the record plane of the store at `directory`, and
    ///   the roots name at least one root.
    /// - ensures: on success the tree of the roots' records is written to the
    ///   plane's directory and the file names its root node, which is returned,
    ///   so [`Roots::tree`] reads these roots back from it.
    /// - provides: the write every fold makes.
    /// - fails: [`StoreError::Record`] when the tree cannot be built or
    ///   admitted, [`StoreError::Io`] when a file cannot be written.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root set reads back after reopening.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    fn write(
        &self,
        directory: &Path,
        nodes: &mut NodeDirectory,
    ) -> Result<NodeHash, StoreError>
    {
        let values: Vec<(&RootName, Recorded)> = self
            .0
            .iter()
            .map(|(name, &pointer)| (name, Recorded::from(pointer)))
            .collect();
        let refs: Vec<RecordRef<'_>> = values
            .iter()
            .map(|&(name, ref value)| RecordRef::new(name.0.as_bytes(), value.0.as_slice()))
            .collect();
        let tree = RecordTree::build(&refs, TreeParams::current()).map_err(StoreError::Record)?;
        tree.write_to(nodes).map_err(StoreError::Record)?;
        nodes.write()?;
        publish(
            directory,
            ROOTS,
            Contents(format!("{}\n", tree.root_node_hash()).as_bytes()),
        )
        .map_err(StoreError::from)?;
        Ok(tree.root_node_hash())
    }
}

/// A journal's generation: each fold publishes the next.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Generation(u64);

impl Generation
{
    /// The generation a fold over this one publishes.
    ///
    /// # Specification
    /// trivial.
    const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// A journal's header: the tree its entries follow, and its generation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Header
{
    /// The roots tree's root node.
    tree: NodeHash,
    /// The generation the fold that published it gave.
    generation: Generation,
}

/// A header's bytes: the magic, the tree's root node, and the generation as
/// eight little-endian bytes.
#[repr(transparent)]
struct HeaderBytes([u8; HEADER_LEN]);

impl From<Header> for HeaderBytes
{
    /// The bytes `header` is written as.
    ///
    /// # Specification
    /// trivial.
    fn from(header: Header) -> Self
    {
        let mut bytes = [0_u8; HEADER_LEN];
        let (magic, rest) = bytes.split_at_mut(MAGIC.len());
        magic.copy_from_slice(&MAGIC);
        let (tree, generation) = rest.split_at_mut(32);
        tree.copy_from_slice(header.tree.as_ref());
        generation.copy_from_slice(&header.generation.0.to_le_bytes());
        Self(bytes)
    }
}

impl HeaderBytes
{
    /// The header these bytes spell.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`unheaded::Absent::Foreign`] for bytes that do not open with
    /// [`MAGIC`].
    fn header(&self) -> Maybe<Header, unheaded::Absent>
    {
        let (magic, rest) = self.0.split_at(MAGIC.len());
        let (tree, generation) = rest.split_at(32);
        match (
            magic == MAGIC.as_slice(),
            <[u8; 32]>::try_from(tree),
            <[u8; 8]>::try_from(generation),
        ) {
            (true, Ok(tree), Ok(generation)) => Maybe::Present(Header {
                tree: NodeHash::from(tree),
                generation: Generation(u64::from_le_bytes(generation)),
            }),
            (false, ..) | (true, Err(_), _) | (true, _, Err(_)) => {
                Maybe::Absent(unheaded::Absent::Foreign)
            },
        }
    }
}

/// How far a store has read the journal over its tree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Read
{
    /// The journal's header.
    header: Header,
    /// The journal's bytes read, the header's included: where the next entry
    /// goes.
    end: u64,
    /// The entries read.
    entries: usize,
}

/// Where a store's reading of its roots stands.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Reading
{
    /// No roots file stood.
    #[default]
    Untreed,
    /// The tree stood with no journal over it: a fold stopped before its
    /// journal, or no fold wrote one.
    Stale
    {
        /// The tree's root node.
        tree: NodeHash,
    },
    /// The tree stood with its journal, read up to `read`.
    Current
    {
        /// The roots the tree holds.
        tree_roots: usize,
        /// How far the journal is read.
        read: Read,
    },
}

/// A store's roots, and where its reading of the tree and the journal stands.
///
/// The journal's header names the tree's root node and a generation. Each
/// entry holds the name's length as four little-endian bytes, the name, the
/// pointer as the tree records it, and a digest of the name and the pointer. A
/// naming appends one entry, so it reads only the entries other stores
/// appended since its store last read. Once the journal holds as many entries
/// as the tree holds roots, and at least [`FOLD_FLOOR`], the next naming
/// folds: it builds the tree again with every root, names it in `roots`, then
/// publishes an empty journal of the next generation. A tree of n roots is
/// built after at least n namings, so a naming costs amortised constant time.
///
/// A journal whose header names another tree is stale: a fold named its tree
/// and stopped before it published the journal. The tree holds its entries,
/// so a reading skips them, and the next naming folds. An entry whose digest
/// fails ends the journal: a naming stopped while it appended, and the next
/// naming cuts the file there.
#[derive(Debug, Default)]
pub struct Kept
{
    /// The roots, as last read or written.
    roots: Roots,
    /// Where the reading stands.
    reading: Reading,
}

impl Kept
{
    /// The roots, as last read or written.
    ///
    /// # Specification
    /// trivial.
    pub const fn roots(&self) -> &Roots
    {
        &self.roots
    }

    /// The roots the store at `directory` names: its tree's, then each entry
    /// of the journal over that tree.
    ///
    /// # Specification
    /// - requires: `nodes` is the record plane of the store at `directory`, and
    ///   the caller holds the roots lock.
    /// - ensures: none when no [`ROOTS`] file stands; otherwise the records of
    ///   the tree whose root node the file names, then each entry the journal
    ///   over that tree holds, in order, up to its end or the first entry that
    ///   does not verify. A journal over another tree adds nothing.
    /// - provides: the roots a store holds as it opens.
    /// - fails: as [`Kept::catch_up`].
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root set reads back after reopening, from the tree
    ///   or from the journal, and a torn entry ends the journal.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    /// - witness: `tests::store::a_torn_journal_entry_is_cut_by_the_next_naming_4081`
    pub fn read(
        directory: &Path,
        nodes: &mut NodeDirectory,
    ) -> Result<Self, StoreError>
    {
        let mut kept = Self::default();
        let mut journal = journal(directory)?;
        let _seen = kept.catch_up(directory, nodes, &mut journal)?;
        Ok(kept)
    }

    /// Name `pointer` by `name`: append one entry to the journal, or fold the
    /// journal into a tree once it holds as many entries as the tree holds
    /// roots.
    ///
    /// # Specification
    /// - requires: `nodes` is the record plane of the store at `directory`, and
    ///   the caller holds the roots lock alone.
    /// - ensures: on success the roots [`Kept::catch_up`] reads, with `name`
    ///   naming `pointer`, are this store's and stand on disk, so a store
    ///   opened later reads them. The naming appends one entry when the journal
    ///   stands over the tree and holds fewer entries than the tree holds roots
    ///   or than [`FOLD_FLOOR`]; it folds otherwise.
    /// - provides: the one way a root changes.
    /// - fails: as [`Kept::catch_up`], [`StoreError::Io`] for a journal that
    ///   cannot be cut or appended to, and as [`Kept::fold`].
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: the work is the entries other stores appended since this
    ///   reading, and one more. A fold builds a tree of n roots after at least
    ///   n namings since the last fold, so a naming costs amortised constant
    ///   time.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — namings read back after reopening, the record plane
    ///   holds far fewer nodes than namings, two stores keep each other's roots
    ///   across a fold, and a torn entry is cut by the next naming.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    /// - witness: `tests::store::naming_roots_one_at_a_time_writes_no_tree_per_naming_4081`
    /// - witness: `tests::store::two_stores_keep_each_other_s_roots_across_a_fold_4081`
    /// - witness: `tests::store::a_torn_journal_entry_is_cut_by_the_next_naming_4081`
    pub fn name(
        &mut self,
        directory: &Path,
        nodes: &mut NodeDirectory,
        name: RootName,
        pointer: ContentPtr,
    ) -> Result<(), StoreError>
    {
        let mut journal = journal(directory)?;
        let seen = self.catch_up(directory, nodes, &mut journal)?;
        if let Reading::Current { tree_roots, read } = self.reading
            && read.entries < tree_roots.max(FOLD_FLOOR)
            && let Maybe::Present(entry) = Entry::new(&name, pointer)
        {
            let path = directory.join(JOURNAL);
            let io = |error: io::Error| StoreError::io(&path, &error);
            journal.set_len(read.end).map_err(io)?;
            let _at = journal.seek(io::SeekFrom::Start(read.end)).map_err(io)?;
            journal.write_all(&entry.0).map_err(io)?;
            let appended = u64::try_from(entry.0.len()).unwrap_or(u64::MAX);
            let read = Read {
                end: read.end.saturating_add(appended),
                entries: read.entries.saturating_add(1),
                ..read
            };
            let _named = self.roots.0.insert(name, pointer);
            self.reading = Reading::Current { tree_roots, read };
            return Ok(());
        }
        self.fold(directory, nodes, seen, (name, pointer))
    }

    /// Fold the journal: the roots, with the naming's name naming its pointer,
    /// written as a tree and named in [`ROOTS`], then an empty journal of the
    /// generation after `seen` published over it.
    ///
    /// # Specification
    /// - requires: as [`Kept::name`], and `seen` the generation of the
    ///   journal's header, or the first where none stands.
    /// - ensures: on success the roots with the naming are this store's, the
    ///   tree is named, and the journal over it is current and empty. When the
    ///   tree cannot be written the roots are as they were; when the journal
    ///   cannot be published the tree stands named, the reading is stale over
    ///   it, and the next naming folds again.
    /// - provides: the one write of a whole roots tree.
    /// - fails: as [`Roots::write`], and [`StoreError::Io`] for a journal that
    ///   cannot be published.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — namings across a fold read back after reopening, and
    ///   a second store reads the fold's tree.
    /// - witness: `tests::store::naming_roots_one_at_a_time_writes_no_tree_per_naming_4081`
    /// - witness: `tests::store::two_stores_keep_each_other_s_roots_across_a_fold_4081`
    fn fold(
        &mut self,
        directory: &Path,
        nodes: &mut NodeDirectory,
        seen: Generation,
        (name, pointer): (RootName, ContentPtr),
    ) -> Result<(), StoreError>
    {
        let previous = self.roots.0.insert(name.clone(), pointer);
        let tree = match self.roots.write(directory, nodes) {
            Ok(tree) => tree,
            Err(fault) => {
                let _restored = match previous {
                    Some(previous) => self.roots.0.insert(name, previous),
                    None => self.roots.0.remove(&name),
                };
                return Err(fault);
            },
        };
        let tree_roots = self.roots.0.len();
        self.reading = Reading::Stale { tree };
        let header = Header {
            tree,
            generation: seen.next(),
        };
        publish(directory, JOURNAL, Contents(&HeaderBytes::from(header).0))
            .map_err(StoreError::from)?;
        self.reading = Reading::Current {
            tree_roots,
            read: Read {
                header,
                end: FIRST_ENTRY,
                entries: 0,
            },
        };
        Ok(())
    }

    /// Read what changed in the roots since this reading: the journal's new
    /// entries, or the tree and its journal again when a fold changed either.
    ///
    /// # Specification
    /// - requires: as [`Kept::read`].
    /// - ensures: on success the roots and the reading are those [`Kept::read`]
    ///   gives now, and the generation returned is the journal header's, or the
    ///   first where none stands. The tree is read only when the roots file or
    ///   the journal's header changed since this reading.
    /// - provides: the reading every naming starts from.
    /// - fails: [`StoreError::Io`] for a file that cannot be read,
    ///   [`StoreError::Record`] for a node the plane refuses, and
    ///   [`StoreError::Roots`] for a roots file that names no tree.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two stores over one directory keep each other's
    ///   roots, within a journal and across a fold.
    /// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
    /// - witness: `tests::store::two_stores_keep_each_other_s_roots_across_a_fold_4081`
    fn catch_up(
        &mut self,
        directory: &Path,
        nodes: &mut NodeDirectory,
        journal: &mut File,
    ) -> Result<Generation, StoreError>
    {
        let path = directory.join(JOURNAL);
        let header = header(journal, &path)?;
        let seen = match header {
            Maybe::Present(header) => header.generation,
            Maybe::Absent(_) => Generation::default(),
        };
        let named = named_tree(directory)?;
        let Maybe::Present(tree) = named
        else {
            *self = Self::default();
            return Ok(seen);
        };
        let over = match header {
            Maybe::Present(header) if header.tree == tree => Maybe::Present(header),
            Maybe::Present(_) => Maybe::Absent(unheaded::Absent::Foreign),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        match (self.reading, over) {
            (Reading::Current { read, .. }, Maybe::Present(header)) if read.header == header => {},
            (Reading::Stale { tree: stale }, Maybe::Absent(_)) if stale == tree => {
                return Ok(seen);
            },
            (Reading::Untreed | Reading::Stale { .. } | Reading::Current { .. }, _) => {
                let roots = Roots::tree(directory, nodes, tree)?;
                let tree_roots = roots.0.len();
                self.roots = roots;
                let Maybe::Present(header) = over
                else {
                    self.reading = Reading::Stale { tree };
                    return Ok(seen);
                };
                self.reading = Reading::Current {
                    tree_roots,
                    read: Read {
                        header,
                        end: FIRST_ENTRY,
                        entries: 0,
                    },
                };
            },
        }
        self.replay(journal, &path)?;
        Ok(seen)
    }

    /// Read each entry the journal holds past the reading's end, in order, up
    /// to the journal's end or the first entry that does not verify.
    ///
    /// # Specification
    /// - requires: `journal` is the journal at `path`.
    /// - ensures: on success each entry read names its pointer in the roots,
    ///   and a current reading ends after the last; a reading that is not
    ///   current is as it was.
    /// - provides: the namings another store appended, read without the tree.
    /// - fails: [`StoreError::Io`] for a journal that cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second store reads the first's journaled root, and
    ///   a torn entry ends the journal.
    /// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
    /// - witness: `tests::store::a_torn_journal_entry_is_cut_by_the_next_naming_4081`
    fn replay(
        &mut self,
        journal: &mut File,
        path: &Path,
    ) -> Result<(), StoreError>
    {
        let Reading::Current {
            tree_roots,
            mut read,
        } = self.reading
        else {
            return Ok(());
        };
        let io = |error: io::Error| StoreError::io(path, &error);
        let _at = journal.seek(io::SeekFrom::Start(read.end)).map_err(io)?;
        let mut bytes = Vec::new();
        let _taken = io::copy(journal, &mut bytes).map_err(io)?;
        let mut tail = bytes.as_slice();
        while let Maybe::Present(entered) = decoded(Tail(tail)) {
            tail = tail.get(entered.length ..).unwrap_or_default();
            let length = u64::try_from(entered.length).unwrap_or(u64::MAX);
            read.end = read.end.saturating_add(length);
            read.entries = read.entries.saturating_add(1);
            let _named = self.roots.0.insert(entered.name, entered.pointer);
        }
        self.reading = Reading::Current { tree_roots, read };
        Ok(())
    }
}

/// The root node the [`ROOTS`] file of the store at `directory` names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Unwritten` when no file stands; the identity the file spells
///   otherwise.
/// - provides: the tree every reading starts from.
/// - fails: [`StoreError::Io`] for a file that cannot be read, and
///   [`StoreError::Roots`] naming [`RootsFault::Unspelled`] for one that spells
///   no node.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a root set reads back after reopening, and a file
///   spelling no node is refused by name.
/// - witness: `tests::store::a_root_set_reads_back_after_reopening`
/// - witness: `tests::store::a_roots_file_naming_no_node_is_refused_on_opening`
fn named_tree(directory: &Path) -> Result<Maybe<NodeHash, untreed::Absent>, StoreError>
{
    let path = directory.join(ROOTS);
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(ref error) if error.kind() == io::ErrorKind::NotFound => {
            return Ok(Maybe::Absent(untreed::Absent::Unwritten));
        },
        Err(ref error) => return Err(StoreError::io(&path, error)),
    };
    let Some(Maybe::Present(hash)) = text
        .strip_suffix('\n')
        .map(|spelled| hexadecimal::<NodeHash>(FileName(spelled)))
    else {
        return Err(StoreError::Roots {
            path,
            fault: RootsFault::Unspelled,
        });
    };
    Ok(Maybe::Present(hash))
}

/// The journal of the store at `directory`, made empty where it is missing,
/// opened to read and to append.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the [`JOURNAL`] file stands at `directory`, its bytes
///   as they were, and the file returned reads and writes it.
/// - provides: the handle every reading and naming takes the journal by.
/// - fails: [`StoreError::Io`] when the file cannot be opened or made.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a journaled root reads back after reopening.
/// - witness: `tests::store::a_root_set_reads_back_after_reopening`
fn journal(directory: &Path) -> Result<File, StoreError>
{
    let path = directory.join(JOURNAL);
    std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(&path)
        .map_err(|error| StoreError::io(&path, &error))
}

/// The header `journal` opens with.
///
/// # Specification
/// - requires: `journal` is the journal at `path`.
/// - ensures: `Short` for a journal of fewer bytes than a header, `Foreign` for
///   one that does not open with [`MAGIC`]; the tree and the generation its
///   header names otherwise.
/// - provides: the header every reading compares with its own.
/// - fails: [`StoreError::Io`] for a journal that cannot be read.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — two stores over one directory keep each other's roots
///   across a fold, which each reads by the header.
/// - witness: `tests::store::two_stores_keep_each_other_s_roots_across_a_fold_4081`
fn header(
    journal: &mut File,
    path: &Path,
) -> Result<Maybe<Header, unheaded::Absent>, StoreError>
{
    let io = |error: io::Error| StoreError::io(path, &error);
    let _at = journal.seek(io::SeekFrom::Start(0)).map_err(io)?;
    let mut bytes = [0_u8; HEADER_LEN];
    match journal.read_exact(&mut bytes) {
        Ok(()) => Ok(HeaderBytes(bytes).header()),
        Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => {
            Ok(Maybe::Absent(unheaded::Absent::Short))
        },
        Err(error) => Err(io(error)),
    }
}

/// The records of the tree whose root node is `hash`: its own when it is a
/// leaf, else each child leaf's in order, each node learned by name first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the records of the root node, or of each leaf it
///   names, each node learned by `nodes` and verified on its load.
/// - provides: the walk [`Roots::tree`] builds the tree again from.
/// - fails: [`StoreError::Record`] for a node that does not load or decode, or
///   an internal node naming a child that is not a leaf.
/// - panics: none.
/// - executable: none — the nodes are the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a root set reads back after reopening, and a second store
///   reads the tree another wrote.
/// - witness: `tests::store::a_root_set_reads_back_after_reopening`
/// - witness: `tests::store::two_stores_keep_each_other_s_roots_across_a_fold_4081`
fn leaves(
    nodes: &mut NodeDirectory,
    hash: NodeHash,
) -> Result<Vec<Record>, StoreError>
{
    let mut work = DecodeWork::new();
    nodes.learn(hash);
    let children: Vec<NodeHash> = {
        let root = nodes.load(hash).map_err(StoreError::Record)?;
        let decoded = decode_node(root.bytes(), &mut work).map_err(StoreError::Record)?;
        match decoded {
            DecodedNode::Leaf(leaf) => return Ok(leaf.records().to_vec()),
            DecodedNode::Internal(internal) => internal
                .children()
                .iter()
                .map(gandr_storage_records::ChildRef::identity)
                .collect(),
        }
    };
    let mut records = Vec::new();
    for child in children {
        nodes.learn(child);
        let node = nodes.load(child).map_err(StoreError::Record)?;
        let decoded = decode_node(node.bytes(), &mut work).map_err(StoreError::Record)?;
        let leaf = decoded.as_leaf().map_err(StoreError::Record)?;
        records.extend_from_slice(leaf.records());
    }
    Ok(records)
}

/// A root's pointer as its record's value: its digest, then its offset as
/// four little-endian bytes.
#[repr(transparent)]
struct Recorded([u8; POINTER_LEN]);

impl From<ContentPtr> for Recorded
{
    /// The value `pointer` is recorded as.
    ///
    /// # Specification
    /// trivial.
    fn from(pointer: ContentPtr) -> Self
    {
        let mut bytes = [0_u8; POINTER_LEN];
        let (digest, offset) = bytes.split_at_mut(32);
        digest.copy_from_slice(pointer.digest().as_ref());
        offset.copy_from_slice(&u32::from(pointer.offset()).to_le_bytes());
        Self(bytes)
    }
}

impl Recorded
{
    /// The pointer these bytes record.
    ///
    /// # Specification
    /// trivial.
    fn pointer(&self) -> ContentPtr
    {
        let (digest, offset) = self.0.split_at(32);
        let mut digested = [0_u8; 32];
        digested.copy_from_slice(digest);
        let mut counted = [0_u8; 4];
        counted.copy_from_slice(offset);
        ContentPtr::new(
            ChunkDigest::from(digested),
            TokenOffset::from(u32::from_le_bytes(counted)),
        )
    }
}

/// The pointer `record`'s value records, the root `name` names.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`RootsFault::Unpointed`] naming `name`, for a value that is not a
/// [`Recorded`] pointer.
fn pointed(
    record: &Record,
    name: &RootName,
) -> Result<ContentPtr, RootsFault>
{
    <[u8; POINTER_LEN]>::try_from(record.value().as_ref())
        .map(|bytes| Recorded(bytes).pointer())
        .map_err(|_length| RootsFault::Unpointed { name: name.clone() })
}

/// The digest an entry carries: of its domain, its name and its recorded
/// pointer.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq)]
struct EntryDigest([u8; DIGEST_LEN]);

impl EntryDigest
{
    /// The digest an entry naming `pointer` by `name` carries.
    ///
    /// # Specification
    /// trivial.
    fn of(
        name: &RootName,
        pointer: &Recorded,
    ) -> Self
    {
        let mut hasher = blake3::Hasher::new();
        let _domain = hasher.update(ENTRY_DOMAIN);
        let _name = hasher.update(name.0.as_bytes());
        let _pointer = hasher.update(&pointer.0);
        Self(*hasher.finalize().as_bytes())
    }
}

/// An entry's bytes: the name's length as four little-endian bytes, the name,
/// the recorded pointer and the entry's digest.
#[repr(transparent)]
struct Entry(Vec<u8>);

impl Entry
{
    /// The entry naming `pointer` by `name`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Long` for a name whose length four bytes cannot count;
    ///   otherwise the bytes [`decoded`] reads back as `name` naming `pointer`.
    /// - provides: the one encoding of an entry.
    /// - fails: never; a name too long to journal is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a journaled root reads back after reopening.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) == u32::try_from(name.0.len()).is_err())]
    fn new(
        name: &RootName,
        pointer: ContentPtr,
    ) -> Maybe<Self, unjournaled::Absent>
    {
        let Ok(length) = u32::try_from(name.0.len())
        else {
            return Maybe::Absent(unjournaled::Absent::Long);
        };
        let recorded = Recorded::from(pointer);
        let digest = EntryDigest::of(name, &recorded);
        let mut bytes = Vec::with_capacity(
            LENGTH_LEN
                .saturating_add(name.0.len())
                .saturating_add(POINTER_LEN)
                .saturating_add(DIGEST_LEN),
        );
        bytes.extend_from_slice(&length.to_le_bytes());
        bytes.extend_from_slice(name.0.as_bytes());
        bytes.extend_from_slice(&recorded.0);
        bytes.extend_from_slice(&digest.0);
        Maybe::Present(Self(bytes))
    }
}

/// A journal's bytes from an offset on.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Tail<'bytes>(&'bytes [u8]);

/// One entry a journal's tail opens with.
struct Entered
{
    /// The root's name.
    name: RootName,
    /// The pointer it names.
    pointer: ContentPtr,
    /// The entry's bytes, its digest included.
    length: usize,
}

/// The entry `tail` opens with.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ended` for an empty tail; the entry the tail opens with when its
///   name is UTF-8 and its digest is the one [`EntryDigest::of`] takes of its
///   name and pointer; `Torn` otherwise.
/// - provides: the one decoding of an entry.
/// - fails: never; a tail that opens with no entry is the typed absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an appended entry reads back, and a torn one ends the
///   journal.
/// - witness: `tests::store::a_root_set_reads_back_after_reopening`
/// - witness: `tests::store::a_torn_journal_entry_is_cut_by_the_next_naming_4081`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(unentered::Absent::Ended)) == tail.0.is_empty())]
fn decoded(tail: Tail<'_>) -> Maybe<Entered, unentered::Absent>
{
    if tail.0.is_empty() {
        return Maybe::Absent(unentered::Absent::Ended);
    }
    let read = || {
        let (length, rest) = tail.0.split_at_checked(LENGTH_LEN)?;
        let length = <[u8; LENGTH_LEN]>::try_from(length).ok()?;
        let length = usize::try_from(u32::from_le_bytes(length)).ok()?;
        let (name, rest) = rest.split_at_checked(length)?;
        let (pointer, rest) = rest.split_at_checked(POINTER_LEN)?;
        let (digest, _rest) = rest.split_at_checked(DIGEST_LEN)?;
        let name = core::str::from_utf8(name).ok()?;
        let name = RootName(String::from(name));
        let recorded = <[u8; POINTER_LEN]>::try_from(pointer).ok()?;
        let recorded = Recorded(recorded);
        let digest = <[u8; DIGEST_LEN]>::try_from(digest).ok()?;
        let digest = EntryDigest(digest);
        (digest == EntryDigest::of(&name, &recorded)).then(|| Entered {
            length: LENGTH_LEN
                .saturating_add(name.0.len())
                .saturating_add(POINTER_LEN)
                .saturating_add(DIGEST_LEN),
            pointer: recorded.pointer(),
            name,
        })
    };
    read().map_or(Maybe::Absent(unentered::Absent::Torn), Maybe::Present)
}
