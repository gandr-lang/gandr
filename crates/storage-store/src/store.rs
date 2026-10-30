//! The facade: one handle over a directory holding the value plane, the record
//! plane and the named roots.
//!
//! [`Store::open`] makes the directory and its two plane directories when
//! they are missing and lists what each holds. [`Store::commit`] commits a
//! [`Stored`] value through the value plane under [`Store::PROFILE_KAPPA`]
//! and [`Store::PROFILE_CAP`], with the value's own codec identity, and
//! writes the chunks it cut before it returns the root pointer;
//! [`Store::deref`] reads it back. [`Store::write_tree`] admits a record tree
//! to the record plane and writes its nodes, and [`Store::records`] is that
//! plane, for opening a stored root. [`Store::set_root`] names a pointer under
//! the roots lock: it reads what another store over the same directory named
//! since, then appends its own naming to the roots journal, so a naming costs
//! amortised constant time and loses no other store's root.

use core::num::NonZeroU64;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_publish::Unpublished;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;

use crate::plane::ChunkDirectory;
use crate::plane::NodeDirectory;
use crate::roots::Kept;
use crate::roots::RootName;
use crate::roots::Roots;

/// The directory of a store's value plane.
const CHUNKS: &str = "chunks";

/// The directory of a store's record plane.
const NODES: &str = "nodes";

/// The file a change to a store's roots holds locked.
const ROOTS_LOCK: &str = "roots.lock";

/// How a store holds its roots lock.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Hold
{
    /// Beside other readers, to read the roots.
    Shared,
    /// Alone, to change them.
    Alone,
}

/// The roots lock of the store at `root`, held as `hold` says until the file
/// returned closes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the lock file stands at `root`, held shared or alone
///   as `hold` says, for as long as the returned file is open.
/// - provides: the lock every reading and naming of the roots holds.
/// - fails: [`StoreError::Io`] when the lock file cannot be opened or locked.
/// - panics: none.
/// - executable: none — the lock is the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — two stores over one directory keep each other's roots.
/// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
fn locked(
    root: &Path,
    hold: Hold,
) -> Result<std::fs::File, StoreError>
{
    let path = root.join(ROOTS_LOCK);
    let lock = std::fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(&path)
        .map_err(|error| StoreError::io(&path, &error))?;
    let held = match hold {
        Hold::Shared => lock.lock_shared(),
        Hold::Alone => lock.lock(),
    };
    held.map_err(|error| StoreError::io(&path, &error))?;
    Ok(lock)
}

/// A value the store commits: a canonical value that names its own codec.
///
/// The codec identity enters the profile the value is committed under, so two
/// codecs that emit alike never share a value by accident.
pub trait Stored: CanonicalValue
{
    /// The codec the value's tokens are written in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same identity on every call, and a new identity whenever
    ///   the value's token encoding changes.
    /// - provides: the codec field of the profile [`Store::commit`] uses.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — a required declaration has no body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs back after reopening.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    fn codec() -> CodecIdentity;
}

/// Why a store's roots file names no roots tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RootsFault
{
    /// The file is not one root node identity in lowercase hexadecimal.
    Unspelled,
    /// The records the named node and its leaves hold build another tree.
    Unbuilt,
    /// A record's key is not a name.
    Unnamed,
    /// A root's record holds no pointer.
    Unpointed
    {
        /// The root.
        name: RootName,
    },
}

impl core::fmt::Display for RootsFault
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Unspelled => {
                f.write_str("it names no root node: remove it to start the roots anew")
            },
            Self::Unbuilt => f.write_str(
                "the records its node holds build another tree: remove it to start the roots anew",
            ),
            Self::Unnamed => {
                f.write_str("a record's key is not a name: remove it to start the roots anew")
            },
            Self::Unpointed { ref name } => write!(
                f,
                "the root `{name}` holds no pointer: remove it to start the roots anew"
            ),
        }
    }
}

/// Every way a store refuses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StoreError
{
    /// A file or directory of the store cannot be made, read or written.
    Io
    {
        /// The file or directory.
        path: PathBuf,
        /// What the file system said.
        kind: io::ErrorKind,
    },
    /// The value plane refused: a value it cannot commit or read back, or a
    /// chunk whose bytes do not verify.
    Value(ValueError),
    /// The record plane refused: a tree it cannot admit, or a node whose bytes
    /// do not verify.
    Record(RecordTreeError),
    /// The roots file names no roots tree.
    Roots
    {
        /// The roots file.
        path: PathBuf,
        /// What it names instead.
        fault: RootsFault,
    },
}

impl StoreError
{
    /// The fault a file system's `error` at `path` is.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn io(
        path: &Path,
        error: &io::Error,
    ) -> Self
    {
        Self::Io {
            path: path.to_path_buf(),
            kind: error.kind(),
        }
    }
}

impl From<Unpublished> for StoreError
{
    /// A file the store could not publish: the file and what the file system
    /// said.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: Unpublished) -> Self
    {
        Self::Io {
            path: fault.path,
            kind: fault.kind,
        }
    }
}

impl core::fmt::Display for StoreError
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Io { ref path, kind } => write!(
                f,
                "the store cannot use `{}`: {kind}: make it readable and writable",
                path.display()
            ),
            Self::Value(ref fault) => write!(f, "the store's value plane refuses: {fault}"),
            Self::Record(ref fault) => write!(f, "the store's record plane refuses: {fault}"),
            Self::Roots {
                ref path,
                ref fault,
            } => write!(f, "the store's roots file `{}`: {fault}", path.display()),
        }
    }
}

impl core::error::Error for StoreError
{
}

/// One store: the value plane, the record plane and the named roots under one
/// directory.
#[derive(Debug)]
pub struct Store
{
    /// The directory the store is rooted at.
    root: PathBuf,
    /// The value plane.
    chunks: ChunkDirectory,
    /// The record plane.
    nodes: NodeDirectory,
    /// The named roots, as the store last read or wrote them, and where its
    /// reading of them stands.
    roots: Kept,
}

impl Store
{
    /// The cut divisor every value the store commits is chunked under.
    pub const PROFILE_KAPPA: NonZeroU64 = NonZeroU64::MIN.saturating_add(3_u64);

    /// The most records a chunk the store commits holds before a cut.
    pub const PROFILE_CAP: NonZeroU64 = NonZeroU64::MIN.saturating_add(63_u64);

    /// The store rooted at `root`, made where it is missing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success `root`, `root/chunks` and `root/nodes` stand as
    ///   directories, every object each holds is listed, and the roots are
    ///   those the roots tree and the journal over it name, read under the
    ///   roots lock shared, or none when no roots file stands.
    /// - provides: the one way a consumer reaches the storage tier on disk.
    /// - fails: [`StoreError::Io`] when a directory cannot be made or listed,
    ///   or the lock, the roots file or the journal cannot be used, and
    ///   [`StoreError::Record`] and [`StoreError::Roots`] when the roots do not
    ///   read back.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing root is made, and a value and a root each
    ///   read back after reopening.
    /// - witness: `tests::store::a_missing_root_directory_is_made_on_opening`
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    #[inline]
    pub fn open(root: &Path) -> Result<Self, StoreError>
    {
        let chunks = ChunkDirectory::open(root.join(CHUNKS))?;
        let mut nodes = NodeDirectory::open(root.join(NODES))?;
        let lock = locked(root, Hold::Shared)?;
        let roots = Kept::read(root, &mut nodes)?;
        drop(lock);
        Ok(Self {
            root: root.to_path_buf(),
            chunks,
            nodes,
            roots,
        })
    }

    /// The directory the store is rooted at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> &Path
    {
        &self.root
    }

    /// The profile a value of codec `codec` is committed under.
    ///
    /// # Specification
    /// trivial.
    fn profile(codec: CodecIdentity) -> ValueProfile
    {
        ValueProfile::new(
            TypedChunkerParams::new(
                Kappa::from(Self::PROFILE_KAPPA),
                TokenCap::from(Self::PROFILE_CAP),
            ),
            codec,
            ChildIndexBase::Absolute,
        )
    }

    /// Commit `value` and write the chunks it was cut into.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the root pointer [`cam_commit`] returns for
    ///   `value` under the store's profile and the value's codec, every chunk
    ///   it names written to the value plane's directory, so a store opened
    ///   later derefs it to a value equal to `value`. The pointer depends on
    ///   the value and the profile alone, never on what the store held.
    /// - provides: the value plane's write path for every consumer.
    /// - fails: [`StoreError::Value`] for a value the plane cannot commit,
    ///   [`StoreError::Io`] for a chunk that cannot be written.
    /// - panics: none.
    /// - executable: none — the chunks are the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs back equal after reopening,
    ///   and committing it again into a store that holds it returns the same
    ///   pointer.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    #[inline]
    pub fn commit<Value>(
        &mut self,
        value: &Value,
    ) -> Result<ContentPtr, StoreError>
    where
        Value: Stored,
    {
        let manifest = cam_commit(&mut self.chunks, &Self::profile(Value::codec()), value)
            .map_err(StoreError::Value)?;
        self.chunks.write()?;
        Ok(manifest.root())
    }

    /// The value `pointer` addresses.
    ///
    /// # Specification
    /// - requires: `pointer` was committed as a `Value`.
    /// - ensures: on success the value [`cam_deref`] decodes at `pointer`.
    /// - provides: the value plane's read path for every consumer.
    /// - fails: [`StoreError::Value`]: an unknown chunk, a chunk whose bytes do
    ///   not verify, and the codec's refusals.
    /// - panics: none.
    /// - executable: none — as [`cam_deref`].
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs back equal, and a chunk
    ///   changed on disk is refused by its digest.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    #[inline]
    pub fn deref<Value>(
        &self,
        pointer: ContentPtr,
    ) -> Result<Value, StoreError>
    where
        Value: Stored,
    {
        cam_deref(&self.chunks, pointer).map_err(StoreError::Value)
    }

    /// The record plane, for opening and proving against a stored tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn records(&self) -> &NodeDirectory
    {
        &self.nodes
    }

    /// Admit `tree` to the record plane and write its nodes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every node of `tree` is written to the record
    ///   plane's directory, so a store opened later opens the tree's root.
    /// - provides: the record plane's write path for every consumer.
    /// - fails: [`StoreError::Record`] for a node the plane refuses,
    ///   [`StoreError::Io`] for a node that cannot be written.
    /// - panics: none.
    /// - executable: none — the nodes are the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written tree's root opens from the record plane
    ///   after reopening.
    /// - witness: `tests::store::a_written_tree_opens_from_the_record_plane_after_reopening`
    #[inline]
    pub fn write_tree(
        &mut self,
        tree: &RecordTree,
    ) -> Result<(), StoreError>
    {
        tree.write_to(&mut self.nodes).map_err(StoreError::Record)?;
        self.nodes.write()
    }

    /// The named roots, as the store last read or wrote them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn roots(&self) -> &Roots
    {
        self.roots.roots()
    }

    /// Name `pointer` by `name`, whatever `name` named before.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the roots read again under the roots lock, with
    ///   `name` naming `pointer`, stand on disk and are the store's roots, so
    ///   every other root a store over the same directory set stands too.
    /// - provides: the one way a root changes.
    /// - fails: [`StoreError::Io`] when the lock or a file cannot be used, and
    ///   the faults of reading and writing the roots.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    /// - intension: the naming reads the entries other stores journaled since
    ///   this store last read, and appends one; it builds the whole roots tree
    ///   only after as many namings as the tree holds roots, so it costs
    ///   amortised constant time.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root set reads back after reopening, a second
    ///   setting of one name replaces it, two stores over one directory keep
    ///   each other's roots, and namings one at a time leave far fewer nodes
    ///   than namings.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    /// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
    /// - witness: `tests::store::naming_roots_one_at_a_time_writes_no_tree_per_naming_4081`
    #[inline]
    pub fn set_root(
        &mut self,
        name: RootName,
        pointer: ContentPtr,
    ) -> Result<(), StoreError>
    {
        let lock = locked(&self.root, Hold::Alone)?;
        self.roots
            .name(&self.root, &mut self.nodes, name, pointer)?;
        drop(lock);
        Ok(())
    }
}
