//! The facade: one handle over a directory holding the value plane, the record
//! plane and the named roots.
//!
//! [`Store::open`] makes the directory and its two plane directories when
//! they are missing and lists what each holds. Each operation holds a batch
//! over a plane, the section of the plane that the call owns, so the puts take
//! `&self` and a store is shared between threads with no lock.
//! [`Store::commit`] commits a [`Stored`] value through the value plane under
//! [`Store::PROFILE_KAPPA`] and [`Store::PROFILE_CAP`], with the value's own
//! codec identity, and publishes the chunks it cut before it returns the root
//! pointer; [`Store::deref`] reads it back, and [`Store::closure`] reads where
//! it resides: the chunks it reaches and the bytes of their images.
//! [`Store::write_tree`] admits a record tree to the record plane and
//! publishes its nodes, and [`Store::records`] is a batch over that plane, for
//! opening a stored root. [`Store::open`] also gives the store's
//! [`Register`], the one writer of its roots, and [`Store::roots`] loads the
//! snapshot of the roots that the register last published, with no lock.

use alloc::sync::Arc;
use core::num::NonZeroU64;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use arc_swap::ArcSwap;
use gandr_core_publish::Unpublished;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_records::NodeHash;
use gandr_storage_records::RecordTree;
use gandr_storage_records::RecordTreeError;
use gandr_storage_values::BoundaryClassification;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::ContentPtr;
use gandr_storage_values::ValueClosure;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_closure;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use quenchant_shape::shape::Maybe;

use crate::plane::ChunkBatch;
use crate::plane::ChunkDirectory;
use crate::plane::Image;
use crate::plane::NodeBatch;
use crate::plane::NodeDirectory;
use crate::register::Register;
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
pub enum Hold
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
///   as `hold` says, for as long as the returned file is open. On WASI the file
///   stands unlocked, because the target has no file lock.
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
pub fn locked(
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
    // WASI 0.3 has no file lock. The host that preopens the store's
    // directory to one instance holds that exclusion itself.
    #[cfg(not(target_os = "wasi"))]
    {
        let held = match hold {
            Hold::Shared => lock.lock_shared(),
            Hold::Alone => lock.lock(),
        };
        held.map_err(|error| StoreError::io(&path, &error))?;
    }
    #[cfg(target_os = "wasi")]
    let (Hold::Shared | Hold::Alone) = hold;
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

/// A number of bytes of chunk images: what the chunks of a closure take in
/// the value plane's directory.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImageBytes(u64);

impl ImageBytes
{
    /// The length of `image`.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn of(Image(image): Image<'_>) -> Self
    {
        Self(u64::try_from(image.len()).unwrap_or(u64::MAX))
    }

    /// The bytes of `self` and `more` together, held at the width's end.
    ///
    /// # Specification
    /// trivial.
    const fn plus(
        self,
        more: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(more.0))
    }
}

impl From<ImageBytes> for u64
{
    /// The number of bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: ImageBytes) -> Self
    {
        bytes.0
    }
}

/// Where a stored value resides: the chunks a dereference of its pointer
/// loads, and the bytes of their images together.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Residence
{
    /// The chunks a dereference loads.
    closure: ValueClosure,
    /// The bytes of their images.
    bytes: ImageBytes,
}

impl Residence
{
    /// The chunks a dereference of the value loads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn closure(&self) -> &ValueClosure
    {
        &self.closure
    }

    /// The bytes of the images of those chunks together.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bytes(&self) -> ImageBytes
    {
        self.bytes
    }
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
    /// The named tree reaches a node the record plane does not hold.
    Unheld
    {
        /// The node.
        node: NodeHash,
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
            Self::Unheld { node } => write!(
                f,
                "its tree reaches the node {node}, which the store does not hold: remove it to start the roots anew"
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
    /// The register that owns the roots is gone, so a naming reaches no
    /// owner.
    Unowned,
    /// An entry of a built output, or the tree it names, is refused.
    #[cfg(unix)]
    Entry(crate::entries::EntryFault),
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
            Self::Unowned => write!(
                f,
                "the store's register is gone: keep it open while a namer names roots"
            ),
            #[cfg(unix)]
            Self::Entry(ref fault) => write!(f, "the store refuses an entry: {fault}"),
        }
    }
}

impl core::error::Error for StoreError
{
}

/// One store: the value plane, the record plane and the named roots under one
/// directory. Its puts take `&self`, so threads share one store with no lock.
/// Its [`Register`] names its roots.
#[derive(Debug)]
pub struct Store
{
    /// The directory the store is rooted at.
    root: PathBuf,
    /// The value plane.
    chunks: ChunkDirectory,
    /// The record plane, which the register shares.
    nodes: Arc<NodeDirectory>,
    /// The snapshot of the roots that the register last published.
    roots: Arc<ArcSwap<Roots>>,
}

impl Store
{
    /// The cut divisor every value the store commits is chunked under.
    pub const PROFILE_KAPPA: NonZeroU64 = NonZeroU64::MIN.saturating_add(3_u64);

    /// The most records a chunk the store commits holds before a cut.
    pub const PROFILE_CAP: NonZeroU64 = NonZeroU64::MIN.saturating_add(63_u64);

    /// Which constructors are boundaries in every value the store commits:
    /// each one, so the closure of any value walks under it whatever its
    /// codec.
    const CLASSIFICATION: BoundaryClassification = BoundaryClassification::EveryConstructor;

    /// The store rooted at `root`, made where it is missing, and its register.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success `root`, `root/chunks` and `root/nodes` stand as
    ///   directories, every object each holds is listed, and the roots are
    ///   those the roots tree and the journal over it name, read under the
    ///   roots lock shared, or none when no roots file stands. The register is
    ///   the one writer of the store's roots, and the store's readers load the
    ///   snapshot it publishes.
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
    pub fn open(root: &Path) -> Result<(Self, Register), StoreError>
    {
        let chunks = ChunkDirectory::open(root.join(CHUNKS))?;
        let nodes = Arc::new(NodeDirectory::open(root.join(NODES))?);
        let lock = locked(root, Hold::Shared)?;
        let kept = Kept::read(root, &nodes)?;
        drop(lock);
        let roots = Arc::new(ArcSwap::from_pointee(kept.roots().clone()));
        let register = Register::new(
            root.to_path_buf(),
            Arc::clone(&nodes),
            kept,
            Arc::clone(&roots),
        );
        Ok((
            Self {
                root: root.to_path_buf(),
                chunks,
                nodes,
                roots,
            },
            register,
        ))
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
        .classified(Self::CLASSIFICATION)
    }

    /// Commit `value` and publish the chunks it was cut into.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the root pointer [`cam_commit`] returns for
    ///   `value` under the store's profile and the value's codec, every chunk
    ///   it names a file of the value plane's directory, so a store opened
    ///   later derefs it to a value equal to `value`. The pointer depends on
    ///   the value and the profile alone, never on what the store held.
    /// - provides: the value plane's write path for every consumer, on any
    ///   thread.
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
    ///   pointer; sixteen threads that commit one value at once each return its
    ///   pointer, and leave one file per chunk.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::sixteen_writers_of_one_value_leave_one_object_per_digest_6899`
    #[inline]
    pub fn commit<Value>(
        &self,
        value: &Value,
    ) -> Result<ContentPtr, StoreError>
    where
        Value: Stored,
    {
        let mut batch = ChunkBatch::over(&self.chunks);
        let manifest = cam_commit(&mut batch, &Self::profile(Value::codec()), value)
            .map_err(StoreError::Value)?;
        batch.publish()?;
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
        cam_deref(&ChunkBatch::over(&self.chunks), pointer).map_err(StoreError::Value)
    }

    /// Where the value at `pointer` resides: the chunks a dereference of it
    /// loads, each verified, and the bytes of their images.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the closure [`cam_closure`] walks from `pointer`
    ///   under the classification of the store's profile, and the sum of the
    ///   lengths of those chunks' images. The store writes nothing and names no
    ///   root.
    /// - provides: the residence of a value that the store's roots name, read
    ///   with no codec, so a reader that holds only the pointer reads it.
    /// - fails: [`StoreError::Value`]: an unknown chunk, a chunk whose bytes do
    ///   not verify, and the walk's other refusals.
    /// - panics: none.
    /// - executable: none — the chunks are the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — after reopening, a value's closure is the chunks its
    ///   commit wrote and the bytes of their files, and a chunk changed on disk
    ///   is refused by its digest.
    /// - witness: `tests::store::a_committed_value_resides_in_the_chunks_its_commit_wrote_6296`
    #[inline]
    pub fn closure(
        &self,
        pointer: ContentPtr,
    ) -> Result<Residence, StoreError>
    {
        let batch = ChunkBatch::over(&self.chunks);
        let closure =
            cam_closure(&batch, pointer, Self::CLASSIFICATION).map_err(StoreError::Value)?;
        let mut bytes = ImageBytes::default();
        for &digest in closure.digests() {
            let Maybe::Present(size) = batch.size(digest)
            else {
                return Err(StoreError::Value(ValueError::UnknownChunk { digest }));
            };
            bytes = bytes.plus(size);
        }
        Ok(Residence { closure, bytes })
    }

    /// A batch over the record plane, for opening and proving against a
    /// stored tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn records(&self) -> NodeBatch<'_>
    {
        NodeBatch::over(&self.nodes)
    }

    /// The record plane, for the read of an entry's tree.
    ///
    /// # Specification
    /// trivial.
    #[cfg(unix)]
    pub(crate) fn nodes(&self) -> &NodeDirectory
    {
        &self.nodes
    }

    /// Admit `tree` to the record plane and publish its nodes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every node of `tree` is a file of the record
    ///   plane's directory, so a store opened later opens the tree's root.
    /// - provides: the record plane's write path for every consumer, on any
    ///   thread.
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
    ///   after reopening, and from the store that wrote it.
    /// - witness: `tests::store::a_written_tree_opens_from_the_record_plane_after_reopening`
    /// - witness: `tests::store::a_written_tree_opens_from_the_store_that_wrote_it_6899`
    #[inline]
    pub fn write_tree(
        &self,
        tree: &RecordTree,
    ) -> Result<(), StoreError>
    {
        let mut batch = NodeBatch::over(&self.nodes);
        tree.write_to(&mut batch).map_err(StoreError::Record)?;
        batch.publish()
    }

    /// The named roots, as the register last published them. The snapshot
    /// stays as it was loaded while the register publishes others.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn roots(&self) -> Arc<Roots>
    {
        self.roots.load_full()
    }
}
