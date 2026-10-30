//! The two planes on disk: a directory of objects each, one file per object,
//! named by its identity in lowercase hexadecimal.
//!
//! A plane is listed when it opens, and each object listed is read the first
//! time it is loaded and kept for the store's life, so a load borrows from the
//! store as both plane traits ask. An insertion is taken in memory and written
//! only when the facade's operation that made it ends: neither plane trait can
//! name a file system's failure, and the facade can. A write publishes each
//! object through `gandr_core_publish`: a temporary file in the plane's
//! directory, renamed onto its name, so a reader never meets half an object,
//! and two writers of one object write the same bytes. Every load verifies
//! what it read, so bytes changed on disk are refused by the plane's own
//! fault. A refused object stands for no name, so the next insertion of that
//! name takes its bytes and writes them over the file.
//!
//! # Boundaries
//!
//! An object another process writes after this store opened is not listed and
//! loads as unknown; the roots are listed again before each change, under the
//! roots lock.
//!
//! # References
//!
//! - `vault:01a178aa-4bbc-7842-9a60-d11551c41e06` — background: § The real leak
//!   was in the filesystem — an object's temporary has one owner, the guard of
//!   the writer it publishes through.

use alloc::collections::BTreeMap;
use core::cell::Cell;
use core::cell::OnceCell;
use std::io;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_publish::Contents;
use gandr_core_publish::publish;
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

use crate::store::StoreError;

/// The identity a plane names its objects by: 32 bytes, spelled as 64
/// lowercase hexadecimal digits.
pub trait ObjectName: Copy + Ord + core::fmt::Display + From<[u8; 32]>
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
            /// The plane lists no object of that identity.
            Unlisted,
            /// The plane lists it, and its file cannot be read.
            Unreadable,
            /// The text spells no identity: it is not exactly 64 lowercase
            /// hexadecimal digits.
            Unspelled,
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

/// Whether a load refused a filed object's bytes as not the object its name
/// names.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Standing
{
    /// No load refused the bytes.
    #[default]
    Unrefused,
    /// A load refused the bytes, so the next insertion of the name writes the
    /// object afresh.
    Refused,
}

/// One object of a plane.
#[derive(Debug)]
enum Object
{
    /// Named by a file of the directory, read on its first load.
    Filed
    {
        /// The file's bytes as first read.
        read: OnceCell<Result<Box<[u8]>, io::ErrorKind>>,
        /// Whether a load refused them.
        standing: Cell<Standing>,
    },
    /// Taken by an insertion and not written yet.
    Pending(Box<[u8]>),
}

/// A directory of objects, each a file named by its identity.
#[derive(Debug)]
pub struct Directory<Name>
{
    /// The directory.
    path: PathBuf,
    /// Every object listed or taken, by identity.
    objects: BTreeMap<Name, Object>,
    /// The identities taken and not written, in the order they were taken.
    pending: Vec<Name>,
}

impl<Name> Directory<Name>
where
    Name: ObjectName,
{
    /// The directory at `path`, created when missing, and every object it
    /// holds listed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a directory at `path`; each file named by 64 lowercase
    ///   hexadecimal digits listed as the object of that identity, every other
    ///   file ignored; nothing pending.
    /// - provides: a plane's backing as the store opens.
    /// - fails: [`StoreError::Io`] when the directory cannot be made or listed.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing root is created, and a committed value
    ///   loads after reopening.
    /// - witness: `tests::store::a_missing_root_directory_is_made_on_opening`
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    pub fn open(path: PathBuf) -> Result<Self, StoreError>
    {
        std::fs::create_dir_all(&path).map_err(|error| StoreError::io(&path, &error))?;
        let mut directory = Self {
            path,
            objects: BTreeMap::new(),
            pending: Vec::new(),
        };
        directory.list()?;
        Ok(directory)
    }

    /// List each object the directory holds that this plane does not, as
    /// [`Directory::open`] reads a name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every object the plane held is held as it was, and each file
    ///   of the directory named by an identity it did not hold is listed.
    /// - provides: the reading the roots take again under their lock.
    /// - fails: [`StoreError::Io`] when the directory cannot be listed.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two stores over one directory each set a root, and
    ///   both stand after reopening.
    /// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
    pub fn list(&mut self) -> Result<(), StoreError>
    {
        let entries =
            std::fs::read_dir(&self.path).map_err(|error| StoreError::io(&self.path, &error))?;
        for entry in entries {
            let entry = entry.map_err(|error| StoreError::io(&self.path, &error))?;
            let Maybe::Present(name) = named::<Name>(&entry.file_name())
            else {
                continue;
            };
            let _held = self.objects.entry(name).or_insert_with(|| Object::Filed {
                read: OnceCell::new(),
                standing: Cell::new(Standing::Unrefused),
            });
        }
        Ok(())
    }

    /// The bytes held under `name`: taken, or read from its file the first
    /// time they are asked for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the bytes taken under `name`, else its file's bytes as first
    ///   read; `Unlisted` for a name neither taken nor listed, `Unreadable` for
    ///   a file that could not be read when first asked for.
    /// - provides: the one read both planes verify.
    /// - fails: never; a missing object is the typed absence.
    /// - panics: none.
    /// - executable: none — the bytes are the file system's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, and bytes
    ///   changed on disk are refused.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_chunk_changed_on_disk_is_refused_by_its_digest`
    pub fn bytes(
        &self,
        name: Name,
    ) -> Maybe<Image<'_>, unheld::Absent>
    {
        match self.objects.get(&name) {
            None => Maybe::Absent(unheld::Absent::Unlisted),
            Some(&Object::Pending(ref bytes)) => Maybe::Present(Image(bytes)),
            Some(&Object::Filed { ref read, .. }) => read
                .get_or_init(|| {
                    std::fs::read(self.path.join(name.to_string()))
                        .map(Vec::into_boxed_slice)
                        .map_err(|error| error.kind())
                })
                .as_ref()
                .map_or(Maybe::Absent(unheld::Absent::Unreadable), |bytes| {
                    Maybe::Present(Image(bytes))
                }),
        }
    }

    /// Mark the filed object under `name` refused, so the next
    /// [`Directory::take`] of `name` writes it afresh.
    ///
    /// # Specification
    /// - requires: a load refused the bytes [`Directory::bytes`] gave for
    ///   `name` as not the object `name` names.
    /// - ensures: a filed object under `name` stands refused; a pending one, or
    ///   none, is as it was.
    /// - provides: the refusal a later insertion reads.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the standing is a cell the plane's insertion reads.
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
        if let Some(&Object::Filed { ref standing, .. }) = self.objects.get(&name) {
            standing.set(Standing::Refused);
        }
    }

    /// Take `bytes` under `name`, to be written by the next
    /// [`Directory::write`], unless the plane already holds `name` unrefused.
    ///
    /// # Specification
    /// - requires: `bytes` are verified as the object `name` names.
    /// - ensures: a name the plane held unrefused keeps what it held; another,
    ///   or one a load refused, is held as `bytes` and pending.
    /// - provides: the insertion both plane traits make.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs before and after reopening,
    ///   and a refused chunk is written afresh by the next commit.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    /// - witness: `tests::store::a_refused_chunk_is_written_afresh_by_the_next_commit_4074`
    #[spec(ensures: self.objects.contains_key(&name))]
    fn take(
        &mut self,
        name: Name,
        bytes: Image<'_>,
    )
    {
        match self.objects.get(&name) {
            Some(&Object::Filed { ref standing, .. }) if standing.get() == Standing::Refused => {},
            Some(_) => return,
            None => {},
        }
        let _taken = self
            .objects
            .insert(name, Object::Pending(Box::from(bytes.0)));
        self.pending.push(name);
    }

    /// Write each pending object to its file.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success each object taken since the last write is a file
    ///   of the directory under its name and nothing is pending; on failure the
    ///   objects not written stay pending.
    /// - provides: the end of every facade operation that inserts.
    /// - fails: [`StoreError::Io`] for the first file that cannot be written.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// [`StoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed value derefs after reopening, which reads
    ///   only what was written.
    /// - witness: `tests::store::a_committed_value_derefs_back_after_reopening`
    pub fn write(&mut self) -> Result<(), StoreError>
    {
        let pending = core::mem::take(&mut self.pending);
        for (at, name) in pending.iter().enumerate() {
            if let Some(object) = self.objects.get_mut(name)
                && let Object::Pending(ref mut bytes) = *object
            {
                if let Err(fault) = publish(&self.path, name, Contents(bytes)) {
                    self.pending = pending.get(at ..).map_or_else(Vec::new, <[Name]>::to_vec);
                    return Err(StoreError::from(fault));
                }
                let written = core::mem::take(bytes);
                *object = Object::Filed {
                    read: OnceCell::from(Ok(written)),
                    standing: Cell::new(Standing::Unrefused),
                };
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

    /// Write each pending chunk, as [`Directory::write`] does.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn write(&mut self) -> Result<(), StoreError>
    {
        self.0.write()
    }
}

impl ChunkStore for ChunkDirectory
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
    /// - executable: none — the held bytes are the directory's.
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
    /// - ensures: as [`ChunkStore::load`]; an image the directory does not
    ///   list, or whose file cannot be read, is unknown.
    /// - provides: the value plane's read half on disk.
    /// - fails: [`ValueError::UnknownChunk`], and [`verify_chunk_image`]'s
    ///   refusals for bytes changed on disk, which mark the chunk refused so
    ///   its next insertion writes it afresh.
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
        let Maybe::Present(Image(bytes)) = self.0.bytes(digest)
        else {
            return Err(ValueError::UnknownChunk { digest });
        };
        verify_chunk_image(StoredChunkRef::new(digest, ChunkImage::from(bytes)))
            .inspect_err(|_refusal| self.0.refuse(digest))
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

    /// List what the directory holds since, as [`Directory::list`] does.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn list(&mut self) -> Result<(), StoreError>
    {
        self.0.list()
    }

    /// Write each pending node, as [`Directory::write`] does.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn write(&mut self) -> Result<(), StoreError>
    {
        self.0.write()
    }
}

impl BlockStore for NodeDirectory
{
    /// Admits verified node bytes, to be written when the operation ends.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's own precondition.
    /// - ensures: on success the node's identity is held, by the bytes held
    ///   before or by the node's, which were verified first; a refused node
    ///   leaves the plane as it was.
    /// - provides: the record plane's admission on disk.
    /// - fails: propagates [`verify_stored_node`]'s refusal unchanged.
    /// - panics: none.
    /// - executable: none — the held bytes are the directory's.
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
    /// - ensures: as [`BlockStore::load`]; a node the directory does not list,
    ///   or whose file cannot be read, is unknown.
    /// - provides: the record plane's verified load on disk.
    /// - fails: [`RecordTreeError::UnknownNode`], and [`verify_stored_node`]'s
    ///   refusals for bytes changed on disk, which mark the node refused so its
    ///   next insertion writes it afresh.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written tree opens after reopening, and a node
    ///   changed on disk is refused.
    /// - witness: `tests::store::a_written_tree_opens_from_the_record_plane_after_reopening`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|node| node.identity() == hash))]
    fn load(
        &self,
        hash: NodeHash,
    ) -> Result<StoredNode<'_>, RecordTreeError>
    {
        let Maybe::Present(Image(bytes)) = self.0.bytes(hash)
        else {
            return Err(RecordTreeError::UnknownNode { hash });
        };
        let node = StoredNode::new(hash, EncodedNode::from(bytes));
        verify_stored_node(node).inspect_err(|_refusal| self.0.refuse(hash))?;
        Ok(node)
    }
}
