//! Named roots: a small record tree on the record plane, each record a name
//! and the content pointer it names.
//!
//! A root names where something stands in the store by a name of the
//! consumer's own, as `lock/<package address>` or `verdict/<key>`. The tree's
//! records are each name's bytes keyed to the pointer's digest and then its
//! offset as four little-endian bytes; the file `roots` at the store's root
//! holds the tree's root node identity in lowercase hexadecimal. Reading the
//! roots loads that node and its leaves from the record plane, which verifies
//! each, then builds the tree again from their records and refuses a tree
//! whose root node is not the one the file names.
//!
//! # Boundaries
//!
//! A root is local to the store it is set in: a content pointer crosses hosts,
//! and a name is what one host's consumer chose. A root states where a value
//! stands, never that it is valid.

use alloc::collections::BTreeMap;
use std::io;
use std::path::Path;

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

/// The bytes a root's pointer is recorded as: its digest, then its offset.
const POINTER_LEN: usize = 36_usize;

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

    /// The roots with `name` naming `pointer`, whatever it named before.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn with(
        mut self,
        name: RootName,
        pointer: ContentPtr,
    ) -> Self
    {
        let _named = self.0.insert(name, pointer);
        self
    }

    /// The roots the store at `directory` names, read from `nodes`.
    ///
    /// # Specification
    /// - requires: `nodes` is the record plane of the store at `directory`.
    /// - ensures: none when no [`ROOTS`] file stands; otherwise the records of
    ///   the tree whose root node the file names, each a name and a pointer,
    ///   when that node and its leaves load verified from `nodes` and build
    ///   again to the same root node.
    /// - provides: the roots a store holds as it opens and before each change.
    /// - fails: [`StoreError::Io`] for a file that cannot be read,
    ///   [`StoreError::Record`] for a node the plane refuses, and
    ///   [`StoreError::Roots`] for anything else that is not a roots tree.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a root set reads back after reopening, a second
    ///   store's root stands beside the first's, and a file spelling no node is
    ///   refused by name.
    /// - witness: `tests::store::a_root_set_reads_back_after_reopening`
    /// - witness: `tests::store::two_stores_over_one_directory_keep_each_other_s_roots`
    /// - witness: `tests::store::a_roots_file_naming_no_node_is_refused_on_opening`
    pub(crate) fn read(
        directory: &Path,
        nodes: &NodeDirectory,
    ) -> Result<Self, StoreError>
    {
        let path = directory.join(ROOTS);
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(ref error) if error.kind() == io::ErrorKind::NotFound => {
                return Ok(Self::default());
            },
            Err(ref error) => return Err(StoreError::io(&path, error)),
        };
        let unrooted = |fault: RootsFault| StoreError::Roots {
            path: path.clone(),
            fault,
        };
        let Some(Maybe::Present(hash)) = text
            .strip_suffix('\n')
            .map(|spelled| hexadecimal::<NodeHash>(FileName(spelled)))
        else {
            return Err(unrooted(RootsFault::Unspelled));
        };
        let records = leaves(nodes, hash)?;
        let refs: Vec<RecordRef<'_>> = records.iter().map(Record::as_record_ref).collect();
        let tree = RecordTree::build(&refs, TreeParams::current()).map_err(StoreError::Record)?;
        if tree.root_node_hash() != hash {
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
    ///   plane's directory and the file names its root node, so [`Roots::read`]
    ///   reads these roots back.
    /// - provides: the write every root change ends with.
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
    pub(crate) fn write(
        &self,
        directory: &Path,
        nodes: &mut NodeDirectory,
    ) -> Result<(), StoreError>
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
        .map_err(StoreError::from)
    }
}

/// The records of the tree whose root node is `hash`: its own when it is a
/// leaf, else each child leaf's in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the records of the root node, or of each leaf it
///   names, each node verified by `nodes` on its load.
/// - provides: the walk [`Roots::read`] builds the tree again from.
/// - fails: [`StoreError::Record`] for a node that does not load or decode, or
///   an internal node naming a child that is not a leaf.
/// - panics: none.
/// - executable: none — the nodes are the file system's.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — a root set reads back after reopening.
/// - witness: `tests::store::a_root_set_reads_back_after_reopening`
fn leaves(
    nodes: &NodeDirectory,
    hash: NodeHash,
) -> Result<Vec<Record>, StoreError>
{
    let mut work = DecodeWork::new();
    let root = nodes.load(hash).map_err(StoreError::Record)?;
    match decode_node(root.bytes(), &mut work).map_err(StoreError::Record)? {
        DecodedNode::Leaf(leaf) => Ok(leaf.records().to_vec()),
        DecodedNode::Internal(internal) => {
            let mut records = Vec::new();
            for child in internal.children() {
                let node = nodes.load(child.identity()).map_err(StoreError::Record)?;
                let decoded = decode_node(node.bytes(), &mut work).map_err(StoreError::Record)?;
                let leaf = decoded.as_leaf().map_err(StoreError::Record)?;
                records.extend_from_slice(leaf.records());
            }
            Ok(records)
        },
    }
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
    let value = record.value();
    let read = || {
        let (digest, offset) = value.as_ref().split_at_checked(32)?;
        let digest: [u8; 32] = digest.try_into().ok()?;
        let offset: [u8; 4] = offset.try_into().ok()?;
        Some(ContentPtr::new(
            ChunkDigest::from(digest),
            TokenOffset::from(u32::from_le_bytes(offset)),
        ))
    };
    read().ok_or_else(|| RootsFault::Unpointed { name: name.clone() })
}
