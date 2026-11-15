//! A built output as a tree of entries in the store: a directory, a
//! file or a symbolic link, each with an address that its content alone
//! decides.
//!
//! A directory is one record tree keyed by entry name, each name's bytes in
//! the file system's order. A record's value is the child's [`Entry`] in its
//! encoding. A file's bytes are a blob: the byte profile of
//! `gandr-storage-chunker` cuts them where the content says
//! ([`ByteChunkerParams::blob`]), the value plane keeps each piece as one
//! value, and the blob is a record tree keyed by the piece's index, each
//! record the piece's pointer. A tree with no record is not written: its
//! reference holds a zero count. The read cuts a file one buffer at a time
//! ([`ByteScanner`]) and commits each piece at its cut, so it holds one buffer
//! and one piece, never the file.
//!
//! [`Store::read_in`] reads a directory, a file or a symbolic link into the
//! store and gives its entry. [`Store::write_out`] writes an entry out into a
//! path that does not stand yet. The planes check each node and each piece
//! against its digest as it loads, and the write checks each reference against
//! the manifest it seals and each file's bytes against its size.
//!
//! # Boundaries
//!
//! A file keeps its bytes and its executable bit, and no other mode. A
//! directory keeps its entries and no mode. An entry's address states which
//! content it holds, never that the content is a valid build output.
//!
//! # References
//!
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — exemplar: § the storage
//!   tier is the store — a directory as one record tree keyed by name, the
//!   three entry kinds, the blob cut, and an output as a record.

use alloc::boxed::Box;
use alloc::vec::Vec;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::fs;
use std::io::Read as _;
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::fs::FileTypeExt as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_storage_chunker::ByteChunkerParams;
use gandr_storage_chunker::ByteScanner;
use gandr_storage_chunker::CanonicalBytes;
use gandr_storage_records::NodeHash;
use gandr_storage_records::Record;
use gandr_storage_records::RecordCount;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::StoredRoot;
use gandr_storage_records::TreeParams;
use gandr_storage_records::TreeRoot;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;

use crate::roots::Recorded;
use crate::roots::leaves;
use crate::store::Store;
use crate::store::StoreError;
use crate::store::Stored;

/// The tag an entry's encoding opens with for a directory.
const DIRECTORY: u8 = 0_u8;

/// The tag an entry's encoding opens with for a file.
const FILE: u8 = 1_u8;

/// The tag an entry's encoding opens with for a symbolic link.
const SYMLINK: u8 = 2_u8;

/// The bytes of a tree's reference: its root node, then its record count.
const REFERENCE_LEN: usize = 40_usize;

/// The domain an entry's address is taken in, so it meets no other digest.
const ADDRESS_DOMAIN: &[u8] = b"gandr storage-store entry address\0";

/// The mode a file the write makes executable takes.
const EXECUTABLE_MODE: u32 = 0o755_u32;

/// The mode every other file the write makes takes.
const PLAIN_MODE: u32 = 0o644_u32;

/// The bytes a read of a file takes from the file system at once: one buffer
/// for the whole tree, so a read holds it and one piece, never a file.
const READ_BUFFER: usize = 0x0010_0000_usize;

/// The one buffer that a read of a tree takes each file's bytes into.
#[repr(transparent)]
struct ReadBuffer(Vec<u8>);

impl ReadBuffer
{
    /// A buffer of [`READ_BUFFER`] bytes.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        Self(vec![0_u8; READ_BUFFER])
    }
}

/// A file read into the store: its blob and the bytes it holds.
struct Blob
{
    /// The record tree of the file's pieces.
    tree: TreeRef,
    /// The bytes of the file.
    size: u64,
}

/// Why an entry, or the tree it names, is refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EntryFault
{
    /// An entry's bytes are not an encoding of an entry.
    Unencoded,
    /// A directory holds a name that is empty, `.`, `..` or holds a `/` or a
    /// zero byte, so a write would leave the directory.
    Unsafe
    {
        /// The name's bytes.
        name: Box<[u8]>,
    },
    /// A file's pieces hold another count of bytes than its entry.
    Resized
    {
        /// The bytes the entry states.
        stated: u64,
        /// The bytes the pieces hold.
        held: u64,
    },
    /// A path names a kind the store does not keep: a device, a socket or a
    /// pipe.
    Unkept,
    /// The byte profile refused a file's bytes.
    Uncut,
}

impl core::fmt::Display for EntryFault
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
            Self::Unencoded => f.write_str("an entry's bytes encode no entry"),
            Self::Unsafe { ref name } => write!(
                f,
                "a directory holds the name `{}`, which a write cannot make inside it",
                name.escape_ascii()
            ),
            Self::Resized { stated, held } => write!(
                f,
                "a file's entry states {stated} bytes and its pieces hold {held}"
            ),
            Self::Unkept => f.write_str(
                "the path is a device, a socket or a pipe, which the store keeps no form of",
            ),
            Self::Uncut => f.write_str("the byte profile refuses the file's bytes"),
        }
    }
}

/// A record tree as an entry names it: its root node and its record count.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TreeRef
{
    /// The tree's root node.
    root_node: NodeHash,
    /// The records the tree holds; zero for a tree that is not written.
    records: RecordCount,
}

impl TreeRef
{
    /// The reference of a tree that holds no record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn empty() -> Self
    {
        Self {
            root_node: NodeHash::from([0_u8; 32]),
            records: RecordCount(0_u64),
        }
    }

    /// The reference of `tree`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(tree: &RecordTree) -> Self
    {
        Self {
            root_node: tree.root_node_hash(),
            records: tree.root().record_count(),
        }
    }

    /// The records the tree holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn records(&self) -> RecordCount
    {
        self.records
    }

    /// The tree's root node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root_node(&self) -> NodeHash
    {
        self.root_node
    }
}

impl From<TreeRef> for [u8; REFERENCE_LEN]
{
    /// The reference as its 40 bytes: the root node, then the count as eight
    /// little-endian bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tree: TreeRef) -> Self
    {
        let mut bytes = [0_u8; REFERENCE_LEN];
        let (node, count) = bytes.split_at_mut(32_usize);
        node.copy_from_slice(tree.root_node.as_ref());
        count.copy_from_slice(&u64::from(tree.records).to_le_bytes());
        bytes
    }
}

impl TryFrom<&[u8]> for TreeRef
{
    type Error = StoreError;

    /// The reference its 40 bytes spell, refused for another count of bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(bytes: &[u8]) -> Result<Self, StoreError>
    {
        let (node, count) = bytes.split_at_checked(32_usize).ok_or_else(unencoded)?;
        let node = <[u8; 32]>::try_from(node).map_err(|_short| unencoded())?;
        let count = <[u8; 8]>::try_from(count).map_err(|_short| unencoded())?;
        Ok(Self {
            root_node: NodeHash::from(node),
            records: RecordCount(u64::from_le_bytes(count)),
        })
    }
}

/// An entry's address: the digest of its encoding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EntryAddress([u8; 32]);

impl From<[u8; 32]> for EntryAddress
{
    /// The address these 32 bytes spell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; 32]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for EntryAddress
{
    /// The address's 32 bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// An entry in its encoding, as a directory's record holds it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct EntryEncoding(Vec<u8>);

impl AsRef<[u8]> for EntryEncoding
{
    /// The encoding's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// Bytes that [`Entry::decode`] reads as an entry's encoding.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EncodedEntry<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for EncodedEntry<'bytes>
{
    /// Reads `bytes` as an entry's encoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        Self(bytes)
    }
}

impl<'bytes> From<&'bytes EntryEncoding> for EncodedEntry<'bytes>
{
    /// Reads an encoding back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(encoding: &'bytes EntryEncoding) -> Self
    {
        Self(&encoding.0)
    }
}

/// One entry of a built output: a directory, a file or a symbolic link.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Entry
{
    /// A directory: the tree of its entries, and the bytes its files hold in
    /// all.
    Directory
    {
        /// The tree of its entries, keyed by name.
        tree: TreeRef,
        /// The bytes its files hold in all, at every depth.
        size: u64,
    },
    /// A file: the tree of its pieces, its size and its executable bit.
    File
    {
        /// The tree of its pieces' pointers, keyed by index.
        blob: TreeRef,
        /// The bytes it holds.
        size: u64,
        /// Whether it runs.
        executable: bool,
    },
    /// A symbolic link: the bytes of its target.
    Symlink
    {
        /// The target's bytes, as the link holds them.
        target: Box<[u8]>,
    },
}

impl Entry
{
    /// The entry as the bytes a directory's record holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one tag byte, then for a directory its tree's reference and
    ///   its size, for a file its executable bit, its size and its blob's
    ///   reference, and for a symbolic link its target's bytes; each integer
    ///   little-endian at eight bytes.
    /// - provides: the one encoding the store keeps an entry in, which
    ///   [`Entry::decode`] reads back.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the round trip relates two operations, and
    ///   [`Entry::decode`] checks it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind decodes back to itself, and a byte cut off
    ///   or added is refused.
    /// - witness: `tests::entries::each_kind_of_entry_reads_back_from_its_encoding`
    #[inline]
    #[must_use]
    pub fn encode(&self) -> EntryEncoding
    {
        let mut bytes = Vec::new();
        match *self {
            Self::Directory { tree, size } => {
                bytes.push(DIRECTORY);
                bytes.extend_from_slice(&<[u8; REFERENCE_LEN]>::from(tree));
                bytes.extend_from_slice(&size.to_le_bytes());
            },
            Self::File {
                blob,
                size,
                executable,
            } => {
                bytes.push(FILE);
                bytes.push(u8::from(executable));
                bytes.extend_from_slice(&size.to_le_bytes());
                bytes.extend_from_slice(&<[u8; REFERENCE_LEN]>::from(blob));
            },
            Self::Symlink { ref target } => {
                bytes.push(SYMLINK);
                bytes.extend_from_slice(target);
            },
        }
        EntryEncoding(bytes)
    }

    /// The entry `encoded` holds.
    ///
    /// # Specification
    /// - requires: nothing; the bytes are arbitrary.
    /// - ensures: on success the entry whose [`Entry::encode`] is `encoded`.
    /// - provides: the read of a directory's record.
    /// - fails: [`StoreError::Entry`] with [`EntryFault::Unencoded`] for bytes
    ///   that encode no entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each kind decodes back to itself, and a byte cut off
    ///   or added is refused.
    /// - witness: `tests::entries::each_kind_of_entry_reads_back_from_its_encoding`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|entry| entry.encode().0.as_slice() == encoded.0))]
    pub fn decode(encoded: EncodedEntry<'_>) -> Result<Self, StoreError>
    {
        let (&tag, rest) = encoded.0.split_first().ok_or_else(unencoded)?;
        match tag {
            DIRECTORY => {
                let (tree, size) = rest.split_at_checked(REFERENCE_LEN).ok_or_else(unencoded)?;
                let size = <[u8; 8]>::try_from(size).map_err(|_short| unencoded())?;
                Ok(Self::Directory {
                    tree: TreeRef::try_from(tree)?,
                    size: u64::from_le_bytes(size),
                })
            },
            FILE => {
                let (&bit, rest) = rest.split_first().ok_or_else(unencoded)?;
                let executable = match bit {
                    0_u8 => false,
                    1_u8 => true,
                    _ => return Err(unencoded()),
                };
                let (size, blob) = rest.split_at_checked(8_usize).ok_or_else(unencoded)?;
                let size = <[u8; 8]>::try_from(size).map_err(|_short| unencoded())?;
                if blob.len() != REFERENCE_LEN {
                    return Err(unencoded());
                }
                Ok(Self::File {
                    blob: TreeRef::try_from(blob)?,
                    size: u64::from_le_bytes(size),
                    executable,
                })
            },
            SYMLINK => Ok(Self::Symlink {
                target: Box::from(rest),
            }),
            _ => Err(unencoded()),
        }
    }

    /// The entry's address: the digest of its encoding, which names its
    /// trees and so all its content.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the BLAKE3 digest of [`ADDRESS_DOMAIN`] and the encoding; two
    ///   entries of one content share it, and an edit anywhere below moves it.
    /// - provides: the identity of an output, which is its root entry's
    ///   address.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the digest is BLAKE3's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree read twice gives one address, and a byte
    ///   changed in one file moves the root's address.
    /// - witness: `tests::entries::a_tree_read_again_writes_no_object_and_keeps_its_address`
    /// - witness: `tests::entries::an_edit_writes_only_its_pieces_and_the_trees_above_it`
    #[inline]
    #[must_use]
    pub fn address(&self) -> EntryAddress
    {
        let mut hasher = blake3::Hasher::new();
        hasher.update(ADDRESS_DOMAIN);
        hasher.update(self.encode().as_ref());
        EntryAddress(*hasher.finalize().as_bytes())
    }
}

/// One piece of a blob, as the value plane keeps it: its bytes.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Piece(Vec<u8>);

impl CanonicalValue for Piece
{
    /// One constructor holding the bytes.
    ///
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(0_u8))?;
        sink.bytes(TokenBytes::from(self.0.as_slice()))?;
        sink.close()
    }

    /// # Specification
    /// trivial.
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let _tag = reader.read_tag()?;
        let bytes = reader.read_bytes()?.as_ref().to_vec();
        reader.read_close()?;
        Ok(Self(bytes))
    }
}

impl Stored for Piece
{
    /// # Specification
    /// trivial.
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(0x6590_u16), CodecVersion::from(1_u16))
    }
}

/// An output of a build: its root entry and the addresses it references.
///
/// The output's identity is its root entry's address alone; the references
/// are what the build found the output to hold, kept beside it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Output
{
    /// The root entry.
    root: Entry,
    /// The addresses of the outputs it references, in increasing order.
    references: Vec<EntryAddress>,
}

impl Output
{
    /// The output of `root`, referencing `references`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the output holds `root` and the references sorted with
    ///   duplicates dropped, so two orders of one set give one output.
    /// - provides: the record of a built output.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an output commits and derefs back equal, and two
    ///   orders of its references give one pointer.
    /// - witness: `tests::entries::an_output_reads_back_with_its_references`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.references.is_sorted_by(|left, right| left < right))]
    pub fn new(
        root: Entry,
        mut references: Vec<EntryAddress>,
    ) -> Self
    {
        references.sort_unstable();
        references.dedup();
        Self { root, references }
    }

    /// The output's identity: its root entry's address.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn identity(&self) -> EntryAddress
    {
        self.root.address()
    }

    /// The root entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> &Entry
    {
        &self.root
    }

    /// The addresses it references, in increasing order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn references(&self) -> &[EntryAddress]
    {
        &self.references
    }
}

impl CanonicalValue for Output
{
    /// One constructor: the root entry's encoding, the count of references,
    /// then each reference.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(0_u8))?;
        sink.bytes(TokenBytes::from(self.root.encode().as_ref()))?;
        let count = u64::try_from(self.references.len()).unwrap_or(u64::MAX);
        sink.word(CanonicalWord::from(count))?;
        for reference in &self.references {
            sink.bytes(TokenBytes::from(reference.as_ref()))?;
        }
        sink.close()
    }

    /// The constructor's tag is the one an output opens with, and a payload
    /// that holds no entry or no address is refused as an unexpected
    /// constructor at the output's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let position = reader.position();
        let found = reader.read_tag()?;
        let refused = ValueError::UnexpectedConstructor { found, position };
        if found != ConstructorTag::from(0_u8) {
            return Err(refused);
        }
        let root = Entry::decode(EncodedEntry::from(reader.read_bytes()?.as_ref()))
            .map_err(|_undecoded| refused)?;
        let count = u64::from(reader.read_word()?);
        let mut references = Vec::new();
        for _ in 0_u64 .. count {
            let bytes = reader.read_bytes()?;
            let address = <[u8; 32]>::try_from(bytes.as_ref()).map_err(|_short| refused)?;
            references.push(EntryAddress(address));
        }
        reader.read_close()?;
        Ok(Self { root, references })
    }
}

impl Stored for Output
{
    /// # Specification
    /// trivial.
    #[inline]
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(0x6591_u16), CodecVersion::from(1_u16))
    }
}

/// The refusal of bytes that encode no entry, no reference or no pointer.
///
/// # Specification
/// trivial.
const fn unencoded() -> StoreError
{
    StoreError::Entry(EntryFault::Unencoded)
}

/// A directory whose entries the read takes in name order: its path, its
/// names, and the encoding of each entry read so far.
struct Opened
{
    /// The directory's path.
    path: PathBuf,
    /// Its entries' names, in the order of their bytes.
    names: Vec<OsString>,
    /// The encodings of the first entries, one for each name read so far.
    encodings: Vec<EntryEncoding>,
    /// The bytes the files read so far hold in all.
    size: u64,
}

impl Opened
{
    /// The path of the next entry to read, or nothing once every entry is in.
    ///
    /// # Specification
    /// trivial.
    fn next(&self) -> Option<PathBuf>
    {
        self.names
            .get(self.encodings.len())
            .map(|name| self.path.join(name))
    }

    /// Take `entry` as the next entry.
    ///
    /// # Specification
    /// trivial.
    fn take(
        &mut self,
        entry: &Entry,
    )
    {
        self.size = self.size.saturating_add(match *entry {
            Entry::Directory { size, .. } | Entry::File { size, .. } => size,
            Entry::Symlink { .. } => 0_u64,
        });
        self.encodings.push(entry.encode());
    }
}

/// What a path reads as: an entry at once, or a directory to read into.
enum Reading
{
    /// A file or a symbolic link, whose entry is done.
    Done(Entry),
    /// A directory, whose entries come next.
    Opened(Opened),
}

impl Store
{
    /// Write `records` as one tree, or nothing when there are none.
    ///
    /// # Specification
    /// trivial.
    fn write_records(
        &self,
        records: &[RecordRef<'_>],
    ) -> Result<TreeRef, StoreError>
    {
        if records.is_empty() {
            return Ok(TreeRef::empty());
        }
        let tree = RecordTree::build(records, TreeParams::current()).map_err(StoreError::Record)?;
        self.write_tree(&tree)?;
        Ok(TreeRef::of(&tree))
    }

    /// The records of the tree `tree` names, its manifest checked against its
    /// root node.
    ///
    /// # Specification
    /// trivial.
    fn read_records(
        &self,
        tree: TreeRef,
    ) -> Result<Vec<Record>, StoreError>
    {
        if tree.records == RecordCount(0_u64) {
            return Ok(Vec::new());
        }
        let root = TreeRoot::seal(TreeParams::current(), tree.records, tree.root_node)
            .map_err(StoreError::Record)?;
        let records = leaves(self.nodes(), tree.root_node)?;
        let _opened =
            StoredRoot::open(root, tree.root_node, &self.records()).map_err(StoreError::Record)?;
        if RecordCount::of_slice(&records).map_err(StoreError::Record)? != tree.records {
            return Err(unencoded());
        }
        Ok(records)
    }

    /// Read the open `file` at `path` into the store as a blob, through
    /// `buffer`, and give the blob and the file's size.
    ///
    /// The scan cuts each buffer as it comes, and each piece goes to the value
    /// plane at its cut. So the read holds one buffer and one piece of at most
    /// the profile's maximum, never the file.
    ///
    /// # Specification
    /// trivial.
    fn read_blob(
        &self,
        file: &mut fs::File,
        path: &Path,
        buffer: &mut ReadBuffer,
    ) -> Result<Blob, StoreError>
    {
        let io = |error: std::io::Error| StoreError::io(path, &error);
        let uncut = || StoreError::Entry(EntryFault::Uncut);
        let params = ByteChunkerParams::blob();
        let mut scanner = ByteScanner::new(&params);
        let max =
            usize::try_from(u64::from(params.limits().max_bytes())).map_err(|_wide| uncut())?;
        let mut piece = Piece(Vec::with_capacity(max));
        let mut pointers = Vec::new();
        let mut size = 0_u64;
        loop {
            let read = match file.read(&mut buffer.0) {
                Ok(0) => break,
                Ok(read) => read,
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(io(error)),
            };
            size = size.saturating_add(u64::try_from(read).unwrap_or(u64::MAX));
            let mut rest = buffer.0.get(.. read).ok_or_else(uncut)?;
            while let Some(taken) = scanner.cut(CanonicalBytes::from(rest)) {
                let (head, tail) = usize::try_from(u64::from(taken))
                    .ok()
                    .and_then(|taken| rest.split_at_checked(taken))
                    .ok_or_else(uncut)?;
                piece.0.extend_from_slice(head);
                pointers.push(Recorded::from(self.commit(&piece)?));
                piece.0.clear();
                rest = tail;
            }
            piece.0.extend_from_slice(rest);
        }
        if !piece.0.is_empty() {
            pointers.push(Recorded::from(self.commit(&piece)?));
        }
        // A record key sorts as its bytes, so the index is spelled most
        // significant byte first and the pieces stand in their order.
        #[expect(
            clippy::big_endian_bytes,
            reason = "a record key sorts as its bytes, so its index is big-endian"
        )]
        let keys: Vec<[u8; 8]> = (0_u64 ..)
            .take(pointers.len())
            .map(u64::to_be_bytes)
            .collect();
        let records: Vec<RecordRef<'_>> = keys
            .iter()
            .zip(&pointers)
            .map(|(key, pointer)| RecordRef::new(key.as_slice(), pointer.as_ref()))
            .collect();
        Ok(Blob {
            tree: self.write_records(&records)?,
            size,
        })
    }

    /// Read `path` as a file or a symbolic link, whose entry is done, or as a
    /// directory opened with its names in the order of their bytes.
    ///
    /// # Specification
    /// trivial.
    fn read_at(
        &self,
        path: &Path,
        buffer: &mut ReadBuffer,
    ) -> Result<Reading, StoreError>
    {
        let io = |error: std::io::Error| StoreError::io(path, &error);
        let meta = fs::symlink_metadata(path).map_err(io)?;
        let kind = meta.file_type();
        if kind.is_symlink() {
            let target = fs::read_link(path).map_err(io)?;
            return Ok(Reading::Done(Entry::Symlink {
                target: Box::from(target.as_os_str().as_bytes()),
            }));
        }
        if kind.is_dir() {
            let mut names = fs::read_dir(path)
                .map_err(io)?
                .map(|entry| entry.map(|entry| entry.file_name()))
                .collect::<Result<Vec<_>, _>>()
                .map_err(io)?;
            names.sort_unstable_by(|left, right| left.as_bytes().cmp(right.as_bytes()));
            return Ok(Reading::Opened(Opened {
                path: path.to_path_buf(),
                encodings: Vec::with_capacity(names.len()),
                names,
                size: 0_u64,
            }));
        }
        if kind.is_block_device() || kind.is_char_device() || kind.is_fifo() || kind.is_socket() {
            return Err(StoreError::Entry(EntryFault::Unkept));
        }
        let mut file = fs::File::open(path).map_err(io)?;
        let Blob { tree, size } = self.read_blob(&mut file, path, buffer)?;
        Ok(Reading::Done(Entry::File {
            blob: tree,
            size,
            executable: meta.permissions().mode() & 0o111_u32 != 0_u32,
        }))
    }

    /// Write the tree of `opened`'s entries, one record per name, and give
    /// the directory's entry.
    ///
    /// # Specification
    /// trivial.
    fn close(
        &self,
        opened: &Opened,
    ) -> Result<Entry, StoreError>
    {
        let records: Vec<RecordRef<'_>> = opened
            .names
            .iter()
            .zip(&opened.encodings)
            .map(|(name, encoding)| RecordRef::new(name.as_bytes(), encoding.as_ref()))
            .collect();
        Ok(Entry::Directory {
            tree: self.write_records(&records)?,
            size: opened.size,
        })
    }

    /// Read the directory, file or symbolic link at `path` into the store.
    ///
    /// The read holds one opened directory for each depth of the path it
    /// reads, so a deep tree takes no stack of the thread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the entry of `path`: a directory's tree holds one
    ///   record per entry in the order of the names' bytes, a file's blob holds
    ///   its pieces as the byte profile cuts them, a link its target. Every
    ///   node and piece the entry reaches stands in the store, and a path read
    ///   again gives an equal entry and writes no object.
    /// - provides: the read of a build's output, or of a source tree, into the
    ///   store.
    /// - fails: [`StoreError::Io`] for a path that cannot be read,
    ///   [`StoreError::Entry`] for a device, a socket or a pipe, and the
    ///   planes' refusals.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a tree of every kind of entry: it writes out to the
    ///   same bytes and modes, a second read writes no object, and an edit
    ///   writes only its pieces and the trees above it.
    /// - witness: `tests::entries::a_tree_writes_out_to_the_same_bytes_and_modes`
    /// - witness: `tests::entries::a_tree_read_again_writes_no_object_and_keeps_its_address`
    /// - witness: `tests::entries::an_edit_writes_only_its_pieces_and_the_trees_above_it`
    #[inline]
    pub fn read_in(
        &self,
        path: &Path,
    ) -> Result<Entry, StoreError>
    {
        let mut buffer = ReadBuffer::new();
        let mut opened = match self.read_at(path, &mut buffer)? {
            Reading::Done(entry) => return Ok(entry),
            Reading::Opened(opened) => opened,
        };
        let mut above: Vec<Opened> = Vec::new();
        loop {
            if let Some(next) = opened.next() {
                match self.read_at(&next, &mut buffer)? {
                    Reading::Done(entry) => opened.take(&entry),
                    Reading::Opened(inner) => above.push(core::mem::replace(&mut opened, inner)),
                }
                continue;
            }
            let entry = self.close(&opened)?;
            let Some(parent) = above.pop()
            else {
                return Ok(entry);
            };
            opened = parent;
            opened.take(&entry);
        }
    }

    /// Write `entry` out at `path`, which must not stand yet.
    ///
    /// The write holds the entries it owes in one list, so a deep tree takes
    /// no stack of the thread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success `path` holds what `entry` names: a directory with
    ///   each entry written below it under its name, a file with its pieces'
    ///   bytes and its executable bit, a link to its target. Each tree is
    ///   checked against the manifest its reference seals, and each piece by
    ///   its digest as the value plane loads it.
    /// - provides: the materialisation of an output into a real directory, as a
    ///   sandboxed command needs.
    /// - fails: [`StoreError::Entry`] for a name a write would leave the
    ///   directory by, a file whose pieces hold another size, or a record that
    ///   encodes no entry; [`StoreError::Io`] for a path that stands or cannot
    ///   be made; and the planes' refusals. A failed write leaves what it made
    ///   so far.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on a tree of every kind of entry, and on a directory
    ///   whose record names `..`, which is refused before anything is made.
    /// - witness: `tests::entries::a_tree_writes_out_to_the_same_bytes_and_modes`
    /// - witness: `tests::entries::a_name_that_leaves_the_directory_is_refused`
    #[inline]
    pub fn write_out(
        &self,
        entry: &Entry,
        path: &Path,
    ) -> Result<(), StoreError>
    {
        // A name a write cannot make inside a directory: empty, `.` or `..`,
        // or with a `/` or a zero byte.
        let leaves_directory = |name: &[u8]| {
            name.is_empty()
                || name == b"."
                || name == b".."
                || name.iter().any(|&byte| byte == b'/' || byte == 0_u8)
        };
        let mut owed = vec![(entry.clone(), path.to_path_buf())];
        while let Some((entry, path)) = owed.pop() {
            let io = |error: std::io::Error| StoreError::io(&path, &error);
            match entry {
                Entry::Directory { tree, .. } => {
                    let records = self.read_records(tree)?;
                    if let Some(name) = records
                        .iter()
                        .map(|record| record.key())
                        .find(|name| leaves_directory(name.as_ref()))
                    {
                        return Err(StoreError::Entry(EntryFault::Unsafe {
                            name: Box::from(name.as_ref()),
                        }));
                    }
                    fs::DirBuilder::new().create(&path).map_err(io)?;
                    // The list is a stack, so the last name goes in first and
                    // the entries are written in name order.
                    for record in records.iter().rev() {
                        let child = Entry::decode(EncodedEntry::from(record.value().as_ref()))?;
                        let key = record.key();
                        owed.push((child, path.join(OsStr::from_bytes(key.as_ref()))));
                    }
                },
                Entry::File {
                    blob,
                    size,
                    executable,
                } => {
                    // Each piece goes to the file as it is read, so the write
                    // holds one piece at a time, never the whole file.
                    let mut file = fs::OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .open(&path)
                        .map_err(io)?;
                    let mut held = 0_u64;
                    for record in self.read_records(blob)? {
                        let recorded = Recorded::try_from(record.value().as_ref())
                            .map_err(|_short| unencoded())?;
                        let piece: Piece = self.deref(recorded.pointer())?;
                        std::io::Write::write_all(&mut file, &piece.0).map_err(io)?;
                        held =
                            held.saturating_add(u64::try_from(piece.0.len()).unwrap_or(u64::MAX));
                    }
                    if held != size {
                        return Err(StoreError::Entry(EntryFault::Resized {
                            stated: size,
                            held,
                        }));
                    }
                    let mode = if executable {
                        EXECUTABLE_MODE
                    }
                    else {
                        PLAIN_MODE
                    };
                    file.set_permissions(fs::Permissions::from_mode(mode))
                        .map_err(io)?;
                },
                Entry::Symlink { ref target } => {
                    std::os::unix::fs::symlink(OsStr::from_bytes(target), &path).map_err(io)?;
                },
            }
        }
        Ok(())
    }
}
