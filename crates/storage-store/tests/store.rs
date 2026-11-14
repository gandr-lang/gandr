//! The store's contract: each plane and the roots read back from disk after
//! reopening, bytes changed on disk are refused, and threads share one store
//! with no lock.

extern crate alloc;

use alloc::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;

use gandr_storage_records::BlockStore as _;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::StoredRoot;
use gandr_storage_records::TreeParams;
use gandr_storage_store::ContentPtr;
use gandr_storage_store::Namer;
use gandr_storage_store::Register;
use gandr_storage_store::RootName;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_store::Stored;
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
use quenchant_shape::shape::Maybe;

/// The tag a list of labels opens with.
const LIST: u8 = 0_u8;

/// The tag each label opens with.
const LABEL: u8 = 1_u8;

/// A list of byte strings: a count, then one constructor per label, so a long
/// list is cut into several chunks.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Labels(Vec<Vec<u8>>);

impl CanonicalValue for Labels
{
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(LIST))?;
        let count = self
            .0
            .iter()
            .fold(0_u64, |count, _| count.saturating_add(1));
        sink.word(CanonicalWord::from(count))?;
        for label in &self.0 {
            sink.open(ConstructorTag::from(LABEL))?;
            sink.bytes(TokenBytes::from(label.as_slice()))?;
            sink.close()?;
        }
        sink.close()
    }

    /// # Specification
    /// trivial.
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let _list = reader.read_tag()?;
        let count = u64::from(reader.read_word()?);
        let mut labels = Vec::new();
        for _ in 0 .. count {
            let _label = reader.read_tag()?;
            let bytes = reader.read_bytes()?;
            labels.push(bytes.as_ref().to_vec());
            reader.read_close()?;
        }
        reader.read_close()?;
        Ok(Self(labels))
    }
}

impl Stored for Labels
{
    /// # Specification
    /// trivial.
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(0x7E57_u16), CodecVersion::from(1_u16))
    }
}

/// A fresh, empty directory for `test`, removed first if a run left it.
///
/// # Specification
/// trivial.
fn scratch(test: &Path) -> PathBuf
{
    let directory = std::env::temp_dir().join(format!(
        "gandr-storage-store-{}-{}",
        test.display(),
        std::process::id()
    ));
    if directory.exists() {
        std::fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
    }
    directory
}

/// How many labels a case lists.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Count(u8);

/// `count` labels, each distinct.
///
/// # Specification
/// trivial.
fn labels(count: Count) -> Labels
{
    Labels(
        (0 .. count.0)
            .map(|index| vec![index; usize::from(index)])
            .collect(),
    )
}

/// The files of the directory `directory`, each by its name.
///
/// # Specification
/// trivial.
fn files(directory: &Path) -> Vec<PathBuf>
{
    let mut files: Vec<PathBuf> = std::fs::read_dir(directory)
        .expect("the plane's directory is listed")
        .map(|entry| entry.expect("an entry is read").path())
        .collect();
    files.sort();
    files
}

/// The length of a segment record's header.
const HEADER: u64 = 64_u64;

/// One record a plane's segment holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Found
{
    /// The object's identity, in lowercase hexadecimal.
    digest: String,
    /// The segment that holds it.
    file: PathBuf,
    /// Where its bytes start in the segment, past its header.
    offset: u64,
    /// How many bytes it holds.
    length: u64,
}

/// Every record the segments of the plane at `directory` hold, in order, up
/// to each segment's first bytes that open no record.
///
/// # Specification
/// trivial.
pub fn records(directory: &Path) -> Vec<Found>
{
    let mut found = Vec::new();
    for file in files(directory) {
        let bytes = std::fs::read(&file).expect("a segment reads");
        let mut rest = bytes.as_slice();
        let mut at = 0_u64;
        while let Some((magic, after)) = rest.split_first_chunk::<4>()
            && magic == b"gsg1"
            && let Some((length, after)) = after.split_first_chunk::<4>()
            && let Some((digest, after)) = after.split_first_chunk::<32>()
            && let Some((_place, after)) = after.split_first_chunk::<24>()
            && let Ok(length) = usize::try_from(u32::from_le_bytes(*length))
            && let Some(next) = after.get(length ..)
        {
            let body = u64::try_from(length).expect("a record's length fits 64 bits");
            let offset = at.saturating_add(HEADER);
            found.push(Found {
                digest: digest.iter().fold(String::new(), |mut text, byte| {
                    core::fmt::Write::write_fmt(&mut text, format_args!("{byte:02x}"))
                        .expect("a string takes text");
                    text
                }),
                file: file.clone(),
                offset,
                length: body,
            });
            at = offset.saturating_add(body);
            rest = next;
        }
    }
    found
}

/// The record of the value plane at `root` that holds the root chunk of
/// `pointer`.
///
/// # Specification
/// trivial.
fn held(
    root: &Path,
    pointer: ContentPtr,
) -> Found
{
    let digest = pointer.digest().to_string();
    records(&root.join("chunks"))
        .into_iter()
        .find(|found| found.digest == digest)
        .expect("a segment holds the root chunk")
}

/// Change the last byte of the record `found`, in place in its segment.
///
/// # Specification
/// trivial.
fn corrupt(found: &Found)
{
    use std::os::unix::fs::FileExt as _;
    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&found.file)
        .expect("the segment opens");
    let last = found
        .offset
        .saturating_add(found.length)
        .checked_sub(1_u64)
        .expect("a record has bytes");
    let mut byte = [0_u8; 1];
    file.read_exact_at(&mut byte, last)
        .expect("the last byte reads");
    let [ref mut changed] = byte;
    *changed ^= 0xFF_u8;
    file.write_all_at(&byte, last)
        .expect("the last byte is changed");
}

/// A missing root and its two plane directories are made on opening.
#[test]
fn a_missing_root_directory_is_made_on_opening()
{
    let root = scratch(Path::new("made"))
        .join("data")
        .join("gandr")
        .join("store");
    let (store, _register) = Store::open(&root).expect("a missing root is made");
    assert_eq!(store.root(), root.as_path());
    for plane in ["chunks", "nodes"] {
        assert!(root.join(plane).is_dir(), "`{plane}` stands after opening");
    }
    assert_eq!(
        store.roots().names().count(),
        0,
        "a new store names no root"
    );
}

/// A value cut into several chunks is written as one record per chunk, derefs
/// back equal from a store opened later, and commits again to the same
/// pointer without writing another record.
#[test]
fn a_committed_value_derefs_back_after_reopening()
{
    let root = scratch(Path::new("committed"));
    let value = labels(Count(120));
    let pointer = {
        let (store, _register) = Store::open(&root).expect("the store opens");
        let pointer = store.commit(&value).expect("the value commits");
        let back: Labels = store
            .deref(pointer)
            .expect("the value derefs where it was committed");
        assert_eq!(back, value);
        pointer
    };
    let written = records(&root.join("chunks"));
    assert!(
        written.len() > 1,
        "a long list is cut into several chunks, each its own record: {written:?}"
    );
    let digest = pointer.digest().to_string();
    assert!(
        written.iter().any(|found| found.digest == digest),
        "a record holds the root chunk under its digest"
    );
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    let back: Labels = reopened
        .deref(pointer)
        .expect("the value derefs after reopening");
    assert_eq!(back, value);
    assert_eq!(
        reopened.commit(&value),
        Ok(pointer),
        "committing again returns the same pointer"
    );
    assert_eq!(
        records(&root.join("chunks")),
        written,
        "and writes no other record"
    );
}

/// A chunk whose record is changed on disk is refused by its digest when the
/// value is read back, and a pointer the store never committed is unknown.
#[test]
fn a_chunk_changed_on_disk_is_refused_by_its_digest()
{
    let root = scratch(Path::new("changed"));
    let pointer = Store::open(&root)
        .expect("the store opens")
        .0
        .commit(&labels(Count(3)))
        .expect("the value commits");
    corrupt(&held(&root, pointer));
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    assert!(
        matches!(
            reopened.deref::<Labels>(pointer),
            Err(StoreError::Value(ValueError::DigestMismatch { expected, .. })) if expected == pointer.digest()
        ),
        "the changed chunk is refused by its digest"
    );
    let other = Store::open(&scratch(Path::new("changed-other")))
        .expect("another store opens")
        .0
        .commit(&labels(Count(4)))
        .expect("another value commits");
    assert_eq!(
        reopened.deref::<Labels>(other),
        Err(StoreError::Value(ValueError::UnknownChunk {
            digest: other.digest()
        })),
        "a chunk the store never held is unknown"
    );
}

/// A value read with no codec resides in exactly the chunks its commit
/// wrote, and its bytes are the sum of their records' lengths. A chunk changed
/// on disk is refused by its digest, as a dereference refuses it (#6296).
#[test]
fn a_committed_value_resides_in_the_chunks_its_commit_wrote_6296()
{
    let root = scratch(Path::new("resides"));
    let pointer = Store::open(&root)
        .expect("the store opens")
        .0
        .commit(&labels(Count(120)))
        .expect("the value commits");
    let written = records(&root.join("chunks"));
    let residence = Store::open(&root)
        .expect("the store opens again")
        .0
        .closure(pointer)
        .expect("the closure reads");
    let named: BTreeSet<String> = residence
        .closure()
        .digests()
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        named,
        written
            .iter()
            .map(|found| found.digest.clone())
            .collect::<BTreeSet<String>>(),
        "the closure is each chunk the commit wrote"
    );
    assert!(written.len() > 1, "a long list resides in several chunks");
    let lengths = written
        .iter()
        .fold(0_u64, |sum, found| sum.saturating_add(found.length));
    assert_eq!(
        u64::from(residence.bytes()),
        lengths,
        "the bytes are the lengths of the chunks' records"
    );
    let digest = pointer.digest().to_string();
    let changed = written
        .iter()
        .find(|found| found.digest == digest)
        .expect("a segment holds the root chunk");
    corrupt(changed);
    assert!(
        matches!(
            Store::open(&root).expect("the store opens a third time").0.closure(pointer),
            Err(StoreError::Value(ValueError::DigestMismatch { expected, .. })) if expected == pointer.digest()
        ),
        "the changed chunk is refused by its digest"
    );
}

/// A chunk a read refused by its digest is written afresh by the next commit
/// of its value, and a store opened later derefs the value back (#4074).
#[test]
fn a_refused_chunk_is_written_afresh_by_the_next_commit_4074()
{
    let root = scratch(Path::new("rewritten"));
    let value = labels(Count(3));
    let pointer = Store::open(&root)
        .expect("the store opens")
        .0
        .commit(&value)
        .expect("the value commits");
    corrupt(&held(&root, pointer));
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    assert!(
        matches!(
            reopened.deref::<Labels>(pointer),
            Err(StoreError::Value(ValueError::DigestMismatch { .. }))
        ),
        "the changed chunk is refused by its digest"
    );
    assert_eq!(
        reopened.commit(&value),
        Ok(pointer),
        "the value commits again"
    );
    let (fresh, _register) = Store::open(&root).expect("the store opens a third time");
    assert_eq!(
        fresh.deref::<Labels>(pointer),
        Ok(value),
        "the chunk is written afresh, and the value derefs back"
    );
}

/// A written record tree's root opens from the record plane of a store
/// opened later.
#[test]
fn a_written_tree_opens_from_the_record_plane_after_reopening()
{
    let root = scratch(Path::new("tree"));
    let records: Vec<(Vec<u8>, Vec<u8>)> = (0_u8 .. 40_u8)
        .map(|index| (vec![b'k', index], vec![index; 8]))
        .collect();
    let refs: Vec<RecordRef<'_>> = records
        .iter()
        .map(|&(ref key, ref value)| RecordRef::new(key.as_slice(), value.as_slice()))
        .collect();
    let tree = RecordTree::build(&refs, TreeParams::current()).expect("the records build a tree");
    Store::open(&root)
        .expect("the store opens")
        .0
        .write_tree(&tree)
        .expect("the tree is written");
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    let opened = StoredRoot::open(tree.root(), tree.root_node_hash(), &reopened.records())
        .expect("the tree's root opens from the record plane");
    assert_eq!(opened.root(), tree.root());
    for leaf in &tree.leaf_hashes() {
        assert!(
            reopened.records().load(*leaf).is_ok(),
            "every leaf loads verified"
        );
    }
}

/// A root set reads back from a store opened later, and setting the name
/// again replaces what it named and keeps every other root.
#[test]
fn a_root_set_reads_back_after_reopening()
{
    let root = scratch(Path::new("rooted"));
    let lock = RootName::new(String::from("lock/hello"));
    let verdict = RootName::new(String::from("verdict/one"));
    let (first, second, third): (ContentPtr, ContentPtr, ContentPtr) = {
        let (store, mut register) = Store::open(&root).expect("the store opens");
        let first = store.commit(&labels(Count(1))).expect("a value commits");
        let second = store.commit(&labels(Count(2))).expect("a value commits");
        let third = store.commit(&labels(Count(5))).expect("a value commits");
        register
            .name(lock.clone(), first)
            .expect("the first root is set");
        register
            .name(verdict.clone(), second)
            .expect("the second root is set");
        assert_eq!(store.roots().root(&lock), Maybe::Present(first));
        (first, second, third)
    };
    let (reopened, mut register) = Store::open(&root).expect("the store opens again");
    assert_eq!(reopened.roots().root(&lock), Maybe::Present(first));
    assert_eq!(reopened.roots().root(&verdict), Maybe::Present(second));
    register
        .name(lock.clone(), third)
        .expect("the first root is set again");
    let (again, _register) = Store::open(&root).expect("the store opens a third time");
    assert_eq!(
        again.roots().root(&lock),
        Maybe::Present(third),
        "setting a name again replaces what it named"
    );
    assert_eq!(
        again.roots().root(&verdict),
        Maybe::Present(second),
        "and keeps the other root"
    );
    assert_eq!(again.roots().names().cloned().collect::<Vec<_>>(), vec![
        lock, verdict
    ]);
}

/// Two stores opened over one directory each set a root, and a store opened
/// after both holds both: a change reads the roots again under the lock.
#[test]
fn two_stores_over_one_directory_keep_each_other_s_roots()
{
    let root = scratch(Path::new("shared"));
    let (left, mut left_register) = Store::open(&root).expect("the first store opens");
    let (right, mut right_register) = Store::open(&root).expect("the second store opens");
    let one = left.commit(&labels(Count(1))).expect("a value commits");
    let two = right.commit(&labels(Count(2))).expect("a value commits");
    let first = RootName::new(String::from("lock/first"));
    let second = RootName::new(String::from("lock/second"));
    left_register
        .name(first.clone(), one)
        .expect("the first store sets its root");
    right_register
        .name(second.clone(), two)
        .expect("the second store sets its root");
    assert_eq!(
        right.roots().root(&first),
        Maybe::Present(one),
        "the second store reads the first's root as it changes its own"
    );
    let (after, _register) = Store::open(&root).expect("a third store opens");
    assert_eq!(after.roots().root(&first), Maybe::Present(one));
    assert_eq!(after.roots().root(&second), Maybe::Present(two));
}

/// Naming roots one at a time writes the record plane no tree per naming: a
/// store that names 256 roots, each by a change of its own, holds far fewer
/// nodes than namings, and every root reads back after reopening.
#[test]
fn naming_roots_one_at_a_time_writes_no_tree_per_naming_4081()
{
    let root = scratch(Path::new("journaled"));
    let (store, mut register) = Store::open(&root).expect("the store opens");
    let pointer = store.commit(&labels(Count(3))).expect("a value commits");
    let names: Vec<RootName> = (0_u16 .. 256_u16)
        .map(|index| RootName::new(format!("verdict/{index:04}")))
        .collect();
    for name in &names {
        register
            .name(name.clone(), pointer)
            .expect("each root is set");
    }
    let nodes = records(&root.join("nodes")).len();
    assert!(
        nodes.saturating_mul(4) < names.len(),
        "256 namings leave {nodes} nodes on the record plane"
    );
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    assert!(
        names
            .iter()
            .all(|name| reopened.roots().root(name) == Maybe::Present(pointer)),
        "every root reads back after reopening"
    );
}

/// Two stores over one directory keep each other's roots across folds: a
/// store reads the tree another folded, the journal another appended to, and
/// a tree folded again after its own reading.
#[test]
fn two_stores_keep_each_other_s_roots_across_a_fold_4081()
{
    let root = scratch(Path::new("folded"));
    let (left, mut left_register) = Store::open(&root).expect("the first store opens");
    let (right, mut right_register) = Store::open(&root).expect("the second store opens");
    let pointer = left.commit(&labels(Count(2))).expect("a value commits");
    let named = |range: core::ops::Range<u16>| -> Vec<RootName> {
        range
            .map(|index| RootName::new(format!("lock/{index:03}")))
            .collect()
    };
    let early = named(0_u16 .. 200_u16);
    for name in &early {
        left_register
            .name(name.clone(), pointer)
            .expect("the first store names a root");
    }
    let own = RootName::new(String::from("verdict/right"));
    right_register
        .name(own.clone(), pointer)
        .expect("the second store names its root");
    assert!(
        early
            .iter()
            .all(|name| right.roots().root(name) == Maybe::Present(pointer)),
        "the second store reads every root the first named, folded or journaled"
    );
    let late = named(200_u16 .. 400_u16);
    for name in &late {
        left_register
            .name(name.clone(), pointer)
            .expect("the first store names a root");
    }
    assert_eq!(
        left.roots().root(&own),
        Maybe::Present(pointer),
        "the first store reads the second's journaled root"
    );
    let again = RootName::new(String::from("verdict/right-again"));
    right_register
        .name(again, pointer)
        .expect("the second store names a root again");
    assert!(
        late.iter()
            .all(|name| right.roots().root(name) == Maybe::Present(pointer)),
        "the second store reads the roots folded after its own reading"
    );
    let (after, _register) = Store::open(&root).expect("a third store opens");
    assert_eq!(
        after.roots().names().count(),
        early.len().saturating_add(late.len()).saturating_add(2),
        "a store opened after both reads every root"
    );
}

/// A journal entry torn by a naming that stopped while it appended ends the
/// journal: the roots before it read back, and the next naming cuts it and
/// stands after it.
#[test]
fn a_torn_journal_entry_is_cut_by_the_next_naming_4081()
{
    let root = scratch(Path::new("torn"));
    let first = RootName::new(String::from("verdict/first"));
    let second = RootName::new(String::from("verdict/second"));
    let third = RootName::new(String::from("verdict/third"));
    let pointer = {
        let (store, mut register) = Store::open(&root).expect("the store opens");
        let pointer = store.commit(&labels(Count(2))).expect("a value commits");
        register
            .name(first.clone(), pointer)
            .expect("the first root is set");
        register
            .name(second.clone(), pointer)
            .expect("the second root is set");
        pointer
    };
    let journal = root.join("roots.log.journal");
    let mut bytes = std::fs::read(&journal).expect("the journal reads");
    bytes.extend_from_slice(&[16_u8, 0_u8, 0_u8, 0_u8, b'v', b'e']);
    std::fs::write(&journal, &bytes).expect("a torn entry is appended");
    let (reopened, mut register) = Store::open(&root).expect("a store opens over the torn journal");
    assert_eq!(
        reopened.roots().root(&second),
        Maybe::Present(pointer),
        "the entry before the torn one reads back"
    );
    register
        .name(third.clone(), pointer)
        .expect("the third root is set");
    let (again, _register) = Store::open(&root).expect("the store opens again");
    assert_eq!(
        again.roots().names().cloned().collect::<Vec<_>>(),
        vec![first, second, third],
        "the naming after the torn entry stands, and the torn entry names nothing"
    );
}

/// A roots file naming no node is refused by name on opening.
#[test]
fn a_roots_file_naming_no_node_is_refused_on_opening()
{
    let root = scratch(Path::new("unrooted"));
    drop(Store::open(&root).expect("the store opens"));
    std::fs::write(root.join("roots.log"), "not a node\n").expect("the roots log is written");
    assert!(
        matches!(
            Store::open(&root),
            Err(StoreError::Roots {
                fault: gandr_storage_store::RootsFault::Unspelled,
                ..
            })
        ),
        "a roots file that spells no node is refused"
    );
}

/// A roots log whose tree reaches a node the store does not hold is refused
/// by that log and the node, and removing the log, as the refusal says, opens
/// the store again.
#[test]
fn a_roots_tree_the_store_does_not_hold_is_refused_by_its_file_4397()
{
    let root = scratch(Path::new("unheld"));
    let name = RootName::new(String::from("lock/hello"));
    {
        let (store, mut register) = Store::open(&root).expect("the store opens");
        let pointer = store.commit(&labels(Count(1))).expect("a value commits");
        register.name(name, pointer).expect("the root is set");
    }
    let roots = root.join("roots.log");
    let named = std::fs::read_to_string(&roots).expect("the roots log names a tree");
    let node = named.trim();
    for segment in files(&root.join("nodes")) {
        std::fs::remove_file(segment).expect("the record plane's segment is removed");
    }
    let refused = Store::open(&root).expect_err("a tree the store does not hold is refused");
    assert!(
        matches!(
            refused,
            StoreError::Roots {
                ref path,
                fault: gandr_storage_store::RootsFault::Unheld { node: unheld },
            } if *path == roots && unheld.to_string() == node
        ),
        "{refused:?}"
    );
    assert!(
        refused
            .to_string()
            .ends_with("remove it to start the roots anew"),
        "the refusal names its repair: {refused}"
    );
    std::fs::remove_file(&roots).expect("the roots file is removed");
    let (reopened, _register) = Store::open(&root).expect("the store opens without its roots file");
    assert_eq!(
        reopened.roots().names().count(),
        0_usize,
        "the roots start anew"
    );
}

/// How many threads commit one value at once.
const WRITERS: usize = 16_usize;

/// Sixteen threads that share one store and commit one value at once each
/// return its pointer, leave the chunks one writer leaves, and the value
/// derefs back from a store opened later (#6899).
#[test]
fn sixteen_writers_of_one_value_leave_one_object_per_digest_6899()
{
    let alone = scratch(Path::new("one-writer"));
    let value = labels(Count(120));
    let expected = Store::open(&alone)
        .expect("the store opens")
        .0
        .commit(&value)
        .expect("one writer commits the value");
    let root = scratch(Path::new("sixteen-writers"));
    let (store, _register) = Store::open(&root).expect("the store opens");
    let start = std::sync::Barrier::new(WRITERS);
    let pointers: Vec<Result<ContentPtr, StoreError>> = std::thread::scope(|scope| {
        let writers: Vec<_> = core::iter::repeat_with(|| {
            scope.spawn(|| {
                let _leader = start.wait();
                store.commit(&value)
            })
        })
        .take(WRITERS)
        .collect();
        writers
            .into_iter()
            .map(|writer| writer.join().expect("a writer runs to its end"))
            .collect()
    });
    assert!(
        pointers.iter().all(|pointer| *pointer == Ok(expected)),
        "every writer returns the pointer one writer returns: {pointers:?}"
    );
    let digests = |directory: &Path| -> BTreeSet<String> {
        records(directory)
            .into_iter()
            .map(|found| found.digest)
            .collect()
    };
    assert_eq!(
        digests(&root.join("chunks")),
        digests(&alone.join("chunks")),
        "sixteen writers leave the chunks one writer leaves"
    );
    let back: Labels = Store::open(&root)
        .expect("the store opens again")
        .0
        .deref(expected)
        .expect("the value derefs after reopening");
    assert_eq!(back, value);
}

/// Sixteen threads that share one store and commit sixteen distinct values at
/// once append each to a segment of its shard's own. The plane holds one
/// segment for each shard at most, and every value derefs back from a store
/// opened later (#7462).
#[test]
fn sixteen_writers_append_to_their_own_segments_7462()
{
    let root = scratch(Path::new("sixteen-segments"));
    let (store, _register) = Store::open(&root).expect("the store opens");
    let values: Vec<Labels> = (40_u8 ..)
        .take(WRITERS)
        .map(|count| labels(Count(count)))
        .collect();
    let start = std::sync::Barrier::new(WRITERS);
    let pointers: Vec<ContentPtr> = std::thread::scope(|scope| {
        let writers: Vec<_> = values
            .iter()
            .map(|value| {
                let start = &start;
                let store = &store;
                scope.spawn(move || {
                    let _leader = start.wait();
                    store.commit(value).expect("a writer commits its value")
                })
            })
            .collect();
        writers
            .into_iter()
            .map(|writer| writer.join().expect("a writer runs to its end"))
            .collect()
    });
    let segments = files(&root.join("chunks"));
    assert!(
        !segments.is_empty() && segments.len() <= WRITERS,
        "the writers append to one segment each at most: {segments:?}"
    );
    let held: BTreeSet<String> = records(&root.join("chunks"))
        .into_iter()
        .map(|found| found.digest)
        .collect();
    let wanted: BTreeSet<String> = pointers
        .iter()
        .map(|pointer| pointer.digest().to_string())
        .collect();
    assert!(
        wanted.is_subset(&held),
        "a segment holds each value's root chunk"
    );
    let reopened = Store::open(&root).expect("the store opens again").0;
    for (pointer, value) in pointers.iter().zip(&values) {
        let back: Labels = reopened
            .deref(*pointer)
            .expect("each value derefs from the plane after reopening");
        assert_eq!(&back, value, "each writer's value reads back whole");
    }
}

/// A segment whose tail a writer tore is cut at its first header that does
/// not check: each record before it derefs after reopening, and a commit
/// after it stands (#7462).
#[test]
fn a_torn_segment_tail_is_cut_on_opening_7462()
{
    let root = scratch(Path::new("torn-segment"));
    let first = labels(Count(3));
    let second = labels(Count(4));
    let pointer = Store::open(&root)
        .expect("the store opens")
        .0
        .commit(&first)
        .expect("the first value commits");
    let segments = files(&root.join("chunks"));
    let [ref segment] = *segments
    else {
        panic!("one commit appends to one segment: {segments:?}");
    };
    let bytes = std::fs::read(segment).expect("the segment reads");
    let torn = bytes
        .get(.. 40_usize)
        .expect("a record is longer than 40 bytes");
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .open(segment)
        .expect("the segment opens to append");
    std::io::Write::write_all(&mut file, torn).expect("a torn record is appended");
    drop(file);
    let (reopened, _register) = Store::open(&root).expect("a store opens over the torn tail");
    assert_eq!(
        reopened.deref::<Labels>(pointer),
        Ok(first.clone()),
        "the record before the torn one derefs"
    );
    let later = reopened
        .commit(&second)
        .expect("a value commits after the torn tail");
    let (again, _register) = Store::open(&root).expect("the store opens again");
    assert_eq!(again.deref::<Labels>(pointer), Ok(first));
    assert_eq!(
        again.deref::<Labels>(later),
        Ok(second),
        "the commit after the torn tail stands"
    );
}

/// A store finds a value that a second store over its directory committed
/// after it opened: a load that misses reads the other writers' new records
/// (#7462).
#[test]
fn a_store_finds_what_another_put_after_it_opened_7462()
{
    let root = scratch(Path::new("other-writer"));
    let value = labels(Count(30));
    let (reader, _reader_register) = Store::open(&root).expect("the first store opens");
    let (writer, _writer_register) = Store::open(&root).expect("the second store opens");
    let pointer = writer.commit(&value).expect("the second store commits");
    assert_eq!(
        reader.deref::<Labels>(pointer),
        Ok(value),
        "the first store derefs what the second committed after it opened"
    );
}

/// The variable that names where a crash test's child stops.
const CRASH_AT: &str = "GANDR_STORE_CRASH_AT";

/// The variable that names the store a crash test's child writes.
const CRASH_CHILD: &str = "GANDR_STORE_CRASH_CHILD";

/// How many roots a crash test's child names: past the first fold of a tree
/// of one root, which the 65th naming makes.
const CRASH_NAMINGS: u16 = 70_u16;

/// The work of a crash test's child over the store at `root`: commit a value,
/// then name it once for each root, and print each name once its naming
/// returns.
///
/// # Specification
/// trivial.
fn crash_child(root: &Path)
{
    let (store, mut register) = Store::open(root).expect("the child's store opens");
    let pointer = store
        .commit(&labels(Count(50)))
        .expect("the child's value commits");
    for index in 0_u16 .. CRASH_NAMINGS {
        let name = format!("crash/{index:03}");
        register
            .name(RootName::new(name.clone()), pointer)
            .expect("the child names a root");
        println!("named {name}");
    }
}

/// A writer stopped at each point before and after each durable step of a
/// commit and a fold leaves a store that opens, whose every root derefs, and
/// that holds every naming that returned before the stop (#7462).
#[test]
fn a_crash_after_each_step_of_a_fold_leaves_roots_that_load_7459()
{
    if let Some(root) = std::env::var_os(CRASH_CHILD) {
        crash_child(Path::new(&root));
        return;
    }
    let points = [
        "objects-before",
        "objects-after",
        "tree-before",
        "tree-after",
        "log-before",
        "log-after",
        "journal-before",
        "journal-after",
        "",
    ];
    let base = RootName::new(String::from("crash/base"));
    let before = labels(Count(5));
    let program = std::env::current_exe().expect("the test binary is known");
    for point in points {
        let root = scratch(&Path::new("crash").join(if point.is_empty() { "none" } else { point }));
        let pointer = {
            let (store, mut register) = Store::open(&root).expect("the store opens");
            let pointer = store.commit(&before).expect("the first value commits");
            register
                .name(base.clone(), pointer)
                .expect("the first root is set");
            pointer
        };
        let output = std::process::Command::new(&program)
            .args([
                "a_crash_after_each_step_of_a_fold_leaves_roots_that_load_7459",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CRASH_CHILD, &root)
            .env(CRASH_AT, point)
            .output()
            .expect("the child runs");
        assert_eq!(
            output.status.success(),
            point.is_empty(),
            "the child stops at `{point}` and only there: {output:?}"
        );
        let stdout = String::from_utf8(output.stdout).expect("the child prints text");
        let returned: Vec<RootName> = stdout
            .lines()
            .filter_map(|line| line.split_once("named ").map(|(_, name)| name))
            .map(|name| RootName::new(String::from(name)))
            .collect();
        let (store, _register) = Store::open(&root).expect("the store opens after the stop");
        assert_eq!(
            store.deref::<Labels>(pointer),
            Ok(before.clone()),
            "the root named before the child derefs after `{point}`"
        );
        assert!(
            returned
                .iter()
                .all(|name| matches!(store.roots().root(name), Maybe::Present(_))),
            "each naming that returned stands after `{point}`"
        );
        for name in store.roots().names() {
            let Maybe::Present(named) = store.roots().root(name)
            else {
                panic!("a listed root names a pointer");
            };
            assert!(
                store.deref::<Labels>(named).is_ok(),
                "the root `{name:?}` derefs after `{point}`"
            );
        }
        if point.is_empty() {
            assert_eq!(
                returned.len(),
                usize::from(CRASH_NAMINGS),
                "the child that does not stop names every root"
            );
        }
    }
}

/// How many leaves the tree of the same-store test spans at least.
const LEAVES: usize = 37_usize;

/// A record tree that a store writes opens from the same store's record plane,
/// which indexes each node as its batch appends it (#6899).
#[test]
fn a_written_tree_opens_from_the_store_that_wrote_it_6899()
{
    let root = scratch(Path::new("tree-same-store"));
    let mut records: Vec<([u8; 4], Vec<u8>)> = (0_u32 .. 20_000_u32)
        .map(|index| (index.to_le_bytes(), index.to_le_bytes().repeat(16)))
        .collect();
    records.sort_unstable();
    let refs: Vec<RecordRef<'_>> = records
        .iter()
        .map(|&(ref key, ref value)| RecordRef::new(key.as_slice(), value.as_slice()))
        .collect();
    let tree = RecordTree::build(&refs, TreeParams::current()).expect("the records build a tree");
    let leaves = tree.leaf_hashes();
    assert!(leaves.len() >= LEAVES, "{} leaves", leaves.len());
    let (store, _register) = Store::open(&root).expect("the store opens");
    store.write_tree(&tree).expect("the tree is written");
    let nodes = store.records();
    let opened = StoredRoot::open(tree.root(), tree.root_node_hash(), &nodes)
        .expect("the tree's root opens from the store that wrote it");
    assert_eq!(opened.root(), tree.root());
    for leaf in &leaves {
        let node = nodes.load(*leaf).expect("every leaf loads verified");
        assert_eq!(
            node.identity(),
            *leaf,
            "each read by name answers its own name"
        );
    }
    for leaf in &leaves {
        assert_eq!(
            nodes.load(*leaf).map(|node| node.identity()),
            Ok(*leaf),
            "a second load finds each name in the index"
        );
    }
}

/// Sixteen threads that share one store each commit a value of their own and
/// hand its naming to the register's owner. No reader sees a naming before
/// the owner drains, and after one drain the store's readers and a store
/// opened later read every root (#6899).
#[test]
fn the_namings_of_sixteen_threads_stand_after_one_drain_6899()
{
    let root = scratch(Path::new("sixteen-namers"));
    let (store, mut register) = Store::open(&root).expect("the store opens");
    let namer = register.namer();
    let start = std::sync::Barrier::new(WRITERS);
    let named: Vec<(RootName, ContentPtr)> = std::thread::scope(|scope| {
        let namers: Vec<_> = (0_u8 ..)
            .take(WRITERS)
            .map(|index| {
                let (store, namer, start) = (&store, &namer, &start);
                scope.spawn(move || {
                    let _leader = start.wait();
                    let pointer = store
                        .commit(&labels(Count(index.saturating_add(1))))
                        .expect("each thread commits its value");
                    let name = RootName::new(format!("verdict/{index:02}"));
                    namer
                        .name(name.clone(), pointer)
                        .expect("each thread hands its naming over");
                    (name, pointer)
                })
            })
            .collect();
        namers
            .into_iter()
            .map(|namer| namer.join().expect("a namer runs to its end"))
            .collect()
    });
    assert_eq!(
        store.roots().names().count(),
        0_usize,
        "no reader sees a naming before the owner drains"
    );
    register.drain().expect("the owner drains the namings");
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    for &(ref name, pointer) in &named {
        assert_eq!(
            store.roots().root(name),
            Maybe::Present(pointer),
            "the store's readers read `{name}` after the drain"
        );
        assert_eq!(
            reopened.roots().root(name),
            Maybe::Present(pointer),
            "a store opened later reads `{name}`"
        );
    }
    assert_eq!(reopened.roots().names().count(), WRITERS);
}

/// A register that serves on a thread of its own names each naming that
/// namers on other threads hand it, and returns once every namer is gone, so
/// a store opened after it reads each root (#6899).
#[test]
fn a_serving_register_names_each_naming_until_its_namers_go_6899()
{
    let root = scratch(Path::new("serving"));
    let (store, register) = Store::open(&root).expect("the store opens");
    let namer = register.namer();
    let owner = std::thread::spawn(move || register.serve());
    let start = std::sync::Barrier::new(WRITERS);
    let named: Vec<(RootName, ContentPtr)> = std::thread::scope(|scope| {
        let namers: Vec<_> = (0_u8 ..)
            .take(WRITERS)
            .map(|index| {
                let (store, namer, start) = (&store, &namer, &start);
                scope.spawn(move || {
                    let _leader = start.wait();
                    let pointer = store
                        .commit(&labels(Count(index.saturating_add(1))))
                        .expect("each thread commits its value");
                    let name = RootName::new(format!("lock/{index:02}"));
                    namer
                        .name(name.clone(), pointer)
                        .expect("each thread hands its naming over");
                    (name, pointer)
                })
            })
            .collect();
        namers
            .into_iter()
            .map(|namer| namer.join().expect("a namer runs to its end"))
            .collect()
    });
    drop(namer);
    owner
        .join()
        .expect("the owner runs to its end")
        .expect("the owner names every naming");
    let (reopened, _register) = Store::open(&root).expect("the store opens again");
    for &(ref name, pointer) in &named {
        assert_eq!(
            reopened.roots().root(name),
            Maybe::Present(pointer),
            "a store opened after the owner reads `{name}`"
        );
    }
}

/// The marker of the impl that every type takes.
struct Every;

/// The marker of the impl that a type with the trait also takes.
struct Bound;

/// A function that resolves for a type that is not `Sync` alone: a `Sync`
/// type takes both impls, so its call is ambiguous and the test does not
/// compile.
trait Unsynced<Marker>
{
    /// # Specification
    /// trivial.
    fn unsynced()
    {
    }
}

impl<Type: ?Sized> Unsynced<Every> for Type
{
}

impl<Type: ?Sized + Sync> Unsynced<Bound> for Type
{
}

/// A function that resolves for a type that is not `Clone` alone, as
/// [`Unsynced`] does for `Sync`.
trait Uncloned<Marker>
{
    /// # Specification
    /// trivial.
    fn uncloned()
    {
    }
}

impl<Type: ?Sized> Uncloned<Every> for Type
{
}

impl<Type: Clone> Uncloned<Bound> for Type
{
}

/// Compiles for a type that threads share.
///
/// # Specification
/// trivial.
const fn shared<Type>()
where
    Type: Clone + Send + Sync,
{
}

/// Compiles for a type that moves to another thread.
///
/// # Specification
/// trivial.
const fn sent<Type>()
where
    Type: Send,
{
}

/// The register is the one writer of the roots by its type: it is neither
/// `Clone` nor `Sync`, so one owner names the roots, and it moves to the
/// thread that owns it. Threads share the store and a namer (#6899).
#[test]
fn the_register_is_the_one_writer_by_its_type_6899()
{
    <Register as Unsynced<_>>::unsynced();
    <Register as Uncloned<_>>::uncloned();
    sent::<Register>();
    shared::<Namer>();
    let (store, register) =
        Store::open(&scratch(Path::new("one-writer-type"))).expect("the store opens");
    std::thread::scope(|scope| {
        let owner = scope.spawn(move || register);
        let _reader = scope.spawn(|| store.roots());
        drop(owner.join().expect("the register moves to its owner"));
    });
}
