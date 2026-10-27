//! The store's contract: each plane and the roots read back from disk after
//! reopening, and bytes changed on disk are refused.

use std::path::Path;
use std::path::PathBuf;

use gandr_storage_records::BlockStore as _;
use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::StoredRoot;
use gandr_storage_records::TreeParams;
use gandr_storage_store::ContentPtr;
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

/// A missing root and its two plane directories are made on opening.
#[test]
fn a_missing_root_directory_is_made_on_opening()
{
    let root = scratch(Path::new("made"))
        .join("data")
        .join("gandr")
        .join("store");
    let store = Store::open(&root).expect("a missing root is made");
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

/// A value cut into several chunks is written as one file per chunk, derefs
/// back equal from a store opened later, and commits again to the same
/// pointer without writing another file.
#[test]
fn a_committed_value_derefs_back_after_reopening()
{
    let root = scratch(Path::new("committed"));
    let value = labels(Count(120));
    let pointer = {
        let mut store = Store::open(&root).expect("the store opens");
        let pointer = store.commit(&value).expect("the value commits");
        let back: Labels = store
            .deref(pointer)
            .expect("the value derefs where it was committed");
        assert_eq!(back, value);
        pointer
    };
    let written = files(&root.join("chunks"));
    assert!(
        written.len() > 1,
        "a long list is cut into several chunks, each its own file: {written:?}"
    );
    assert!(
        written.contains(&root.join("chunks").join(pointer.digest().to_string())),
        "the root chunk is the file its digest names"
    );
    let mut reopened = Store::open(&root).expect("the store opens again");
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
        files(&root.join("chunks")),
        written,
        "and writes no other chunk"
    );
}

/// A chunk whose file is changed on disk is refused by its digest when the
/// value is read back, and a pointer the store never committed is unknown.
#[test]
fn a_chunk_changed_on_disk_is_refused_by_its_digest()
{
    let root = scratch(Path::new("changed"));
    let pointer = Store::open(&root)
        .expect("the store opens")
        .commit(&labels(Count(3)))
        .expect("the value commits");
    let file = root.join("chunks").join(pointer.digest().to_string());
    let mut bytes = std::fs::read(&file).expect("the chunk's file reads");
    let last = bytes.last_mut().expect("a chunk has bytes");
    *last ^= 0xFF_u8;
    std::fs::write(&file, &bytes).expect("the chunk's file is changed");
    let reopened = Store::open(&root).expect("the store opens again");
    assert!(
        matches!(
            reopened.deref::<Labels>(pointer),
            Err(StoreError::Value(ValueError::DigestMismatch { expected, .. })) if expected == pointer.digest()
        ),
        "the changed chunk is refused by its digest"
    );
    let other = Store::open(&scratch(Path::new("changed-other")))
        .expect("another store opens")
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
        .write_tree(&tree)
        .expect("the tree is written");
    let reopened = Store::open(&root).expect("the store opens again");
    let opened = StoredRoot::open(tree.root(), tree.root_node_hash(), reopened.records())
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
        let mut store = Store::open(&root).expect("the store opens");
        let first = store.commit(&labels(Count(1))).expect("a value commits");
        let second = store.commit(&labels(Count(2))).expect("a value commits");
        let third = store.commit(&labels(Count(5))).expect("a value commits");
        store
            .set_root(lock.clone(), first)
            .expect("the first root is set");
        store
            .set_root(verdict.clone(), second)
            .expect("the second root is set");
        assert_eq!(store.roots().root(&lock), Maybe::Present(first));
        (first, second, third)
    };
    let mut reopened = Store::open(&root).expect("the store opens again");
    assert_eq!(reopened.roots().root(&lock), Maybe::Present(first));
    assert_eq!(reopened.roots().root(&verdict), Maybe::Present(second));
    reopened
        .set_root(lock.clone(), third)
        .expect("the first root is set again");
    let again = Store::open(&root).expect("the store opens a third time");
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
    let mut left = Store::open(&root).expect("the first store opens");
    let mut right = Store::open(&root).expect("the second store opens");
    let one = left.commit(&labels(Count(1))).expect("a value commits");
    let two = right.commit(&labels(Count(2))).expect("a value commits");
    let first = RootName::new(String::from("lock/first"));
    let second = RootName::new(String::from("lock/second"));
    left.set_root(first.clone(), one)
        .expect("the first store sets its root");
    right
        .set_root(second.clone(), two)
        .expect("the second store sets its root");
    assert_eq!(
        right.roots().root(&first),
        Maybe::Present(one),
        "the second store reads the first's root as it changes its own"
    );
    let after = Store::open(&root).expect("a third store opens");
    assert_eq!(after.roots().root(&first), Maybe::Present(one));
    assert_eq!(after.roots().root(&second), Maybe::Present(two));
}

/// A roots file naming no node is refused by name on opening.
#[test]
fn a_roots_file_naming_no_node_is_refused_on_opening()
{
    let root = scratch(Path::new("unrooted"));
    drop(Store::open(&root).expect("the store opens"));
    std::fs::write(root.join("roots"), "not a node\n").expect("the roots file is written");
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
