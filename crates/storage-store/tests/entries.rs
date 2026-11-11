//! A built output as a tree of entries (#6590): it reads into the store and
//! writes out again with its bytes and modes, a second read writes nothing,
//! and an edit writes only what it changed.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the fixtures pass a stream's seed and length, a file's bytes and a count of objects"
    )
)]

use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::path::Path;
use std::path::PathBuf;

use gandr_storage_records::RecordRef;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;
use gandr_storage_store::EncodedEntry;
use gandr_storage_store::Entry;
use gandr_storage_store::EntryAddress;
use gandr_storage_store::EntryFault;
use gandr_storage_store::Output;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_store::TreeRef;

/// A fresh, empty directory for `test`, removed first if a run left it.
///
/// # Specification
/// trivial.
fn scratch(test: &Path) -> PathBuf
{
    let directory = std::env::temp_dir().join(format!(
        "gandr-storage-entries-{}-{}",
        test.display(),
        std::process::id()
    ));
    if directory.exists() {
        fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
    }
    fs::create_dir_all(&directory).expect("the scratch directory is made");
    directory
}

/// `len` bytes of a `SplitMix64` stream from `seed`.
///
/// # Specification
/// trivial.
fn stream(
    seed: u64,
    len: usize,
) -> Vec<u8>
{
    let mut state = seed;
    let mut bytes = Vec::with_capacity(len);
    while bytes.len() < len {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15_u64);
        let mut mixed = state;
        mixed = (mixed ^ (mixed >> 30_u32)).wrapping_mul(0xBF58_476D_1CE4_E5B9_u64);
        mixed = (mixed ^ (mixed >> 27_u32)).wrapping_mul(0x94D0_49BB_1331_11EB_u64);
        mixed ^= mixed >> 31_u32;
        bytes.extend_from_slice(&mixed.to_le_bytes());
    }
    bytes.truncate(len);
    bytes
}

/// A source tree of every kind of entry under `root`: a large file and an
/// executable one in a subdirectory, an empty file, an empty directory and a
/// symbolic link.
///
/// # Specification
/// trivial.
fn source(root: &Path)
{
    fs::create_dir_all(root.join("src/deep")).expect("directories");
    fs::create_dir_all(root.join("empty")).expect("an empty directory");
    fs::write(root.join("src/large.bin"), stream(1, 0x0010_0000)).expect("a large file");
    fs::write(root.join("src/deep/run.sh"), b"#!/bin/sh\necho ok\n").expect("a script");
    fs::set_permissions(
        root.join("src/deep/run.sh"),
        fs::Permissions::from_mode(0o755),
    )
    .expect("chmod");
    fs::write(root.join("README"), stream(2, 5_000)).expect("a small file");
    fs::write(root.join("nothing"), b"").expect("an empty file");
    std::os::unix::fs::symlink("src/deep/run.sh", root.join("run")).expect("a link");
}

/// Each path under `root`, relative, with its kind, its executable bit, its
/// bytes or its link target, in order.
///
/// # Specification
/// trivial.
fn listing(root: &Path) -> Vec<(PathBuf, String, Vec<u8>)>
{
    let mut rows = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(path) = pending.pop() {
        let meta = fs::symlink_metadata(&path).expect("metadata");
        let relative = path
            .strip_prefix(root)
            .expect("below the root")
            .to_path_buf();
        if meta.file_type().is_symlink() {
            let target = fs::read_link(&path)
                .expect("a link")
                .into_os_string()
                .into_encoded_bytes();
            rows.push((relative, "link".to_owned(), target));
        }
        else if meta.is_dir() {
            rows.push((relative, "directory".to_owned(), Vec::new()));
            for entry in fs::read_dir(&path).expect("a directory") {
                pending.push(entry.expect("an entry").path());
            }
        }
        else {
            let kind = if meta.permissions().mode() & 0o111 == 0 {
                "file"
            }
            else {
                "executable"
            };
            rows.push((relative, kind.to_owned(), fs::read(&path).expect("a file")));
        }
    }
    rows.sort();
    rows
}

/// The objects the store at `root` holds on disk.
///
/// # Specification
/// trivial.
fn objects(root: &Path) -> usize
{
    ["chunks", "nodes"]
        .iter()
        .map(|plane| fs::read_dir(root.join(plane)).map_or(0, Iterator::count))
        .sum()
}

#[test]
fn each_kind_of_entry_reads_back_from_its_encoding()
{
    let directory = scratch(Path::new("encoding"));
    let (store, _register) = Store::open(&directory.join("store")).expect("the store opens");
    let tree = directory.join("tree");
    source(&tree);
    let Entry::Directory { tree: listed, .. } = store.read_in(&tree).expect("the tree reads in")
    else {
        panic!("a directory reads in as a directory");
    };
    let entries = [
        Entry::Directory {
            tree: listed,
            size: 7,
        },
        Entry::File {
            blob: TreeRef::empty(),
            size: 0,
            executable: false,
        },
        Entry::File {
            blob: listed,
            size: u64::MAX,
            executable: true,
        },
        Entry::Symlink {
            target: Box::from(b"../a".as_slice()),
        },
        Entry::Symlink {
            target: Box::from([].as_slice()),
        },
    ];
    let decode = |bytes: &[u8]| Entry::decode(EncodedEntry::from(bytes));
    for entry in &entries {
        let bytes = entry.encode();
        assert_eq!(decode(bytes.as_ref()).as_ref(), Ok(entry));
        if !matches!(entry, Entry::Symlink { .. }) {
            let mut longer = bytes.as_ref().to_vec();
            longer.push(0);
            assert_eq!(
                decode(&longer),
                Err(StoreError::Entry(EntryFault::Unencoded))
            );
            assert_eq!(
                decode(bytes.as_ref().split_last().expect("nonempty").1),
                Err(StoreError::Entry(EntryFault::Unencoded))
            );
        }
    }
    assert_eq!(decode(&[]), Err(StoreError::Entry(EntryFault::Unencoded)));
    assert_eq!(decode(&[3]), Err(StoreError::Entry(EntryFault::Unencoded)));
}

#[test]
fn a_tree_writes_out_to_the_same_bytes_and_modes()
{
    let directory = scratch(Path::new("round-trip"));
    let tree = directory.join("tree");
    source(&tree);
    let root = {
        let (store, _register) = Store::open(&directory.join("store")).expect("the store opens");
        store.read_in(&tree).expect("the tree reads in")
    };
    let (reopened, _register) =
        Store::open(&directory.join("store")).expect("the store opens again");
    reopened
        .write_out(&root, &directory.join("out"))
        .expect("the tree writes out");
    assert_eq!(listing(&directory.join("out")), listing(&tree));
}

#[test]
fn a_tree_read_again_writes_no_object_and_keeps_its_address()
{
    let directory = scratch(Path::new("again"));
    let tree = directory.join("tree");
    source(&tree);
    let store_path = directory.join("store");
    let first = Store::open(&store_path)
        .expect("opens")
        .0
        .read_in(&tree)
        .expect("reads in");
    let held = objects(&store_path);
    let second = Store::open(&store_path)
        .expect("opens")
        .0
        .read_in(&tree)
        .expect("reads in");
    assert_eq!(objects(&store_path), held);
    assert_eq!(second, first);
    assert_eq!(second.address(), first.address());
}

#[test]
fn an_edit_writes_only_its_pieces_and_the_trees_above_it()
{
    let directory = scratch(Path::new("edit"));
    let tree = directory.join("tree");
    source(&tree);
    let store_path = directory.join("store");
    let before = Store::open(&store_path)
        .expect("opens")
        .0
        .read_in(&tree)
        .expect("reads in");
    let held = objects(&store_path);
    let mut bytes = fs::read(tree.join("src/large.bin")).expect("the large file");
    bytes.insert(0, b'#');
    fs::write(tree.join("src/large.bin"), &bytes).expect("the edit");
    let after = Store::open(&store_path)
        .expect("opens")
        .0
        .read_in(&tree)
        .expect("reads in");
    let written = objects(&store_path).saturating_sub(held);
    // The edit's piece, the piece after it, the large file's blob tree and
    // the two directories above it: at most two pieces and five nodes.
    assert!(
        written <= 7,
        "the edit of one byte writes {written} objects"
    );
    assert!(
        written >= 3,
        "the edit of one byte writes {written} objects"
    );
    assert_ne!(after.address(), before.address());
}

#[test]
fn a_name_that_leaves_the_directory_is_refused()
{
    let directory = scratch(Path::new("unsafe"));
    let (store, _register) = Store::open(&directory.join("store")).expect("opens");
    let file = Entry::File {
        blob: TreeRef::empty(),
        size: 0,
        executable: false,
    }
    .encode();
    for name in [b"..".as_slice(), b".", b"a/b", b""] {
        let tree = RecordTree::build(
            &[RecordRef::new(name, file.as_ref())],
            TreeParams::current(),
        )
        .expect("the tree builds");
        store.write_tree(&tree).expect("the tree writes");
        let entry = Entry::Directory {
            tree: TreeRef::of(&tree),
            size: 0,
        };
        let out = directory.join("out");
        assert_eq!(
            store.write_out(&entry, &out),
            Err(StoreError::Entry(EntryFault::Unsafe {
                name: Box::from(name)
            }))
        );
        assert!(!out.exists(), "nothing is made for {name:?}");
    }
}

#[test]
fn an_output_reads_back_with_its_references()
{
    let directory = scratch(Path::new("output"));
    let tree = directory.join("tree");
    source(&tree);
    let (store, _register) = Store::open(&directory.join("store")).expect("opens");
    let root = store.read_in(&tree).expect("reads in");
    let address = |byte: u8| EntryAddress::from([byte; 32]);
    let output = Output::new(root.clone(), vec![address(2), address(1), address(2)]);
    assert_eq!(output.references(), &[address(1), address(2)]);
    assert_eq!(output.identity(), root.address());
    let pointer = store.commit(&output).expect("the output commits");
    let reordered = Output::new(root, vec![address(1), address(2)]);
    assert_eq!(store.commit(&reordered).expect("commits"), pointer);
    assert_eq!(store.deref::<Output>(pointer), Ok(output));
}
