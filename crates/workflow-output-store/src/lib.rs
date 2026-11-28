//! **The store of outputs**: one file for each value of a program that the
//! tree does not hold, named by its key.
//!
//! The key of a value is the BLAKE3 digest of two digests: the tool and the
//! input. The tool is the git tree identifier of each package that computes
//! the kind, with the root manifest, the lock and the toolchain file. The
//! input is the git object identifier of the source that the value reads.
//! Two trees with one tool and one source have one value, so a run computes
//! each value one time.
//!
//! A value is written to a file beside its place and renamed into it, so a
//! reader sees no part of a value and two writers need no lock: both write
//! the same bytes. A value is smaller than a page, so a reader reads it with
//! one `read`: a map takes as many system calls and a page of address space.
//!
//! The store is a cache. A run with an empty store computes each value
//! again, and a deleted file costs one computation.
//!
//! The store holds one list for each kind and each git tree that a run
//! computed: each value of the tree with its key, its input and its name.
//! The list is a value of the kind, named by the digest of its bytes, and a
//! file named by the tree holds that digest. A reader of a tree thus needs no
//! key of the tool that computed the tree.
//!
//! A test can give a value of a kind that only a test computes ([`given`]).
//! The test writes the value to the store, and an entry with its name to the
//! directory of its run, which the run of the tests reads into a list.

pub mod given;

use core::fmt::Write as _;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;

/// The digest of a tool or of a key: 32 bytes of BLAKE3.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Digest(pub [u8; 32]);

impl Digest
{
    /// The digest of the parts `parts`, each with its length before it, so
    /// two lists of parts that join to one text have two digests.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of_parts<'part, Parts>(parts: Parts) -> Self
    where
        Parts: IntoIterator<Item = &'part [u8]>,
    {
        let mut hasher = blake3::Hasher::new();
        for part in parts {
            let _hashed =
                hasher.update(&u64::try_from(part.len()).unwrap_or(u64::MAX).to_le_bytes());
            let _hashed = hasher.update(part);
        }
        Self(*hasher.finalize().as_bytes())
    }

    /// The digest in 64 hexadecimal digits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn hex(&self) -> String
    {
        blake3::Hash::from_bytes(self.0).to_hex().to_string()
    }

    /// The digest that the 64 hexadecimal digits `hex` write, or `None` when
    /// `hex` is no such text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of_hex(hex: &str) -> Option<Self>
    {
        blake3::Hash::from_hex(hex)
            .ok()
            .map(|hash| Self(*hash.as_bytes()))
    }
}

/// A kind of output, by the name that its directory in the store has.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Kind(pub &'static str);

/// One value of a tree, as the list of the tree holds it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Listed
{
    /// The key of the value.
    pub key: Digest,
    /// The git object identifier of the input of the value.
    pub object: String,
    /// The name of the source.
    pub name: String,
}

/// The store of outputs, below one directory.
#[derive(Clone, Debug)]
pub struct Store
{
    /// The directory that holds a directory for each kind.
    root: PathBuf,
}

impl Store
{
    /// The store below `root`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(root: PathBuf) -> Self
    {
        Self { root }
    }

    /// The store that the environment names in `GANDR_OUTPUT_STORE`, or
    /// `target/outputs` below the workspace root `workspace`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn asked(workspace: &Path) -> Self
    {
        std::env::var_os("GANDR_OUTPUT_STORE").map_or_else(
            || Self::at(workspace.join("target/outputs")),
            |root| Self::at(PathBuf::from(root)),
        )
    }

    /// The directory of the store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> &Path
    {
        &self.root
    }

    /// The file of the value of `kind` at `key`: the directory of the kind,
    /// a directory named by the first two digits of the key, and the key.
    ///
    /// # Specification
    /// - ensures: the file is below the directory of the store.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two keys give two files, and a key gives one file in
    ///   each run.
    /// - witness: `store::tests::a_value_reads_as_it_was_written`
    #[spec(ensures: |ret| ret.starts_with(&self.root))]
    #[inline]
    #[must_use]
    pub fn place(
        &self,
        kind: Kind,
        key: &Digest,
    ) -> PathBuf
    {
        let hex = key.hex();
        let fan = hex.get(.. 2).unwrap_or_default();
        self.root.join(kind.0).join(fan).join(&hex)
    }

    /// The value of `kind` at `key`, or `None` when the store does not hold
    /// it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A file of the store that exists and cannot be read.
    #[inline]
    pub fn get(
        &self,
        kind: Kind,
        key: &Digest,
    ) -> io::Result<Option<Vec<u8>>>
    {
        match fs::read(self.place(kind, key)) {
            Ok(value) => Ok(Some(value)),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// Writes `value` as the value of `kind` at `key`: to a file beside its
    /// place, named by the process, then renamed into its place.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A directory or a file of the store that cannot be written.
    #[inline]
    pub fn put(
        &self,
        kind: Kind,
        key: &Digest,
        value: &[u8],
    ) -> io::Result<()>
    {
        write_whole(&self.place(kind, key), value)
    }

    /// The file that holds the digest of the list of `kind` for the git tree
    /// `tree`.
    ///
    /// # Specification
    /// trivial.
    fn pointer(
        &self,
        kind: Kind,
        tree: &str,
    ) -> PathBuf
    {
        self.root.join(kind.0).join("trees").join(tree)
    }

    /// Writes `entries` as the list of the values of `kind` for the git tree
    /// `tree`: one line for each entry, with its key, its input and its
    /// name, and a tab between two fields.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A directory or a file of the store that cannot be written.
    #[inline]
    pub fn list(
        &self,
        kind: Kind,
        tree: &str,
        entries: &[Listed],
    ) -> io::Result<()>
    {
        let mut text = String::new();
        for entry in entries {
            let _written = writeln!(
                text,
                "{}\t{}\t{}",
                entry.key.hex(),
                entry.object,
                entry.name
            );
        }
        let key = Digest::of_parts([b"list".as_slice(), text.as_bytes()]);
        self.put(kind, &key, text.as_bytes())?;
        write_whole(&self.pointer(kind, tree), key.hex().as_bytes())
    }

    /// The list of the values of `kind` for the git tree `tree`, or `None`
    /// when the store holds no list of the tree that it can read.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A file of the store that exists and cannot be read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list reads as it was written, and a tree with no
    ///   list reads as none.
    /// - witness: `store::tests::a_list_reads_as_it_was_written`
    #[inline]
    pub fn listed(
        &self,
        kind: Kind,
        tree: &str,
    ) -> io::Result<Option<Vec<Listed>>>
    {
        let hex = match fs::read_to_string(self.pointer(kind, tree)) {
            Ok(hex) => hex,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error),
        };
        let Some(key) = Digest::of_hex(hex.trim())
        else {
            return Ok(None);
        };
        let Some(bytes) = self.get(kind, &key)?
        else {
            return Ok(None);
        };
        let Ok(text) = String::from_utf8(bytes)
        else {
            return Ok(None);
        };
        Ok(text
            .lines()
            .map(|line| {
                let mut fields = line.splitn(3, '\t');
                let key = Digest::of_hex(fields.next()?)?;
                let object = fields.next()?.to_owned();
                let name = fields.next()?.to_owned();
                Some(Listed { key, object, name })
            })
            .collect())
    }
}

/// Writes `bytes` to a file beside `place`, named by the process, then
/// renames it into `place`, so a reader sees no part of the file.
///
/// # Specification
/// trivial.
///
/// # Errors
/// A directory or a file that cannot be written.
pub(crate) fn write_whole(
    place: &Path,
    bytes: &[u8],
) -> io::Result<()>
{
    let Some(directory) = place.parent()
    else {
        return Err(io::Error::other("a place of the store has no directory"));
    };
    fs::create_dir_all(directory)?;
    let mut partial = place.to_path_buf().into_os_string();
    partial.push(format!(".{}.partial", std::process::id()));
    fs::write(&partial, bytes)?;
    fs::rename(&partial, place)
}

#[cfg(test)]
mod tests
{
    use super::Digest;
    use super::Kind;
    use super::Listed;
    use super::Store;

    /// A value reads as it was written, a key that the store does not hold
    /// reads as none, and two lists of parts that join to one text give two
    /// digests.
    #[test]
    fn a_value_reads_as_it_was_written()
    {
        let root = std::env::temp_dir().join(format!("gandr-outputs-{}", std::process::id()));
        let store = Store::at(root.clone());
        let kind = Kind("recovery");
        let key = Digest::of_parts([b"tool".as_slice(), b"input".as_slice()]);
        let other = Digest::of_parts([b"toolin".as_slice(), b"put".as_slice()]);
        assert_ne!(key, other);
        assert_eq!(store.get(kind, &key).expect("the store reads"), None);
        store
            .put(kind, &key, b"W\t0\t1\tf\n")
            .expect("the store writes");
        assert_eq!(
            store.get(kind, &key).expect("the store reads"),
            Some(b"W\t0\t1\tf\n".to_vec())
        );
        assert_eq!(store.get(kind, &other).expect("the store reads"), None);
        std::fs::remove_dir_all(root).expect("the store is removed");
    }

    /// A list reads as it was written, a tree with no list reads as none,
    /// and a list of one kind is no list of another kind.
    #[test]
    fn a_list_reads_as_it_was_written()
    {
        let root = std::env::temp_dir().join(format!("gandr-outputs-list-{}", std::process::id()));
        let store = Store::at(root.clone());
        let kind = Kind("recovery");
        let tree = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";
        let entries = vec![
            Listed {
                key: Digest::of_parts([b"first".as_slice()]),
                object: String::from("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"),
                name: String::from("fixture/model/circle.gandr"),
            },
            Listed {
                key: Digest::of_parts([b"second".as_slice()]),
                object: String::from("8b137891791fe96927ad78e64b0aad7bded08bdc"),
                name: String::from("strict/a name with a space.gandr"),
            },
        ];
        assert_eq!(store.listed(kind, tree).expect("the store reads"), None);
        store.list(kind, tree, &entries).expect("the store writes");
        assert_eq!(
            store.listed(kind, tree).expect("the store reads"),
            Some(entries)
        );
        assert_eq!(
            store.listed(Kind("roles"), tree).expect("the store reads"),
            None
        );
        std::fs::remove_dir_all(root).expect("the store is removed");
    }
}
