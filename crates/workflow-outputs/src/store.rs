//! The store of outputs: one file for each value, named by its key.
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
}

/// A kind of output, by the name that its directory in the store has.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Kind(pub &'static str);

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
        let place = self.place(kind, key);
        let Some(directory) = place.parent()
        else {
            return Err(io::Error::other("a place of the store has no directory"));
        };
        fs::create_dir_all(directory)?;
        let mut partial = place.clone().into_os_string();
        partial.push(format!(".{}.partial", std::process::id()));
        fs::write(&partial, value)?;
        fs::rename(&partial, &place)
    }
}

#[cfg(test)]
mod tests
{
    use super::Digest;
    use super::Kind;
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
}
