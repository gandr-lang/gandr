//! The store account: one row for each value that a store's roots or a
//! package's lock name, keyed by its content pointer.
//!
//! # Rows
//!
//! The name of a root gives the kind of its value: the prefix `receipt/` names
//! a receipt, `stratum/` a stratum and `export/` the export of a package. A
//! root of another name is no value of the engine and holds no row. A lock
//! records the pointer of each identity of a package, and the account reads
//! those pointers as identities. A row states where the value resides, which
//! is the content-addressable memory, the bytes of the images of its chunks,
//! their count, and the in-degree of its root chunk: the number of the
//! account's values whose closure holds that chunk, the value itself among
//! them. A value whose chunks the store refuses holds the refusal in place of
//! the counts, and it adds no chunk to an in-degree.
//!
//! The account reads the store and writes nothing to it. It opens the store
//! only where its directory stands, so it makes no directory, and it changes
//! no key.
//!
//! # Owed cells
//!
//! The commit that wrote a value comes with the provenance record of #3022,
//! and the world it stands in with the located content of #3381. The
//! location-addressable memory and its region come with #6272, and the reduct
//! with #5723. [`Owed`] names each of these cells with the number of its unit.
//!
//! # Refresh
//!
//! [`StoreAccount::refresh`] walks the closure of each value that it did not
//! read yet, once, and adds each chunk of that closure to the chunk's
//! in-degree. A query is then one lookup. A value that leaves the store's
//! names rebuilds the account, since the in-degrees keep no closure to take
//! back.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-store gives the row of the store pane: where a node
//!   resides, its bytes, its chunks, how many share it, and the cells that wait
//!   for their units.
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — background: the storage
//!   programme's chunk DAG, whose closures the account walks and whose shared
//!   chunks the in-degree counts.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::num::NonZeroU32;
use std::path::Path;

use anodized::spec;
use gandr_storage_store::ImageBytes;
use gandr_storage_store::Roots;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_values::ChunkCount;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::ContentPtr;
use quenchant_shape::shape::Maybe;

use crate::package::export::EXPORT_ROOTS;
use crate::receipts::RECEIPT_ROOTS;
use crate::strata::STRATUM_ROOTS;

/// What a value of the store is, by the name that finds it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StoredKind
{
    /// A receipt of kernel verdicts, under a root that `receipt/` opens.
    Receipt,
    /// A stratum of kept outcomes, under a root that `stratum/` opens.
    Stratum,
    /// The export of a package, under a root that `export/` opens.
    Export,
    /// The identity of a package, whose pointer a lock records.
    Identity,
}

/// A cell of every row that no layer fills yet.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Owed
{
    /// The commit that wrote the value.
    Wrote,
    /// The world that the value stands in.
    World,
    /// The location-addressable memory and the region of the value there.
    Lam,
    /// The reduct of the value and its gradient.
    Reduct,
}

impl Owed
{
    /// Each owed cell, in the order of the pane's columns.
    pub const ALL: [Self; 4] = [Self::Wrote, Self::World, Self::Lam, Self::Reduct];
}

impl From<Owed> for &'static str
{
    /// The name of the cell's column.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(owed: Owed) -> Self
    {
        match owed {
            Owed::Wrote => "wrote",
            Owed::World => "world",
            Owed::Lam => "lam",
            Owed::Reduct => "reduct",
        }
    }
}

impl From<Owed> for NonZeroU32
{
    /// The number of the issue of the unit that fills the cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(owed: Owed) -> Self
    {
        let below = match owed {
            Owed::Wrote => 3_021_u32,
            Owed::World => 3_380_u32,
            Owed::Lam => 6_271_u32,
            Owed::Reduct => 5_722_u32,
        };
        Self::MIN.saturating_add(below)
    }
}

/// How many values of an account hold a chunk in their closure.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InDegree(usize);

impl From<InDegree> for usize
{
    /// The number of values.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(degree: InDegree) -> Self
    {
        degree.0
    }
}

/// Where a value resides, in the content-addressable memory, and what it
/// takes there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Resident
{
    /// The bytes of the images of its chunks.
    pub bytes: ImageBytes,
    /// The number of its chunks.
    pub chunks: ChunkCount,
    /// The in-degree of its root chunk among the account's values.
    pub shared: InDegree,
}

/// One row of an account, borrowed from it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StoredRow<'account>
{
    /// The value's pointer, the row's key.
    pub pointer: ContentPtr,
    /// What the value is.
    pub kind: StoredKind,
    /// Where it resides, or the store's refusal of one of its chunks.
    pub residence: Result<Resident, &'account StoreError>,
}

/// What an account read of one value: its kind, and the bytes and the count
/// of its chunks, or the store's refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Read
{
    /// What the value is.
    kind: StoredKind,
    /// The bytes and the count of its chunks, or the store's refusal.
    residence: Result<(ImageBytes, ChunkCount), StoreError>,
}

/// The rows of the values of one store, and the in-degree of each chunk that
/// their closures hold.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StoreAccount
{
    /// What the account read of each value, by its pointer.
    read: BTreeMap<ContentPtr, Read>,
    /// The in-degree of each chunk that a closure of a value holds.
    holders: BTreeMap<ChunkDigest, InDegree>,
}

impl StoreAccount
{
    /// Refresh the account from the store at `directory`, the pointers in
    /// `identities` read as identities.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when no directory stands at `directory`, the account holds no
    ///   row, and nothing is made. Otherwise, on success, the account is what
    ///   [`StoreAccount::refresh`] makes of the store opened there. On a
    ///   failure, the account is as it was.
    /// - provides: the reading of the store under a data directory, for a
    ///   reader that keeps no store open between readings.
    /// - fails: [`StoreError`] when the store at `directory` does not open.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`StoreAccount::refresh`], and a missing directory
    ///   reads as no row and stays missing.
    /// - witness: `stored::tests::the_account_reads_each_value_s_chunks_and_the_in_degree_of_its_root_6296`
    #[inline]
    #[spec(captures: [before = self.read.len()],
        ensures: |ret| ret.is_ok() || self.read.len() == before)]
    pub fn read(
        &mut self,
        directory: &Path,
        identities: &BTreeSet<ContentPtr>,
    ) -> Result<(), StoreError>
    {
        if !directory.is_dir() {
            *self = Self::default();
            return Ok(());
        }
        let store = Store::open(directory)?;
        self.refresh(&store, identities);
        Ok(())
    }

    /// Refresh the account from `store`, the pointers in `identities` read as
    /// identities.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the account holds one row for each pointer that a root of a
    ///   receipt, a stratum or an export names in `store`, and for each pointer
    ///   of `identities`; a pointer named twice takes the kind of its first
    ///   name, the roots before the identities. Each row holds the bytes and
    ///   the count of the chunks of the closure [`Store::closure`] reads, or
    ///   its refusal. The in-degree of each chunk is the number of rows whose
    ///   closure holds it. The store is not written.
    /// - provides: the account that a query reads by one lookup.
    /// - fails: never; a refused closure is its row's refusal.
    /// - panics: none.
    /// - intension: the closure of each pointer that the account did not hold
    ///   is walked once; a pointer that leaves the store's names rebuilds the
    ///   account, one walk of each value.
    /// - executable: none — the clauses quantify over every row, and a check
    ///   that walks the rows costs what the refresh does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three values under three kinds of root and one
    ///   identity, one value nesting another whole and one sharing a run of its
    ///   chunks, read their chunk counts and the in-degrees 2, 1, 1 and 1; a
    ///   chunk changed on disk is its row's refusal; a value that leaves the
    ///   names leaves the rows; the store's files do not change.
    /// - witness: `stored::tests::the_account_reads_each_value_s_chunks_and_the_in_degree_of_its_root_6296`
    #[inline]
    pub fn refresh(
        &mut self,
        store: &Store,
        identities: &BTreeSet<ContentPtr>,
    )
    {
        let named = named(store.roots(), identities);
        if self.read.keys().any(|pointer| !named.contains_key(pointer)) {
            *self = Self::default();
        }
        for (pointer, kind) in named {
            if self.read.contains_key(&pointer) {
                continue;
            }
            let residence = store.closure(pointer).map(|residence| {
                for &digest in residence.closure().digests() {
                    let held = self.holders.entry(digest).or_default();
                    *held = InDegree(held.0.saturating_add(1));
                }
                (residence.bytes(), residence.closure().chunk_count())
            });
            drop(self.read.insert(pointer, Read { kind, residence }));
        }
    }

    /// The row of the value at `pointer`, when the account holds one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn row(
        &self,
        pointer: ContentPtr,
    ) -> Option<StoredRow<'_>>
    {
        self.read
            .get(&pointer)
            .map(|read| self.row_of(pointer, read))
    }

    /// Each row, in the order of the pointers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn rows(&self) -> impl Iterator<Item = StoredRow<'_>>
    {
        self.read
            .iter()
            .map(|(&pointer, read)| self.row_of(pointer, read))
    }

    /// The row of `read`, the value at `pointer`, with the in-degree of its
    /// root chunk.
    ///
    /// # Specification
    /// trivial.
    fn row_of<'account>(
        &'account self,
        pointer: ContentPtr,
        read: &'account Read,
    ) -> StoredRow<'account>
    {
        StoredRow {
            pointer,
            kind: read.kind,
            residence: read.residence.as_ref().map(|&(bytes, chunks)| Resident {
                bytes,
                chunks,
                shared: self
                    .holders
                    .get(&pointer.digest())
                    .copied()
                    .unwrap_or_default(),
            }),
        }
    }
}

/// The kind of each value that `roots` or `identities` name, by its pointer:
/// a pointer named twice takes its first name's kind, the roots first.
///
/// # Specification
/// trivial.
fn named(
    roots: &Roots,
    identities: &BTreeSet<ContentPtr>,
) -> BTreeMap<ContentPtr, StoredKind>
{
    let mut named = BTreeMap::new();
    for name in roots.names() {
        let text: &str = name.as_ref();
        let kind = if text.starts_with(RECEIPT_ROOTS) {
            StoredKind::Receipt
        }
        else if text.starts_with(STRATUM_ROOTS) {
            StoredKind::Stratum
        }
        else if text.starts_with(EXPORT_ROOTS) {
            StoredKind::Export
        }
        else {
            continue;
        };
        if let Maybe::Present(pointer) = roots.root(name) {
            let _first = named.entry(pointer).or_insert(kind);
        }
    }
    for &pointer in identities {
        let _first = named.entry(pointer).or_insert(StoredKind::Identity);
    }
    named
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::path::Path;
    use std::path::PathBuf;
    use std::time::SystemTime;

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
    use gandr_storage_values::ContentPtr;
    use gandr_storage_values::TokenBytes;
    use gandr_storage_values::TokenReader;
    use gandr_storage_values::TokenSink;
    use gandr_storage_values::ValueError;

    use super::StoreAccount;
    use super::StoredKind;

    /// The tag a list of labels opens with.
    const LIST: u8 = 0_u8;

    /// The tag each label opens with.
    const LABEL: u8 = 1_u8;

    /// The tag a nest opens with.
    const NEST: u8 = 2_u8;

    /// The codec both test values are written in.
    ///
    /// # Specification
    /// trivial.
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(0x7E57_u16), CodecVersion::from(1_u16))
    }

    /// A list of byte strings: a count, then one constructor for each label,
    /// so a long list is cut into several chunks.
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
                labels.push(reader.read_bytes()?.as_ref().to_vec());
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
            codec()
        }
    }

    /// One constructor around a list: its pointer when written, the list when
    /// read.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Nest
    {
        /// The pointer of a list already committed.
        Pointer(ContentPtr),
        /// The list itself.
        Value(Labels),
    }

    impl CanonicalValue for Nest
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
            sink.open(ConstructorTag::from(NEST))?;
            match *self {
                Self::Pointer(pointer) => sink.child_pointer(pointer)?,
                Self::Value(ref labels) => labels.emit_tokens(sink)?,
            }
            sink.close()
        }

        /// # Specification
        /// trivial.
        fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
        {
            let _nest = reader.read_tag()?;
            let labels = Labels::decode_tokens(reader)?;
            reader.read_close()?;
            Ok(Self::Value(labels))
        }
    }

    impl Stored for Nest
    {
        /// # Specification
        /// trivial.
        fn codec() -> CodecIdentity
        {
            codec()
        }
    }

    /// A number of labels.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Count(u8);

    /// The first `count` labels, each distinct.
    ///
    /// # Specification
    /// trivial.
    fn labels(Count(count): Count) -> Labels
    {
        Labels(
            (0 .. count)
                .map(|index| alloc::vec![index; usize::from(index)])
                .collect(),
        )
    }

    /// When a file was last written, and its length.
    #[derive(Debug, Eq, PartialEq)]
    struct Stamp
    {
        /// Its length in bytes.
        length: u64,
        /// When it was last written.
        written: SystemTime,
    }

    /// Each file under `directory`, with its stamp.
    ///
    /// # Specification
    /// trivial.
    fn files(directory: &Path) -> BTreeMap<PathBuf, Stamp>
    {
        let mut files = BTreeMap::new();
        let mut pending = Vec::from([directory.to_path_buf()]);
        while let Some(next) = pending.pop() {
            for entry in std::fs::read_dir(&next).expect("the directory lists") {
                let path = entry.expect("an entry reads").path();
                let metadata = std::fs::metadata(&path).expect("an entry is read");
                if metadata.is_dir() {
                    pending.push(path);
                }
                else {
                    let written = metadata.modified().expect("a file has a time");
                    let replaced = files.insert(path, Stamp {
                        length: metadata.len(),
                        written,
                    });
                    assert!(replaced.is_none(), "each file is listed once");
                }
            }
        }
        files
    }

    /// What a test reads of a row: its kind, its chunk count and the
    /// in-degree of its root chunk.
    #[derive(Debug, Eq, PartialEq)]
    struct Counted
    {
        /// What the value is.
        kind: StoredKind,
        /// The number of its chunks.
        chunks: usize,
        /// The in-degree of its root chunk.
        shared: usize,
    }

    /// What the row at `pointer` counts.
    ///
    /// # Specification
    /// trivial.
    fn counted(
        account: &StoreAccount,
        pointer: ContentPtr,
    ) -> Counted
    {
        let row = account.row(pointer).expect("the value has a row");
        let resident = row.residence.expect("the value resides in its chunks");
        Counted {
            kind: row.kind,
            chunks: usize::from(resident.chunks),
            shared: usize::from(resident.shared),
        }
    }

    /// Sixty labels (A), ninety labels whose first sixty are A's (B) and A
    /// inside one more constructor (C), under three kinds of root, beside one
    /// list that a lock records (D). A's root chunk has the in-degree 2, as C
    /// holds A whole; B shares a run of A's chunks and has the in-degree 1. A
    /// chunk changed on disk is its row's refusal, and a value that leaves
    /// the names leaves the rows. The account writes nothing and makes no
    /// directory (#6296).
    #[test]
    fn the_account_reads_each_value_s_chunks_and_the_in_degree_of_its_root_6296()
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-surface-dispatcher-stored-{}",
            std::process::id()
        ));
        if directory.exists() {
            std::fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
        }
        let mut store = Store::open(&directory).expect("the store opens");
        let a = store.commit(&labels(Count(60))).expect("A commits");
        let b = store.commit(&labels(Count(90))).expect("B commits");
        let c = store.commit(&Nest::Pointer(a)).expect("C commits");
        let d = store.commit(&labels(Count(3))).expect("D commits");
        for (name, pointer) in [
            ("export/a", a),
            ("stratum/1/9/5/b", b),
            ("receipt/c", c),
            ("elsewhere/d", d),
        ] {
            store
                .set_root(RootName::new(String::from(name)), pointer)
                .expect("the root is named");
        }
        drop(store);
        let identities = BTreeSet::from([d]);
        let before = files(&directory);
        let mut account = StoreAccount::default();
        account
            .read(&directory, &identities)
            .expect("the store reads");
        assert_eq!(files(&directory), before, "the account writes nothing");
        assert_eq!(counted(&account, a), Counted {
            kind: StoredKind::Export,
            chunks: 14,
            shared: 2
        });
        assert_eq!(counted(&account, b), Counted {
            kind: StoredKind::Stratum,
            chunks: 22,
            shared: 1
        });
        assert_eq!(counted(&account, c), Counted {
            kind: StoredKind::Receipt,
            chunks: 15,
            shared: 1
        });
        assert_eq!(counted(&account, d).kind, StoredKind::Identity);
        assert_eq!(
            account.rows().count(),
            4,
            "a root of another name has no row"
        );
        let shared = Store::open(&directory)
            .expect("the store opens")
            .closure(b)
            .expect("B resides")
            .closure()
            .digests()
            .intersection(
                Store::open(&directory)
                    .expect("the store opens")
                    .closure(a)
                    .expect("A resides")
                    .closure()
                    .digests(),
            )
            .count();
        assert_eq!(shared, 13, "B shares a run of A's chunks");

        let file = directory.join("chunks").join(d.digest().to_string());
        let mut bytes = std::fs::read(&file).expect("D's chunk reads");
        let last = bytes.last_mut().expect("a chunk has bytes");
        *last ^= 0xFF_u8;
        std::fs::write(&file, &bytes).expect("D's chunk is changed");
        let mut fresh = StoreAccount::default();
        fresh
            .read(&directory, &identities)
            .expect("the store reads");
        assert!(
            matches!(
                fresh.row(d).map(|row| row.residence),
                Some(Err(&StoreError::Value(ValueError::DigestMismatch { expected, .. }))) if expected == d.digest()
            ),
            "a changed chunk is its row's refusal"
        );
        assert_eq!(counted(&fresh, a), Counted {
            kind: StoredKind::Export,
            chunks: 14,
            shared: 2
        });

        Store::open(&directory)
            .expect("the store opens")
            .set_root(RootName::new(String::from("export/a")), b)
            .expect("the root names B");
        account
            .read(&directory, &BTreeSet::new())
            .expect("the store reads");
        assert!(
            account.row(a).is_none(),
            "a value that leaves the names leaves the rows"
        );
        assert!(
            account.row(d).is_none(),
            "an identity no lock records has no row"
        );
        assert_eq!(counted(&account, b), Counted {
            kind: StoredKind::Export,
            chunks: 22,
            shared: 1
        });
        assert_eq!(counted(&account, c), Counted {
            kind: StoredKind::Receipt,
            chunks: 15,
            shared: 1
        });
        assert_eq!(account.rows().count(), 2, "B and C are left");

        let missing = directory.join("missing");
        let mut none = StoreAccount::default();
        none.read(&missing, &identities)
            .expect("a missing store reads");
        assert_eq!(none.rows().count(), 0, "a missing store holds no row");
        assert!(!missing.exists(), "the account makes no directory");
        std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    }
}
