//! The reader: every source a verb reads, read once per identity.
//!
//! # Read once, buffered below a measured crossover
//!
//! A [`Reader`] holds each source it has read under the path it was asked for,
//! beside the file's identity: its length, its modification time and, on
//! unix, its device and inode. Asked again, it answers the held source when
//! the identity is unchanged, and reads the file again when it changed. A walk
//! or a script holds one reader, so an invocation, which runs one verb, reads
//! through one.
//!
//! **Buffered by default; mapped at or above the crossover.** A file below
//! [`Crossover::MAPPED`] is read into one owned buffer; a file at or above it
//! is mapped read-only. The premise was the reverse, mapping by default with
//! a buffered read as the measured exception, and it was measured: over the
//! corpus, 455 files of about 1.1 KB, a mapping read took 750 µs on one thread
//! against `read_to_string`'s 376 µs, and 2,372 µs on 32 threads against
//! 174 µs, with the same number of system calls. Page faults and `munmap`'s
//! TLB shootdowns carry the loss. A single file maps faster from 1 MiB: 27 µs
//! against 35 µs there, 3.7 ms against 8.6 ms at 128 MiB. The crossover is the
//! linux host's measured 1 MiB until the second host's measurement moves it.
//! It reverses to mapping by default on a host where mapping corpus-sized
//! files measures no slower.
//!
//! **The mapping is `memmap2`'s.** It is the ecosystem's standard mapping
//! crate, used directly by over two thousand crates, with no required
//! dependency beyond `libc` on unix and no default feature. Its one advisory
//! (RUSTSEC-2026-0186, an unchecked range in the advise and flush calls this
//! reader never makes) was fixed two days after it was reported. The
//! alternatives were these:
//!
//! - _The raw call, through `libc` or `rustix`._ Both are in the graph, and the
//!   emitter maps its executable regions through `libc`. The length, the
//!   unmapping, the empty file and each platform's call would be the reader's
//!   own unsafe code. Reversal: one wrapper that the emitter and the reader
//!   share.
//! - _[`mmap-rs`](https://crates.io/crates/mmap-rs)._ A wider surface
//!   (anonymous, executable and locked mappings) and two orders of magnitude
//!   fewer users. Reversal: a need for the mappings it adds.
//!
//! The choice of `memmap2` reverses on an advisory against a call the reader
//! makes that no release fixes, or an unmaintained mark.
//!
//! **A mapped file is one no gandr verb writes.** A mapping's bytes change if
//! the file under it is rewritten in place, and a truncated file faults the
//! reader that touches the lost pages. No verb that writes a source reads it
//! through a reader: the formatter reads its own until its rung brings it here
//! and writes through a replacement then. Another process rewriting a mapped
//! file in place is the hazard every mapped reader accepts.

use alloc::sync::Arc;
use std::collections::HashMap;
use std::fs::File;
use std::fs::Metadata;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::SystemTime;

use anodized::spec;
use gandr_surface_syntax::SourceText;

/// The size, in bytes, at and above which the reader maps a file.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Crossover(u64);

impl Crossover
{
    /// The linux host's measured crossover, 1 MiB.
    const MAPPED: Self = Self(1 << 20);
}

/// What tells one state of a file from another without reading it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Identity
{
    /// Its length in bytes.
    len: u64,
    /// When it was last modified, where the host records it.
    modified: Option<SystemTime>,
    /// Its device and inode.
    #[cfg(unix)]
    node: (u64, u64),
}

impl Identity
{
    /// The identity `metadata` gives.
    ///
    /// # Specification
    /// trivial.
    fn of(metadata: &Metadata) -> Self
    {
        Self {
            len: metadata.len(),
            modified: metadata.modified().ok(),
            #[cfg(unix)]
            node: (
                std::os::unix::fs::MetadataExt::dev(metadata),
                std::os::unix::fs::MetadataExt::ino(metadata),
            ),
        }
    }
}

/// A source's text, held once and shared by every holder.
#[repr(transparent)]
#[derive(Clone, Debug)]
pub struct Read(Arc<Held>);

/// Where a source's text lives.
#[derive(Debug)]
enum Held
{
    /// An owned buffer, for a file below the crossover.
    Buffered(Box<str>),
    /// A read-only mapping whose bytes were checked as UTF-8 when mapped.
    Mapped(memmap2::Mmap),
}

impl Read
{
    /// The source's text.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn text(&self) -> SourceText<'_>
    {
        SourceText::from(match *self.0 {
            Held::Buffered(ref text) => &**text,
            // SAFETY: `Reader::read` checked these bytes as UTF-8 when it
            // mapped them, and the mapping is read-only; the module docs state
            // the one way they change under it, a rewrite in place by another
            // process.
            Held::Mapped(ref map) => unsafe { core::str::from_utf8_unchecked(map) },
        })
    }
}

/// The sources one invocation has read, each held under its path beside the
/// identity it was read at.
///
/// # Specification
/// - provides: one read per state of a file, and its text shared by every
///   holder.
/// - panics: none.
/// - executable: none — the answers are the file system's.
///
/// # Adequacy
/// - hypothesis: L3 — a file asked for twice unchanged is read once, a
///   rewritten one again, and a mapped file reads as the buffered one.
/// - witness: `reader::tests::an_unchanged_file_is_read_once`
/// - witness: `reader::tests::a_rewritten_file_is_read_again`
/// - witness: `reader::tests::a_file_at_the_crossover_is_mapped_as_it_reads`
#[derive(Debug)]
pub struct Reader
{
    /// The size at and above which a file is mapped.
    crossover: Crossover,
    /// Each source read, under the path it was asked for.
    held: Mutex<HashMap<PathBuf, (Identity, Read)>>,
}

impl Default for Reader
{
    /// As [`Reader::new`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl Reader
{
    /// A reader that has read nothing, mapping at [`Crossover::MAPPED`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::mapping_from(Crossover::MAPPED)
    }

    /// A reader that has read nothing, mapping from `crossover`.
    ///
    /// # Specification
    /// trivial.
    fn mapping_from(crossover: Crossover) -> Self
    {
        Self {
            crossover,
            held: Mutex::new(HashMap::new()),
        }
    }

    /// The text of the file at `path`, read now unless the reader holds it at
    /// the file's present identity.
    ///
    /// # Specification
    /// - requires: nothing; a canonical `path` gives a file one entry.
    /// - ensures: the file's complete text, as `std::fs::read_to_string` reads
    ///   it. It is the held text when the file's length, modification time and,
    ///   on unix, device and inode are those it was read at, and is read and
    ///   held otherwise: into a buffer below the crossover, mapped at or above
    ///   it.
    /// - fails: the I/O error opening, inspecting or reading the file met, a
    ///   directory among them, and `InvalidData` for text that is not UTF-8.
    /// - panics: none.
    ///
    /// # Errors
    /// The I/O error the file met, or `InvalidData` for text that is not
    /// UTF-8.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Reader`].
    /// - witness: `reader::tests::an_unchanged_file_is_read_once`
    /// - witness: `reader::tests::a_rewritten_file_is_read_again`
    /// - witness: `reader::tests::a_file_at_the_crossover_is_mapped_as_it_reads`
    #[spec(ensures: |ret| ret.as_ref().is_err() || self.held.lock().unwrap_or_else(PoisonError::into_inner).contains_key(path))]
    pub fn read(
        &self,
        path: &Path,
    ) -> io::Result<Read>
    {
        let file = File::open(path)?;
        let metadata = file.metadata()?;
        let identity = Identity::of(&metadata);
        if let Some(&(held, ref read)) = self
            .held
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .get(path)
            && held == identity
        {
            return Ok(read.clone());
        }
        let held = if metadata.is_file() && Crossover(metadata.len()) >= self.crossover {
            // SAFETY: the mapping is read-only, and no gandr verb writes a file
            // a reader holds; the module docs state the hazard a rewrite in
            // place by another process leaves.
            let map = unsafe { memmap2::Mmap::map(&file) }?;
            core::str::from_utf8(&map)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
            Held::Mapped(map)
        }
        else {
            Held::Buffered(io::read_to_string(&file)?.into_boxed_str())
        };
        let read = Read(Arc::new(held));
        self.held
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(path.to_path_buf(), (identity, read.clone()));
        Ok(read)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::sync::Arc;
    use std::io;
    use std::path::Path;

    use gandr_surface_syntax::SourceText;

    use super::Crossover;
    use super::Held;
    use super::Reader;
    use crate::walk::tests::Scratch;

    #[test]
    fn an_unchanged_file_is_read_once()
    {
        let scratch = Scratch::new(Path::new("reader-once"));
        scratch.file(Path::new("a.gandr"), SourceText::from("def one = 1 ;"));
        let path = scratch.root().join("a.gandr");
        let reader = Reader::new();
        let first = reader.read(&path).expect("the file reads");
        let second = reader.read(&path).expect("the file reads again");
        assert_eq!(first.text().as_ref(), "def one = 1 ;");
        assert!(
            Arc::ptr_eq(&first.0, &second.0),
            "an unchanged file answers the text read before"
        );
        let missing = scratch.root().join("missing.gandr");
        assert_eq!(
            reader.read(&missing).expect_err("a missing file").kind(),
            io::ErrorKind::NotFound
        );
        assert!(
            reader.read(scratch.root()).is_err(),
            "a directory is no source"
        );
        let invalid = scratch.root().join("invalid.gandr");
        std::fs::write(&invalid, [0xff_u8, 0xfe]).expect("the invalid file is written");
        assert_eq!(
            reader
                .read(&invalid)
                .expect_err("bytes that are not UTF-8")
                .kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn a_rewritten_file_is_read_again()
    {
        let scratch = Scratch::new(Path::new("reader-again"));
        scratch.file(Path::new("a.gandr"), SourceText::from("def one = 1 ;"));
        let path = scratch.root().join("a.gandr");
        let reader = Reader::new();
        let before = reader.read(&path).expect("the file reads");
        scratch.file(
            Path::new("a.gandr"),
            SourceText::from("def one = 1 ; def two = 2 ;"),
        );
        let after = reader.read(&path).expect("the rewritten file reads");
        assert_eq!(
            before.text().as_ref(),
            "def one = 1 ;",
            "a held text never changes"
        );
        assert_eq!(after.text().as_ref(), "def one = 1 ; def two = 2 ;");
    }

    #[test]
    fn a_file_at_the_crossover_is_mapped_as_it_reads()
    {
        let scratch = Scratch::new(Path::new("reader-mapped"));
        let text = "def one = 1 ;\n".repeat(64);
        scratch.file(Path::new("a.gandr"), SourceText::from(text.as_str()));
        let path = scratch.root().join("a.gandr");
        let mapping =
            Reader::mapping_from(Crossover(u64::try_from(text.len()).expect("a small file")));
        let mapped = mapping.read(&path).expect("the file maps");
        assert!(
            matches!(*mapped.0, Held::Mapped(_)),
            "a file at the crossover is mapped"
        );
        let buffered = Reader::new().read(&path).expect("the file reads");
        assert!(
            matches!(*buffered.0, Held::Buffered(_)),
            "a file below it is buffered"
        );
        assert_eq!(mapped.text().as_ref(), buffered.text().as_ref());
        assert_eq!(mapped.text().as_ref(), text);
        let again = mapping.read(&path).expect("the file maps again");
        assert!(
            Arc::ptr_eq(&mapped.0, &again.0),
            "a mapped file is held as a buffered one is"
        );
        let invalid = scratch.root().join("invalid.gandr");
        std::fs::write(&invalid, [0xff_u8; 2048]).expect("the invalid file is written");
        assert_eq!(
            mapping
                .read(&invalid)
                .expect_err("mapped bytes that are not UTF-8")
                .kind(),
            io::ErrorKind::InvalidData
        );
    }
}
