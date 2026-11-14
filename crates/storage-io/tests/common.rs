//! The witnesses' shared fixtures: a fresh scratch file, an `Io` of each
//! form, and the completions of an `Io` until it holds no submission.

use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::fs::File;
use std::fs::OpenOptions;
use std::path::PathBuf;

use gandr_storage_io::Buffer;
use gandr_storage_io::Count;
use gandr_storage_io::Done;
use gandr_storage_io::Io;

/// The bytes of one block that the witnesses write and read.
pub const BLOCK: usize = 4_096;

/// The scratch files named so far in this process, so each name is fresh.
static NAMED: AtomicU64 = AtomicU64::new(0);

/// A fresh file for one witness, removed when the witness ends.
#[repr(transparent)]
pub struct Scratch
{
    /// The file's path.
    path: PathBuf,
}

impl Scratch
{
    /// A fresh scratch file, named by the process and a counter.
    ///
    /// # Specification
    /// trivial.
    pub fn new() -> Self
    {
        let serial = NAMED.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("gandr-storage-io-{}-{serial}", std::process::id()));
        Self { path }
    }

    /// The file, open to read and to write.
    ///
    /// # Specification
    /// trivial.
    pub fn open(&self) -> File
    {
        OpenOptions::new()
            .create(true)
            .truncate(true)
            .read(true)
            .write(true)
            .open(&self.path)
            .expect("the scratch file opens")
    }

    /// The file, open to read alone.
    ///
    /// # Specification
    /// trivial.
    pub fn reader(&self) -> File
    {
        File::open(&self.path).expect("the scratch file opens to read")
    }

    /// The bytes of the file.
    ///
    /// # Specification
    /// trivial.
    pub fn bytes(&self) -> Buffer
    {
        Buffer::from(std::fs::read(&self.path).expect("the scratch file reads"))
    }
}

impl Drop for Scratch
{
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let _removed = std::fs::remove_file(&self.path);
    }
}

/// An `Io` of each form at `depth`: the form that the kernel gives, then
/// the blocking form.
///
/// # Specification
/// trivial.
pub fn forms(depth: Count) -> [Io; 2]
{
    [
        Io::open(depth).expect("an io opens"),
        Io::blocking(depth).expect("the blocking form opens"),
    ]
}

/// Each completion of `io`, until it holds no submission.
///
/// # Specification
/// trivial.
pub fn completions(io: &mut Io) -> Vec<Done>
{
    core::iter::from_fn(|| io.wait().expect("the wait answers")).collect()
}
