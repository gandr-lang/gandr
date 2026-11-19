//! The cache: one entry for each request under its toolchain and its reader.
//!
//! [`Cache::read`] keys an entry by the identity, the reader program and the
//! request. An entry holds the digest of each source file that the reader
//! read, so a hit reads each of those files again and compares its digest.
//! A hit starts no process. A miss runs the reader once as a process, checks
//! the entry that it writes, and publishes the entry whole.
//!
//! The reader is a program that compiles the crate as `rustc` does, with
//! the build's arguments word for word. It takes the paths of the functions
//! in [`FUNCTIONS`], one on each line, and writes its entry to the file that
//! [`ENTRY`] names. Each other output of its run goes beside the entry.

use alloc::string::String;
use core::fmt;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;
use std::time::UNIX_EPOCH;

use anodized::spec;
use gandr_core_publish::Contents;
use gandr_core_publish::Unpublished;
use gandr_core_publish::publish;

use crate::bytes::Digest;
use crate::bytes::Encoded;
use crate::bytes::Entry;
use crate::bytes::Undecoded;
use crate::names::Status;
use crate::record::Identity;
use crate::record::Record;
use crate::request::Request;

/// The variable that gives the reader the paths of the functions, one on
/// each line.
pub const FUNCTIONS: &str = "GANDR_RUST_RECORD_FUNCTIONS";

/// The variable that names the file that the reader writes its entry to.
pub const ENTRY: &str = "GANDR_RUST_RECORD_ENTRY";

/// The domain of an entry's key, so that no other BLAKE3 key collides with
/// it.
const KEY_DOMAIN: &[u8] = b"gandr-rust-record-key\x01";

/// A directory that holds one entry for each key.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cache
{
    /// The directory.
    directory: PathBuf,
}

/// The reader: a program on rustc's own libraries that writes an entry.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Program(pub PathBuf);

/// Where an answer came from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Origin
{
    /// An entry of the cache, with no process.
    Cache,
    /// One run of the reader.
    Process,
}

/// A record and where it came from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Answer
{
    /// The record.
    pub record: Record,
    /// Where it came from.
    pub origin: Origin,
}

/// How a reader's process ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Exit
{
    /// The process exited with a status.
    Status(Status),
    /// A signal stopped the process.
    Signalled,
}

/// Why no record came back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unread
{
    /// The reader program cannot be read or started.
    Program(io::ErrorKind),
    /// The cache directory cannot be made, read or written.
    Directory(io::ErrorKind),
    /// The reader failed, and wrote what rustc said.
    Failed
    {
        /// How the process ended.
        exit: Exit,
        /// What the process wrote to its error stream.
        diagnostics: String,
    },
    /// The reader succeeded and wrote no entry.
    Absent,
    /// The reader wrote bytes that are no entry for the identity.
    Entry(Undecoded),
    /// The entry cannot be published to the cache.
    Unpublished(Unpublished),
}

impl fmt::Display for Unread
{
    /// Names the cause.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Program(kind) => write!(f, "the reader program cannot start: {kind}"),
            Self::Directory(kind) => write!(f, "the cache directory cannot be used: {kind}"),
            Self::Failed {
                exit: Exit::Status(status),
                ref diagnostics,
            } => {
                write!(f, "the reader failed with status {status}:\n{diagnostics}")
            },
            Self::Failed {
                exit: Exit::Signalled,
                ref diagnostics,
            } => write!(f, "a signal stopped the reader:\n{diagnostics}"),
            Self::Absent => f.write_str("the reader wrote no entry"),
            Self::Entry(ref undecoded) => {
                write!(f, "the reader wrote no entry for this build: {undecoded}")
            },
            Self::Unpublished(ref unpublished) => {
                write!(
                    f,
                    "the entry {} cannot be published: {}",
                    unpublished.path.display(),
                    unpublished.kind
                )
            },
        }
    }
}

/// A count that makes each scratch directory of the process its own.
static SCRATCH: AtomicU64 = AtomicU64::new(0);

impl Cache
{
    /// The cache in `directory`, which a miss creates.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn at(directory: PathBuf) -> Self
    {
        Self { directory }
    }

    /// The record of `request` under `identity`: from the cache when an
    /// entry stands and each of its sources is unchanged, else from one run
    /// of `program`.
    ///
    /// # Specification
    /// - requires: `program` writes an entry as the module states.
    /// - ensures: the record's identity equals `identity`. With
    ///   [`Origin::Cache`] no process started, and each source of the entry
    ///   holds the bytes that the reader read. With [`Origin::Process`] the
    ///   reader ran once, and the cache holds its entry under the key.
    /// - fails: [`Unread::Program`] when the program cannot be read or started;
    ///   [`Unread::Directory`] when the cache directory or the reader's scratch
    ///   directory cannot be used; [`Unread::Failed`] when the reader fails;
    ///   [`Unread::Absent`] when it succeeds and writes no entry;
    ///   [`Unread::Entry`] when its bytes are no entry for `identity`;
    ///   [`Unread::Unpublished`] when the entry cannot be published. Each
    ///   failure leaves the cache as it was.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unread`], as above.
    ///
    /// # Cost
    /// - allocation: the entry's bytes and each source's bytes for its digest,
    ///   growth within the entry and its sources
    /// - allocation: the paths, the list of functions and the reader's
    ///   diagnostics, growth within the request
    /// - allocation: the decoded record, durable by the answer
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a reader that counts its runs runs once for two
    ///   requests; an edit of a source the entry names runs it again; a failing
    ///   reader, a silent reader, a reader of truncated bytes and a reader of
    ///   another toolchain each fail by name and leave no entry.
    /// - witness: `tests::a_second_request_starts_no_process`
    /// - witness: `tests::an_edited_source_reads_again`
    /// - witness: `tests::a_failing_reader_is_failed_and_caches_nothing`
    /// - witness: `tests::a_silent_reader_is_absent`
    /// - witness: `tests::a_truncated_entry_is_refused_and_caches_nothing`
    /// - witness: `tests::an_entry_of_another_toolchain_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |answer| answer.record.identity == *identity))]
    #[inline]
    pub fn read(
        &self,
        program: &Program,
        request: &Request,
        identity: &Identity,
    ) -> Result<Answer, Unread>
    {
        let name = key(program, request, identity)?;
        let file = self.directory.join(&name);
        if let Ok(bytes) = fs::read(&file)
            && let Ok(entry) = Entry::decode(Encoded(&bytes), identity)
            && entry.sources.iter().all(|source| {
                fs::read(source.path.as_ref())
                    .is_ok_and(|now| Digest::of(Encoded(&now)) == source.digest)
            })
        {
            return Ok(Answer {
                record: entry.record,
                origin: Origin::Cache,
            });
        }
        fs::create_dir_all(&self.directory).map_err(|error| Unread::Directory(error.kind()))?;
        let scratch = Scratch::new(&self.directory)?;
        let written = scratch.0.join("entry");
        let mut functions = String::new();
        for (index, path) in request.functions.iter().enumerate() {
            if index > 0 {
                functions.push('\n');
            }
            functions.push_str(path.as_ref());
        }
        let output = Command::new(&program.0)
            .args(&request.arguments)
            .env(FUNCTIONS, functions)
            .env(ENTRY, &written)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .output()
            .map_err(|error| Unread::Program(error.kind()))?;
        if !output.status.success() {
            let exit = output
                .status
                .code()
                .map_or(Exit::Signalled, |code| Exit::Status(Status::from(code)));
            return Err(Unread::Failed {
                exit,
                diagnostics: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
        let bytes = match fs::read(&written) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Err(Unread::Absent),
            Err(error) => return Err(Unread::Directory(error.kind())),
        };
        let entry = Entry::decode(Encoded(&bytes), identity).map_err(Unread::Entry)?;
        publish(&self.directory, &name, Contents(&bytes)).map_err(Unread::Unpublished)?;
        Ok(Answer {
            record: entry.record,
            origin: Origin::Process,
        })
    }
}

/// The file name of a request's entry: the hexadecimal BLAKE3 key of the
/// identity, the reader program's size and time of change, and the request.
///
/// # Specification
/// - requires: nothing.
/// - ensures: equal inputs give equal names; a change of the commit, the
///   target, the program's size or time, any argument or any function gives
///   another name, up to a collision of BLAKE3.
/// - fails: [`Unread::Program`] when the program's metadata cannot be read.
/// - panics: none.
/// - executable: none — the property ranges over every input.
///
/// # Errors
/// [`Unread::Program`], as above.
///
/// # Cost
/// - allocation: the program's metadata and the name of the entry, durable by
///   the key
///
/// # Adequacy
/// - hypothesis: L3 — a change of each part of the key gives another name.
/// - witness: `tests::each_part_of_the_key_changes_the_name`
pub fn key(
    program: &Program,
    request: &Request,
    identity: &Identity,
) -> Result<String, Unread>
{
    let metadata = fs::metadata(&program.0).map_err(|error| Unread::Program(error.kind()))?;
    let changed = metadata
        .modified()
        .ok()
        .and_then(|time| time.duration_since(UNIX_EPOCH).ok())
        .map_or(0, |since| since.as_nanos());
    let mut hasher = blake3::Hasher::new();
    hasher.update(KEY_DOMAIN);
    let mut part = |bytes: &[u8]| {
        hasher.update(&u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes());
        hasher.update(bytes);
    };
    part(identity.commit.as_ref().as_bytes());
    part(identity.target.as_ref().as_bytes());
    part(&metadata.len().to_le_bytes());
    part(&changed.to_le_bytes());
    part(
        &u64::try_from(request.arguments.len())
            .unwrap_or(u64::MAX)
            .to_le_bytes(),
    );
    for argument in &request.arguments {
        part(argument.as_encoded_bytes());
    }
    for function in &request.functions {
        part(function.as_ref().as_bytes());
    }
    let mut name = String::from(hasher.finalize().to_hex().as_str());
    name.push_str(".entry");
    Ok(name)
}

/// A directory that one run of the reader writes into, removed on every
/// exit.
///
/// # Specification
/// - executable: none — creation and removal are the file system's.
///
/// # Adequacy
/// - hypothesis: L3 — after a read, of each outcome, the cache directory holds
///   no scratch directory.
/// - witness: `tests::a_failing_reader_is_failed_and_caches_nothing`
/// - witness: `tests::a_second_request_starts_no_process`
#[repr(transparent)]
struct Scratch(PathBuf);

impl Scratch
{
    /// A new scratch directory in `directory`, named by the process and a
    /// count. A directory of that name stands only when a process of the
    /// same number died before its removal, so its files are stale and go
    /// first.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the directory's path and the file system's own buffers,
    ///   setup
    fn new(directory: &Path) -> Result<Self, Unread>
    {
        let count = SCRATCH.fetch_add(1, Ordering::Relaxed);
        let path = directory.join(alloc::format!(".reading-{}-{count}", std::process::id()));
        let _stale: Result<(), io::Error> = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).map_err(|error| Unread::Directory(error.kind()))?;
        Ok(Self(path))
    }
}

impl Drop for Scratch
{
    /// Removes the scratch directory and each file in it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Cost
    /// - allocation: the file system's buffers of the removal, setup
    fn drop(&mut self)
    {
        let _removed: Result<(), io::Error> = fs::remove_dir_all(&self.0);
    }
}
