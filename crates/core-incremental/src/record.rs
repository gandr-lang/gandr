//! One record file, which both of the crate's file stores write and read.
//!
//! # The frame
//!
//! A record is a magic, a version, the store's key, the payload's length and
//! its BLAKE3 digest, then the payload. A store fixes its key's length: the
//! checkpoint store keys a record by its address and its backend, and the
//! verdict store by nothing. A read checks the magic, the version, the length
//! and the digest before it hands the payload on, so a store decodes only
//! bytes its own frame wrote. The digest is integrity only: it never admits.
//!
//! # Publication
//!
//! A record is written to a private temporary that the write created
//! exclusively, then published under its name by one rename. On every other
//! exit a guard attempts to remove the temporary. A record's name is a digest
//! in lowercase hexadecimal.
//!
//! # Decisions
//!
//! | Decision | Alternatives | Reversal |
//! | -------- | ------------ | -------- |
//! | The frame lives here, below both stores | the store facade in `storage-store`, which a `core` crate cannot depend on under the layering; a crate of its own below both tiers | one writer serves the facade and these stores, from a crate both tiers may depend on |
//! | The checkpoint record's header is the frame under a 64-byte key | a second header beside the frame, which would write the format twice | none: the checkpoint files keep their bytes |
//! | Exclusive temporary, then rename | write in place; a fixed temporary name, which a squatter or a concurrent store could hijack | a consumer needs durability, which adds a sync before and after the rename |
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — a hash proves only that a key names its bytes.

use alloc::string::String;
use alloc::vec::Vec;
use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::codec::Bytes;

/// The byte length of a frame's magic and version.
const OPENING_LEN: usize = 12;

/// The byte length of a frame's payload length and digest.
const CLOSING_LEN: usize = 40;

/// How many private names a write tries before giving up.
///
/// Each candidate draws a fresh 64-bit nonce, so a collision is already
/// improbable; the bound turns a pathological run of them into an error
/// rather than a loop or a silent overwrite.
const MAX_TEMPORARY_ATTEMPTS: u8 = 8;

quenchant_shape::reason_enum! {
    /// Why bytes hold no record of a format.
    pub mod unframed {
        /// The reason no record is read.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The magic, the version, the length or the digest does not
            /// match the frame of the format under a key of the length asked.
            Unframed,
        }
    }
}

/// Why a record could not be framed or published.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RecordFault
{
    /// The payload's length passes 64 bits, or the key is not of the format's
    /// length.
    Unrepresentable,
    /// A temporary could not be created or written, or the rename failed.
    Io,
}

/// What a file-system failure means to a record store.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Failure
{
    /// The path names nothing.
    NotFound,
    /// The path already names something.
    AlreadyExists,
    /// Any other failure.
    Other,
}

/// What `error` means to a record store.
///
/// # Specification
/// - ensures: missing and existing paths retain their distinct classes; every
///   other error kind is classified as `Other`.
///
/// # Adequacy
/// - hypothesis: L3 — actual missing-record and directory-read errors separate
///   `NotFound` from `Other`, and each kind is classified directly. Random
///   staging-name collisions are not forced, so the retry that reads
///   `AlreadyExists` has no collision witness.
/// - witness: `persistence::tests::file_load_distinguishes_not_found_from_other_read_errors`
#[expect(
    clippy::std_instead_of_core,
    reason = "`core::io::ErrorKind` is not stable yet"
)]
#[spec(
    ensures: |ret| match error.kind() {
        | std::io::ErrorKind::NotFound => ret == Failure::NotFound,
        | std::io::ErrorKind::AlreadyExists => ret == Failure::AlreadyExists,
        | _ => ret == Failure::Other,
    },
)]
pub fn failure_of(error: &std::io::Error) -> Failure
{
    let kind = error.kind();
    if kind == std::io::ErrorKind::NotFound {
        Failure::NotFound
    }
    else if kind == std::io::ErrorKind::AlreadyExists {
        Failure::AlreadyExists
    }
    else {
        Failure::Other
    }
}

/// A record file's format: the magic and the version its frame opens with,
/// and the length of the key its store fixes.
///
/// # Specification
/// - provides: the one frame both file stores write and read.
/// - executable: none — the format is three constants; [`Format::frame`] and
///   [`Format::read`] carry the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Format::frame`] and [`Format::read`].
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Format
{
    /// The magic a record opens with.
    pub magic: [u8; 8],
    /// The version that follows the magic.
    pub version: u32,
    /// The byte length of the store's key, which follows the version.
    pub key: usize,
}

/// A byte length: of a record's head, or of a payload a writer expects to
/// append.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Length(pub usize);

/// A record read whole: its key and its payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Framed<'bytes>
{
    /// The store's key, of the format's key length.
    pub key: Bytes<'bytes>,
    /// The payload, whose length and digest the frame states.
    pub payload: Bytes<'bytes>,
}

/// A record's payload, appended in place behind its frame's closing.
///
/// # Specification
/// - provides: the one way a writer reaches the record [`Format::frame`]
///   builds, which only appends, so the frame before it stays as written.
/// - executable: none — the sink holds only the record's bytes.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Format::frame`].
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
#[repr(transparent)]
#[derive(Debug)]
pub struct Payload<'out>(&'out mut Vec<u8>);

impl Payload<'_>
{
    /// Append `bytes` to the payload.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn append(
        &mut self,
        bytes: Bytes<'_>,
    )
    {
        self.0.extend_from_slice(bytes.0);
    }
}

impl Format
{
    /// The byte length of a record's head: the magic, the version and the
    /// key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn head(self) -> Length
    {
        Length(OPENING_LEN.saturating_add(self.key))
    }

    /// The record under `key` of the payload `write` appends in place, with
    /// room reserved for `reserve` bytes of it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the magic, the version, `key`, the payload's length and its
    ///   BLAKE3 digest, then the payload, so [`Format::read`] hands back `key`
    ///   and the payload `write` appended.
    /// - fails: [`RecordFault::Unrepresentable`] when `key` is not of the
    ///   format's key length, or the payload's length passes 64 bits.
    /// - panics: propagates a panic from `write`.
    ///
    /// # Errors
    /// [`RecordFault::Unrepresentable`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checkpoint and receipt records round-trip through a
    ///   reopened store; a changed address, extent or digest is refused on
    ///   load; a checkpoint record written by hand under the unmoved header
    ///   loads. A key of another length and an unrepresentable length are
    ///   unwitnessed.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes`
    /// - witness: `persistence::tests::a_record_under_the_unmoved_header_loads`
    /// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
    #[spec(
        ensures: |ret| match ret {
            | Ok(ref record) => match self.read(Bytes(&record.0)) {
                | Maybe::Present(framed) => framed.key == key,
                | Maybe::Absent(_) => false,
            },
            | Err(fault) => fault == RecordFault::Unrepresentable,
        },
    )]
    #[inline]
    pub fn frame<Write>(
        self,
        key: Bytes<'_>,
        reserve: Length,
        write: Write,
    ) -> Result<ArtifactBytes, RecordFault>
    where
        Write: FnOnce(&mut Payload<'_>),
    {
        if key.0.len() != self.key {
            return Err(RecordFault::Unrepresentable);
        }
        let Length(head) = self.head();
        let start = head.saturating_add(CLOSING_LEN);
        let mut bytes = Vec::with_capacity(start.saturating_add(reserve.0));
        bytes.extend_from_slice(&self.magic);
        bytes.extend_from_slice(&self.version.to_le_bytes());
        bytes.extend_from_slice(key.0);
        bytes.resize(start, 0);
        write(&mut Payload(&mut bytes));
        // The payload only appends, so the closing reserved above is there.
        let Some((closing, payload)) = bytes
            .get_mut(head ..)
            .and_then(|rest| rest.split_first_chunk_mut::<CLOSING_LEN>())
        else {
            return Err(RecordFault::Unrepresentable);
        };
        let length =
            u64::try_from(payload.len()).map_err(|_overflow| RecordFault::Unrepresentable)?;
        if let Some((stated, digest)) = closing.split_first_chunk_mut::<8>() {
            *stated = length.to_le_bytes();
            digest.copy_from_slice(blake3::hash(payload).as_bytes());
        }
        Ok(ArtifactBytes(bytes))
    }

    /// The key and the payload that `bytes` frame under this format.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when `bytes` open with this format's magic
    ///   and version, then a key of the format's length, then a length equal to
    ///   the rest's and the rest's BLAKE3 digest. Absent as
    ///   [`unframed::Absent::Unframed`] otherwise, a truncated or extended
    ///   record among them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a changed address, a changed or missing byte and a
    ///   trailing byte are each refused; a record of another magic is passed
    ///   over; a whole record is read.
    /// - witness: `persistence::tests::file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes`
    /// - witness: `verdicts::tests::a_damaged_file_is_passed_over`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(ref framed) => {
                let at = OPENING_LEN.saturating_add(self.key);
                framed.key.0.len() == self.key
                    && bytes.0.get(.. 8) == Some(self.magic.as_slice())
                    && bytes.0.get(at.saturating_add(CLOSING_LEN) ..) == Some(framed.payload.0)
                    && bytes.0.get(at.saturating_add(8) .. at.saturating_add(CLOSING_LEN))
                        == Some(blake3::hash(framed.payload.0).as_bytes().as_slice())
            },
            | Maybe::Absent(absent) => absent == unframed::Absent::Unframed,
        },
    )]
    #[inline]
    pub fn read<'bytes>(
        self,
        bytes: Bytes<'bytes>,
    ) -> Maybe<Framed<'bytes>, unframed::Absent>
    {
        let unread = Maybe::Absent(unframed::Absent::Unframed);
        let Some((head, rest)) = bytes.0.split_at_checked(self.head().0)
        else {
            return unread;
        };
        let Maybe::Present(stated) = self.key(Bytes(head))
        else {
            return unread;
        };
        let Some((length, rest)) = rest.split_first_chunk::<8>()
        else {
            return unread;
        };
        let Some((digest, payload)) = rest.split_first_chunk::<32>()
        else {
            return unread;
        };
        let stated_length = usize::try_from(u64::from_le_bytes(*length));
        if stated_length != Ok(payload.len()) || digest != blake3::hash(payload).as_bytes() {
            return unread;
        }
        Maybe::Present(Framed {
            key: stated,
            payload: Bytes(payload),
        })
    }

    /// The key that `head`, a record's head or more, states under this
    /// format.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when `head` opens with this format's magic
    ///   and version and holds a key of the format's length after them, which
    ///   it hands back.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store's prune reads each record's head alone and
    ///   passes over a file that opens with no record's magic.
    /// - witness: `persistence::tests::pruning_keeps_only_the_kept_backend_s_records_1816`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(stated) => {
                stated.0.len() == self.key
                    && head.0.get(.. 8) == Some(self.magic.as_slice())
                    && head.0.get(8 .. OPENING_LEN) == Some(self.version.to_le_bytes().as_slice())
            },
            | Maybe::Absent(absent) => absent == unframed::Absent::Unframed,
        },
    )]
    #[inline]
    pub fn key<'bytes>(
        self,
        head: Bytes<'bytes>,
    ) -> Maybe<Bytes<'bytes>, unframed::Absent>
    {
        let opens = head.0.get(.. 8) == Some(self.magic.as_slice())
            && head.0.get(8 .. OPENING_LEN) == Some(self.version.to_le_bytes().as_slice());
        match head.0.get(OPENING_LEN .. self.head().0) {
            Some(stated) if opens => Maybe::Present(Bytes(stated)),
            Some(_) | None => Maybe::Absent(unframed::Absent::Unframed),
        }
    }
}

/// Whether a file's name is spelled as a record's.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Spelling
{
    /// The name is 64 lowercase hexadecimal digits.
    Record,
    /// The name is any other.
    Other,
}

/// The name a record is published under: a digest in lowercase hexadecimal.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordName(String);

impl RecordName
{
    /// The name spelling `digest`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(digest: blake3::Hash) -> Self
    {
        Self(String::from(digest.to_hex().as_str()))
    }

    /// How `file` is spelled: as a record's name, 64 lowercase hexadecimal
    /// digits, or as another.
    ///
    /// # Specification
    /// - ensures: [`Spelling::Record`] exactly when `file` is 64 bytes, each a
    ///   digit or a lowercase letter from `a` to `f`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store's open and prune read the records and leave a
    ///   temporary and a file of another name.
    /// - witness: `persistence::tests::pruning_keeps_only_the_kept_backend_s_records_1816`
    /// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
    #[spec(
        ensures: |ret| (ret == Spelling::Record) == file.to_str().is_some_and(|spelled| {
            spelled.len() == 64
                && spelled.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
        }),
    )]
    #[inline]
    #[must_use]
    pub fn spelling(file: &OsStr) -> Spelling
    {
        let record = file.len() == 64
            && file
                .as_encoded_bytes()
                .iter()
                .all(|byte| matches!(byte, b'0' ..= b'9' | b'a' ..= b'f'));
        if record {
            Spelling::Record
        }
        else {
            Spelling::Other
        }
    }

    /// The path of the record so named in `root`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn within(
        &self,
        root: &Path,
    ) -> PathBuf
    {
        root.join(&self.0)
    }
}

/// A record's bytes, as [`Format::frame`] wrote them.
///
/// # Specification
/// - executable: none — this nominal byte wrapper has no callable boundary;
///   [`Format::frame`] establishes its framing.
///
/// # Adequacy
/// - hypothesis: L3 — real file round-trips and mutations of record integrity
///   exercise the frame.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactBytes(Vec<u8>);

impl ArtifactBytes
{
    /// The name of the record whose name is the BLAKE3 digest of these bytes.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn named_by_digest(&self) -> RecordName
    {
        RecordName::of(blake3::hash(&self.0))
    }
}

impl AsRef<[u8]> for ArtifactBytes
{
    /// The record's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// Write `artifact` into `root` under `name`: a private temporary, then one
/// rename.
///
/// # Specification
/// - requires: `root` is an existing directory.
/// - ensures: on success `root` holds `artifact` under `name`, and no temporary
///   of this write remains; on failure the guard attempts to remove the
///   temporary, and the record under `name` is as it was.
/// - fails: [`RecordFault::Io`] when no temporary can be created or written, or
///   the rename fails.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// [`RecordFault::Io`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`TemporaryRecord::write`] and
///   [`TemporaryRecord::commit`].
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
/// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
pub fn publish(
    root: &Path,
    name: &RecordName,
    artifact: &ArtifactBytes,
) -> Result<(), RecordFault>
{
    TemporaryRecord::write(root, name, artifact)?.commit(&name.within(root))
}

/// An exclusively created private path guarded until publication.
/// Drop attempts cleanup unless a successful rename disarms the guard.
///
/// # Specification
/// - executable: none — publication and cleanup concern external filesystem
///   state; the guard retains only a path and publication flag.
///
/// # Adequacy
/// - hypothesis: L3 — failed rename removes a private record in a writable
///   directory; successful and concurrent publication leave only the named
///   record. Cleanup refusal and forced nonce collisions are not witnessed.
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
struct TemporaryRecord
{
    /// The private path the record was written to.
    path: PathBuf,
    /// Whether the rename published the record, which disarms the removal.
    published: Publication,
}

/// Whether a temporary record reached its published name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Publication
{
    /// Still private: the guard attempts to remove it.
    Private,
    /// Renamed into place: nothing to remove.
    Published,
}

impl TemporaryRecord
{
    /// Write `artifact` into a file created exclusively in `root`, under a
    /// private name leading with `name`.
    ///
    /// # Specification
    /// - requires: `root` is an existing directory.
    /// - ensures: on success the whole artifact is in a file this call created,
    ///   under a name no other live temporary holds; the guard attempts removal
    ///   unless [`Self::commit`] publishes it. A candidate name that exists is
    ///   never opened: exclusive creation turns a collision into a retry under
    ///   a fresh nonce.
    /// - fails: [`RecordFault::Io`] when a candidate cannot be created for any
    ///   reason but existing, when the write fails — the handle is then closed
    ///   before cleanup of the partial file is attempted — or when
    ///   [`MAX_TEMPORARY_ATTEMPTS`] candidates in a row exist.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real publication, failed rename, a predictable-name
    ///   squatter and four concurrent publishers exercise private creation. The
    ///   predicate checks lexical directory/name placement and an armed guard;
    ///   it does not reread the artifact or force the random collision retry
    ///   path.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    /// - witness: `persistence::tests::a_store_never_writes_through_a_file_it_did_not_create`
    /// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
    #[spec(
        ensures: |ret| match ret {
            | Ok(ref record) => {
                record.published == Publication::Private
                    && record.path.parent() == Some(root)
                    && record.path.file_name().is_some_and(|file| {
                        name.0.len() == 64
                            && file.as_encoded_bytes().strip_prefix(name.0.as_bytes())
                                .is_some_and(|rest| rest.starts_with(b".tmp-"))
                    })
            },
            | Err(fault) => fault == RecordFault::Io,
        },
    )]
    fn write(
        root: &Path,
        name: &RecordName,
        artifact: &ArtifactBytes,
    ) -> Result<Self, RecordFault>
    {
        let process = std::process::id();
        for _ in 0 .. MAX_TEMPORARY_ATTEMPTS {
            // A fresh nonce per attempt, so a retry resolves the collision it
            // met instead of meeting it again.
            let nonce = core::hash::BuildHasher::hash_one(&std::hash::RandomState::new(), process);
            let candidate = root.join(alloc::format!("{}.tmp-{process}-{nonce:016x}", name.0));
            let created = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&candidate);
            let mut file = match created {
                Ok(file) => file,
                Err(ref error) if failure_of(error) == Failure::AlreadyExists => continue,
                Err(_error) => return Err(RecordFault::Io),
            };
            // Armed before the first byte, so cleanup also covers partial writes.
            let record = Self {
                path: candidate,
                published: Publication::Private,
            };
            let written = std::io::Write::write_all(&mut file, &artifact.0)
                .and_then(|()| std::io::Write::flush(&mut file));
            // The handle closes here, before either exit: left to scope end,
            // locals drop in reverse order and the guard would remove a file
            // still open, which some platforms refuse.
            drop(file);
            written.map_err(|_error| RecordFault::Io)?;
            return Ok(record);
        }
        Err(RecordFault::Io)
    }

    /// Rename the record onto `destination`, publishing it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when the rename succeeded; the guard is then
    ///   disarmed. On failure the guard attempts to remove the temporary.
    /// - fails: [`RecordFault::Io`] when the rename fails.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — publication succeeds in a writable directory and
    ///   fails against an occupied directory path. The predicate checks the
    ///   guard state; the filesystem witnesses observe the record and cleanup,
    ///   without claiming that a refused removal could not leave a temporary.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    #[spec(
        captures: [before = self.published],
        ensures: |ret| match ret {
            | Ok(()) => self.published == Publication::Published,
            | Err(fault) => fault == RecordFault::Io && self.published == before,
        },
    )]
    fn commit(
        mut self,
        destination: &Path,
    ) -> Result<(), RecordFault>
    {
        std::fs::rename(&self.path, destination).map_err(|_error| RecordFault::Io)?;
        self.published = Publication::Published;
        Ok(())
    }
}

impl Drop for TemporaryRecord
{
    /// Attempt to remove the temporary unless the rename published it.
    ///
    /// # Specification
    /// - ensures: an unpublished path receives one best-effort removal attempt;
    ///   a published path is not removed.
    /// - executable: none — removal is external I/O whose failure is discarded;
    ///   probing the path afterward would neither prove the attempt nor be
    ///   race-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — failed publication leaves no private record in the
    ///   writable test directory, while successful publication remains
    ///   readable. A cleanup failure or concurrent deletion is not injected.
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    #[inline]
    fn drop(&mut self)
    {
        if self.published == Publication::Private {
            drop(std::fs::remove_file(&self.path));
        }
    }
}
