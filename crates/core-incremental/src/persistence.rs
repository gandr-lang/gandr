//! Content-addressed persistence for complete checkpoint sets: a memory
//! backend and an atomic file backend.
//!
//! # Addressed by the program, keyed by the backend
//!
//! A checkpoint set is stored under the BLAKE3 address of its program's
//! canonical bytes and under the identity of the backend artifact that judged
//! it, so a set is only ever restored for the same program and the same
//! checker. A restored set is not trusted: the next resume validates every
//! item of it as it validates an in-memory one.
//!
//! # A failed store leaves the store as it was
//!
//! Both backends encode completely before they change anything, so an
//! unsupported form fails a store with nothing written. The file backend
//! writes the record to a private temporary it created exclusively and
//! publishes it with one rename. On every other exit a guard attempts to
//! remove the temporary; cleanup is best-effort if the filesystem itself
//! refuses removal. Loading checks the header, the address, the length and the
//! payload's digest before it decodes, and decoding refuses a payload that is
//! not the canonical spelling of what it parses to.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_kernel_strata::LevelOffset;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;
use crate::boundary::RecordCount;
use crate::checkpoint::Checkpoints;
use crate::codec::Bytes;
use crate::codec::CheckpointBytes;
use crate::codec::CodecError;
use crate::codec::UnsupportedPersistence;
use crate::codec::write_program;
use crate::content::ItemContent;
use crate::content::encode_item;
use crate::region::Program;

quenchant_shape::reason_enum! {
    /// Why a store holds no checkpoint set for an address.
    pub mod stored {
        /// The reason nothing is loaded.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No record is held at the address.
            NotStored,
            /// The record at the address was judged by another backend.
            OtherBackend,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a restore returned no checkpoint set.
    pub mod restored {
        /// The reason nothing is restored.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The address is not the program's.
            AddressMismatch,
            /// No record is held at the address.
            NotStored,
            /// The record at the address was judged by another backend.
            OtherBackend,
        }
    }
}

/// The byte length of a file record's header.
const FILE_HEADER_LEN: usize = 116;
/// The magic a file record opens with.
const FILE_MAGIC: &[u8; 8] = b"GCKFILE\0";
/// The file record format's version.
const FILE_VERSION: u32 = 1;
/// How many private names a store tries before giving up.
///
/// Each candidate draws a fresh 64-bit nonce, so a collision is already
/// improbable; the bound turns a pathological run of them into an error
/// rather than a loop or a silent overwrite.
const MAX_TEMPORARY_ATTEMPTS: u8 = 8;

/// The content address of a program revision: the BLAKE3 digest of its
/// canonical bytes.
///
/// # Specification
/// - executable: none — the digest does not retain the program whose canonical
///   bytes it addresses.
///
/// # Adequacy
/// - hypothesis: L3 — independently allocated finite programs retain identity;
///   selected reorderings, renamings and value changes separate addresses. This
///   is not a collision-freedom proof.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `persistence::tests::meaningful_program_changes_and_source_order_change_identity`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CheckpointAddress([u8; 32]);

impl CheckpointAddress
{
    /// The digest, as lowercase hexadecimal: the record's file name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_hex(self) -> String
    {
        String::from(blake3::Hash::from_bytes(self.0).to_hex().as_str())
    }
}

/// The identity of the backend artifact that judged a checkpoint set.
///
/// # Specification
/// - executable: none — the digest does not retain the artifact bytes whose
///   identity it records.
///
/// # Adequacy
/// - hypothesis: L3 — real backend digests separate restored records; raw
///   digest extrema exercise the memory key range. Neither witness proves
///   collision freedom.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BackendArtifact([u8; 32]);

impl From<&[u8]> for BackendArtifact
{
    /// The identity of an artifact with these canonical bytes: their BLAKE3
    /// digest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self(*blake3::hash(bytes).as_bytes())
    }
}

/// Why a checkpoint store refused or failed.
///
/// # Specification
/// - executable: none — an error value does not retain the failed codec or
///   filesystem operation.
///
/// # Adequacy
/// - hypothesis: L3 — observed corrupt, noncanonical, oversized-level,
///   unresolved-node and filesystem cases retain their error class and payload.
///   Unrepresentable machine-size lengths are outside this finite evidence.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `persistence::tests::file_load_rejects_parseable_noncanonical_payload_after_integrity_checks`
/// - witness: `persistence::tests::opening_an_existing_file_as_a_directory_fails_without_changing_it`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CheckpointStoreError
{
    /// The record cannot be represented: a length passes the format's width.
    Rejected,
    /// The checkpoint set holds a form the encoding has no spelling for.
    UnsupportedPersistence(UnsupportedPersistence),
    /// The stored bytes are truncated, corrupted, carry trailing bytes, or do
    /// not match their address.
    Corrupt,
    /// A level atom's offset meets the decoder's cap.
    LevelOffsetTooLarge
    {
        /// The offset read.
        offset: LevelOffset,
    },
    /// The payload parses but is not the canonical spelling of its value.
    NonCanonical,
    /// The file system failed.
    Io,
}

impl From<CodecError> for CheckpointStoreError
{
    /// The store's account of a codec failure.
    ///
    /// # Specification
    /// - ensures: the codec failure keeps its class and diagnostic payload in
    ///   the store error vocabulary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — malformed, noncanonical, capped and unresolved
    ///   payloads cross the public persistence boundary with exact errors. The
    ///   machine-width refusal has no reachable oversized allocation in this
    ///   corpus.
    /// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
    /// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
    /// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
    /// - witness: `persistence::tests::file_load_rejects_parseable_noncanonical_payload_after_integrity_checks`
    #[spec(
        ensures: |ret| match (error, ret) {
            | (CodecError::Corrupt, Self::Corrupt)
            | (CodecError::NonCanonical, Self::NonCanonical)
            | (CodecError::Unrepresentable, Self::Rejected) => true,
            | (
                CodecError::LevelOffsetTooLarge { offset },
                Self::LevelOffsetTooLarge { offset: observed },
            ) => offset == observed,
            | (CodecError::Unsupported(form), Self::UnsupportedPersistence(observed)) => {
                form == observed
            },
            | _ => false,
        },
    )]
    #[inline]
    fn from(error: CodecError) -> Self
    {
        match error {
            | CodecError::Corrupt => Self::Corrupt,
            | CodecError::NonCanonical => Self::NonCanonical,
            | CodecError::LevelOffsetTooLarge { offset } => Self::LevelOffsetTooLarge { offset },
            | CodecError::Unsupported(form) => Self::UnsupportedPersistence(form),
            | CodecError::Unrepresentable => Self::Rejected,
        }
    }
}

impl fmt::Display for CheckpointStoreError
{
    /// Writes the failure's message.
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
            | Self::Rejected => f.write_str("the checkpoint record cannot be represented"),
            | Self::UnsupportedPersistence(form) => write!(f, "cannot persist: {form}"),
            | Self::Corrupt => f.write_str("the checkpoint record is corrupt"),
            | Self::LevelOffsetTooLarge { offset } => {
                write!(
                    f,
                    "a level offset of {} passes the decoder's cap",
                    u64::from(offset)
                )
            },
            | Self::NonCanonical => f.write_str("the checkpoint payload is not canonical"),
            | Self::Io => f.write_str("the checkpoint store's file system failed"),
        }
    }
}

impl core::error::Error for CheckpointStoreError
{
}

/// Observes persistence and invalidation without taking part in checking.
///
/// # Specification
/// - executable: none — the trait exposes no notification history or state
///   observer.
///
/// # Adequacy
/// - hypothesis: L3 — a recording observer sees successful stores and empty
///   restores; a failed publication sends no stored notification. This does not
///   certify arbitrary observer implementations or their panic behavior.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
pub trait CheckpointObserver
{
    /// A checkpoint set was stored at `address`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn stored(
        &mut self,
        _address: CheckpointAddress,
    )
    {
    }

    /// A restore at `address` returned nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn invalidated(
        &mut self,
        _address: CheckpointAddress,
    )
    {
    }
}

/// A persistence boundary for complete checkpoint sets.
///
/// # Specification
/// - executable: none — state, canonical bytes and later operations belong to
///   implementors, not this declaration.
///
/// # Adequacy
/// - hypothesis: L3 — memory and reopened files return the tested canonical
///   sets, with backend separation and failure preservation. Capped offsets are
///   refused before replacing an existing record.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
/// - witness: `tests::defects::a_failed_store_leaves_the_store_as_it_was`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
pub trait CheckpointStore
{
    /// Load the set stored at `address` by `backend`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the decoded set stored at `address` by `backend`.
    /// - provides: `stored::Absent` when nothing is stored there, or what is
    ///   was stored by another backend.
    /// - fails: when the stored bytes are corrupt or not canonical, or the
    ///   backing store fails.
    /// - panics: none.
    /// - executable: none — the required method has no body or byte-state
    ///   observer; inspecting storage again would perform another operation.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real memory and file records distinguish matching,
    ///   absent and other-backend keys; corrupt files fail. These witnesses
    ///   cover concrete implementations, not every implementation of the trait.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
    /// - witness: `persistence::tests::file_load_rejects_parseable_noncanonical_payload_after_integrity_checks`
    ///
    /// # Errors
    /// A typed persistence error naming the failure.
    fn load(
        &mut self,
        address: CheckpointAddress,
        backend: BackendArtifact,
    ) -> Result<Maybe<Checkpoints, stored::Absent>, CheckpointStoreError>;

    /// Store `checkpoints` at `address` for `backend`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the new record decodes to `checkpoints`; a later
    ///   load returns that set absent intervening changes or read failures. On
    ///   failure the store holds what it held before.
    /// - fails: unsupported data, capped levels, unrepresentable counts, or a
    ///   backing-store failure.
    /// - panics: none.
    /// - executable: none — the required method has no body or state observer
    ///   with which to compare the stored bytes or a later load.
    ///
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supported sets round-trip; unsupported and capped
    ///   replacements leave the old record intact. File preservation is
    ///   observed through both its bytes and a subsequent load.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `tests::defects::a_failed_store_leaves_the_store_as_it_was`
    /// - witness: `persistence::tests::stores_refuse_capped_levels_without_replacing_records`
    ///
    /// # Errors
    /// A typed persistence error naming the failure.
    fn store(
        &mut self,
        address: CheckpointAddress,
        backend: BackendArtifact,
        checkpoints: &Checkpoints,
    ) -> Result<(), CheckpointStoreError>;
}

/// A checkpoint store in memory, holding canonical records.
///
/// # Specification
/// - executable: none — canonicality relates each stored byte string to the
///   encoding operation, not a retained checkpoint value.
///
/// # Adequacy
/// - hypothesis: L3 — checked sets at two budgets occupy distinct backend keys;
///   replacement preserves neighboring records, and unsupported encoding does
///   not alter the old record. Capped offsets are refused before publication.
/// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
/// - witness: `tests::defects::a_failed_store_leaves_the_store_as_it_was`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MemoryCheckpointStore
{
    /// The canonical records, by address and backend.
    records: BTreeMap<(CheckpointAddress, BackendArtifact), CheckpointBytes>,
}

impl MemoryCheckpointStore
{
    /// How many records the store holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn record_count(&self) -> RecordCount
    {
        RecordCount::from(self.records.len())
    }
}

impl CheckpointStore for MemoryCheckpointStore
{
    /// Decode the record at `address` for `backend`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`CheckpointStore::load`]; a record of another backend at
    ///   the address answers `OtherBackend`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and occupied address ranges, both digest
    ///   extrema, two backend records and replacement preserve the selected set
    ///   and count. The predicate checks selection and error classes without
    ///   decoding twice.
    /// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    #[spec(
        captures: [before = self.records.len()],
        ensures: |ret| {
            self.records.len() == before
                && match ret {
                    | Ok(Maybe::Present(_)) => self.records.contains_key(&(address, backend)),
                    | Ok(Maybe::Absent(stored::Absent::NotStored)) => self
                        .records
                        .range(
                            (address, BackendArtifact([0; 32]))
                                ..= (address, BackendArtifact([u8::MAX; 32])),
                        )
                        .next()
                        .is_none(),
                    | Ok(Maybe::Absent(stored::Absent::OtherBackend)) => {
                        !self.records.contains_key(&(address, backend))
                            && self
                                .records
                                .range(
                                    (address, BackendArtifact([0; 32]))
                                        ..= (address, BackendArtifact([u8::MAX; 32])),
                                )
                                .next()
                                .is_some()
                    },
                    | Err(error) => {
                        self.records.contains_key(&(address, backend))
                            && matches!(
                                error,
                                CheckpointStoreError::Corrupt
                                    | CheckpointStoreError::NonCanonical
                                    | CheckpointStoreError::LevelOffsetTooLarge { .. }
                            )
                    },
                }
        },
    )]
    #[inline]
    fn load(
        &mut self,
        address: CheckpointAddress,
        backend: BackendArtifact,
    ) -> Result<Maybe<Checkpoints, stored::Absent>, CheckpointStoreError>
    {
        if let Some(bytes) = self.records.get(&(address, backend)) {
            let decoded = crate::codec::decode_checkpoints(Bytes(bytes.as_ref()))?;
            return Ok(Maybe::Present(decoded));
        }
        let elsewhere = self
            .records
            .range(
                (address, BackendArtifact([0; 32])) ..= (address, BackendArtifact([u8::MAX; 32])),
            )
            .next()
            .is_some();
        Ok(Maybe::Absent(if elsewhere {
            stored::Absent::OtherBackend
        }
        else {
            stored::Absent::NotStored
        }))
    }

    /// Encode, then insert.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`CheckpointStore::store`]; the encoding completes before
    ///   the map is touched.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct backend keys coexist, replacement preserves
    ///   neighboring values, and unsupported encoding leaves the old record and
    ///   count intact. Value preservation is observed by loads, not a cloned
    ///   pre-state; capped offsets are refused before insertion.
    /// - witness: `tests::defects::a_failed_store_leaves_the_store_as_it_was`
    /// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
    /// - witness: `persistence::tests::stores_refuse_capped_levels_without_replacing_records`
    #[spec(
        captures: [
            before = self.records.len(),
            held = self.records.contains_key(&(address, backend)),
        ],
        ensures: |ret| match ret {
            | Ok(()) => {
                self.records.contains_key(&(address, backend))
                    && before.checked_add(usize::from(!held)) == Some(self.records.len())
            },
            | Err(error) => {
                self.records.len() == before
                    && self.records.contains_key(&(address, backend)) == held
                    && matches!(
                        error,
                        CheckpointStoreError::UnsupportedPersistence(_)
                            | CheckpointStoreError::Rejected
                            | CheckpointStoreError::LevelOffsetTooLarge { .. }
                    )
            },
        },
    )]
    #[inline]
    fn store(
        &mut self,
        address: CheckpointAddress,
        backend: BackendArtifact,
        checkpoints: &Checkpoints,
    ) -> Result<(), CheckpointStoreError>
    {
        let bytes = crate::codec::encode_checkpoints(checkpoints)?;
        let _replaced = self.records.insert((address, backend), bytes);
        Ok(())
    }
}

/// A checkpoint store in a directory: one file per address, named by the
/// address's hexadecimal digest.
///
/// # Specification
/// - executable: none — the path does not hold the directory state, record
///   bytes or results of concurrent filesystem operations.
///
/// # Adequacy
/// - hypothesis: L3 — reopened directories preserve ordinary records; failed
///   publication and four concurrent publishers exercise staging and
///   replacement. Removal failures and forced random-name collisions are
///   outside these witnesses.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
/// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FileCheckpointStore
{
    /// The directory holding the records.
    root: PathBuf,
}

impl FileCheckpointStore
{
    /// Open or create the record directory at `path`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the directory exists.
    /// - fails: [`CheckpointStoreError::Io`] when it cannot be created.
    /// - panics: propagates a panic from the supplied `AsRef` implementation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real directory is created and reopened; a file at
    ///   the requested path fails without changing its bytes. The predicate
    ///   classifies errors without replaying an arbitrary `AsRef`
    ///   implementation or probing the filesystem after the operation.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::opening_an_existing_file_as_a_directory_fails_without_changing_it`
    ///
    /// # Errors
    /// [`CheckpointStoreError::Io`] — the directory cannot be created.
    #[spec(
        ensures: |ret| matches!(ret, Ok(_) | Err(CheckpointStoreError::Io)),
    )]
    #[inline]
    pub fn open<Location>(path: Location) -> Result<Self, CheckpointStoreError>
    where
        Location: AsRef<Path>,
    {
        let root = path.as_ref().to_path_buf();
        std::fs::create_dir_all(&root).map_err(|_error| CheckpointStoreError::Io)?;
        Ok(Self { root })
    }

    /// The path of the record for `address`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn record_path(
        &self,
        address: CheckpointAddress,
    ) -> PathBuf
    {
        self.root.join(address.to_hex())
    }
}

impl CheckpointStore for FileCheckpointStore
{
    /// Read, check and decode the record at `address`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`CheckpointStore::load`]; a missing file answers
    ///   `NotStored`, and a record whose header names another backend answers
    ///   `OtherBackend` after both integrity checking and payload decoding.
    /// - fails: [`CheckpointStoreError::Io`] for any read error but a missing
    ///   file; [`CheckpointStoreError::Corrupt`] for a bad header, an address
    ///   that is not the file's, a length or digest that does not match the
    ///   payload; the decoder's errors after those checks.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the read-error split and each
    ///   integrity check, separated by a missing record, a directory at the
    ///   record path, a flipped address byte, a flipped payload byte, a
    ///   truncated and an extended file, and a well-formed record carrying a
    ///   noncanonical payload for another backend. Decode failure takes
    ///   precedence over backend mismatch. Removal races are not simulated.
    /// - witness: `persistence::tests::file_load_distinguishes_not_found_from_other_read_errors`
    /// - witness: `persistence::tests::file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes`
    /// - witness: `persistence::tests::file_load_rejects_parseable_noncanonical_payload_after_integrity_checks`
    #[spec(
        ensures: |ret| {
            matches!(
                ret,
                Ok(_)
                    | Err(CheckpointStoreError::Io
                        | CheckpointStoreError::Corrupt
                        | CheckpointStoreError::NonCanonical
                        | CheckpointStoreError::LevelOffsetTooLarge { .. })
            )
        },
    )]
    #[inline]
    fn load(
        &mut self,
        address: CheckpointAddress,
        backend: BackendArtifact,
    ) -> Result<Maybe<Checkpoints, stored::Absent>, CheckpointStoreError>
    {
        let bytes = match std::fs::read(self.record_path(address)) {
            | Ok(bytes) => bytes,
            | Err(ref error) if failure_of(error) == Failure::NotFound => {
                return Ok(Maybe::Absent(stored::Absent::NotStored));
            },
            | Err(_error) => return Err(CheckpointStoreError::Io),
        };
        let (header, payload) = bytes
            .split_at_checked(FILE_HEADER_LEN)
            .ok_or(CheckpointStoreError::Corrupt)?;
        let Some((magic, header)) = header.split_first_chunk::<8>()
        else {
            return Err(CheckpointStoreError::Corrupt);
        };
        let Some((version, header)) = header.split_first_chunk::<4>()
        else {
            return Err(CheckpointStoreError::Corrupt);
        };
        let Some((stored_address, header)) = header.split_first_chunk::<32>()
        else {
            return Err(CheckpointStoreError::Corrupt);
        };
        let Some((stored_backend, header)) = header.split_first_chunk::<32>()
        else {
            return Err(CheckpointStoreError::Corrupt);
        };
        let Some((length, digest)) = header.split_first_chunk::<8>()
        else {
            return Err(CheckpointStoreError::Corrupt);
        };
        let length = usize::try_from(u64::from_le_bytes(*length))
            .map_err(|_overflow| CheckpointStoreError::Corrupt)?;
        if magic != FILE_MAGIC
            || u32::from_le_bytes(*version) != FILE_VERSION
            || *stored_address != address.0
            || payload.len() != length
            || digest != blake3::hash(payload).as_bytes()
        {
            return Err(CheckpointStoreError::Corrupt);
        }
        let decoded = crate::codec::decode_checkpoints(Bytes(payload))?;
        if *stored_backend != backend.0 {
            return Ok(Maybe::Absent(stored::Absent::OtherBackend));
        }
        Ok(Maybe::Present(decoded))
    }

    /// Encode, write a private temporary, and publish it with one rename.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`CheckpointStore::store`]; no file that existed before
    ///   the call is opened, truncated or written. An unpublished temporary
    ///   receives a best-effort cleanup attempt.
    /// - fails: the encoding's refusal, before any file is touched;
    ///   [`CheckpointStoreError::Io`] when the temporary cannot be created or
    ///   written or the rename fails.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the surfaces are the staging, the exclusivity of the
    ///   staging name and the publishing rename, separated by a directory
    ///   occupying the record path, a squatter at the name a predictable
    ///   staging scheme would pick, four threads storing one address at once,
    ///   and an unsupported set stored over a published record. Cleanup
    ///   succeeds in those writable directories; forced random-name collisions,
    ///   and cleanup refusal are not proved. Capped offsets leave the old
    ///   record bytes, decoded set and directory entries unchanged.
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    /// - witness: `persistence::tests::a_store_never_writes_through_a_file_it_did_not_create`
    /// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
    /// - witness: `tests::defects::a_failed_store_leaves_the_store_as_it_was`
    /// - witness: `persistence::tests::stores_refuse_capped_levels_without_replacing_records`
    #[spec(
        ensures: |ret| {
            matches!(
                ret,
                Ok(())
                    | Err(CheckpointStoreError::Io
                        | CheckpointStoreError::UnsupportedPersistence(_)
                        | CheckpointStoreError::Rejected
                        | CheckpointStoreError::LevelOffsetTooLarge { .. })
            )
        },
    )]
    #[inline]
    fn store(
        &mut self,
        address: CheckpointAddress,
        backend: BackendArtifact,
        checkpoints: &Checkpoints,
    ) -> Result<(), CheckpointStoreError>
    {
        let payload = crate::codec::encode_checkpoints(checkpoints)?;
        let artifact = artifact_bytes(address, backend, Bytes(payload.as_ref()))?;
        let record = TemporaryRecord::write(&self.root, address, &artifact)?;
        record.commit(&self.record_path(address))
    }
}

/// What a file-system failure means to the store.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Failure
{
    /// The path names nothing.
    NotFound,
    /// The path already names something.
    AlreadyExists,
    /// Any other failure.
    Other,
}

/// What `error` means to the store.
///
/// # Specification
/// - ensures: missing and existing paths retain their distinct classes; every
///   other error kind is classified as `Other`.
///
/// # Adequacy
/// - hypothesis: L3 — actual missing-record and directory-read errors separate
///   `NotFound` from `Other`. Random staging-name collisions are not forced, so
///   `AlreadyExists` classification has no dedicated collision witness.
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
fn failure_of(error: &std::io::Error) -> Failure
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
    /// Write `artifact` into a file created exclusively in `root`.
    ///
    /// # Specification
    /// - requires: `root` is an existing directory.
    /// - ensures: on success the whole artifact is in a file this call created,
    ///   under a name no other live temporary holds; the guard attempts removal
    ///   unless [`Self::commit`] publishes it. A candidate name that exists is
    ///   never opened: exclusive creation turns a collision into a retry under
    ///   a fresh nonce.
    /// - fails: [`CheckpointStoreError::Io`] when a candidate cannot be created
    ///   for any reason but existing, when the write fails — the handle is then
    ///   closed before cleanup of the partial file is attempted — or when
    ///   [`MAX_TEMPORARY_ATTEMPTS`] candidates in a row exist.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real publication, failed rename, a predictable-name
    ///   squatter and four concurrent publishers exercise private creation. The
    ///   predicate checks lexical directory/address placement and an armed
    ///   guard; it does not reread the artifact or force the random collision
    ///   retry path.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    /// - witness: `persistence::tests::a_store_never_writes_through_a_file_it_did_not_create`
    /// - witness: `persistence::tests::concurrent_stores_of_one_address_leave_the_record_and_no_temporary`
    #[spec(
        ensures: |ret| match ret {
            | Ok(ref record) => {
                record.published == Publication::Private
                    && record.path.parent() == Some(root)
                    && record.path.file_name().is_some_and(|name| {
                        let prefix = blake3::Hash::from_bytes(address.0).to_hex();
                        name.as_encoded_bytes().get(.. 64) == Some(prefix.as_str().as_bytes())
                            && name.as_encoded_bytes().get(64 .. 69) == Some(b".tmp-".as_slice())
                    })
            },
            | Err(error) => error == CheckpointStoreError::Io,
        },
    )]
    fn write(
        root: &Path,
        address: CheckpointAddress,
        artifact: &ArtifactBytes,
    ) -> Result<Self, CheckpointStoreError>
    {
        let process = std::process::id();
        for _ in 0 .. MAX_TEMPORARY_ATTEMPTS {
            // A fresh nonce per attempt, so a retry resolves the collision it
            // met instead of meeting it again.
            let nonce = core::hash::BuildHasher::hash_one(&std::hash::RandomState::new(), process);
            let candidate = root.join(alloc::format!(
                "{}.tmp-{process}-{nonce:016x}",
                address.to_hex()
            ));
            let created = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&candidate);
            let mut file = match created {
                | Ok(file) => file,
                | Err(ref error) if failure_of(error) == Failure::AlreadyExists => continue,
                | Err(_error) => return Err(CheckpointStoreError::Io),
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
            written.map_err(|_error| CheckpointStoreError::Io)?;
            return Ok(record);
        }
        Err(CheckpointStoreError::Io)
    }

    /// Rename the record onto `destination`, publishing it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when the rename succeeded; the guard is then
    ///   disarmed. On failure the guard attempts to remove the temporary.
    /// - fails: [`CheckpointStoreError::Io`] when the rename fails.
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
            | Err(error) => error == CheckpointStoreError::Io && self.published == before,
        },
    )]
    fn commit(
        mut self,
        destination: &Path,
    ) -> Result<(), CheckpointStoreError>
    {
        std::fs::rename(&self.path, destination).map_err(|_error| CheckpointStoreError::Io)?;
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

/// A file record: header, then payload.
///
/// # Specification
/// - executable: none — this nominal byte wrapper has no callable boundary;
///   `artifact_bytes` establishes its framing contract.
///
/// # Adequacy
/// - hypothesis: L3 — real file round-trips and mutations of record integrity
///   exercise the envelope. Its constructor checks metadata and payload
///   placement without a second digest computation.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes`
#[repr(transparent)]
struct ArtifactBytes(Vec<u8>);

/// The file record of `payload`: magic, version, address, backend, payload
/// length and payload digest, then the payload.
///
/// # Specification
/// - fails: [`CheckpointStoreError::Rejected`] when the length passes 64 bits.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — file round-trips preserve payloads; address, extent and
///   digest mutations are refused on load. The predicate checks framing and
///   metadata without rehashing the payload; an unrepresentable allocation is
///   unwitnessed.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes`
#[spec(
    ensures: |ret| match ret {
        | Ok(ref artifact) => u64::try_from(payload.0.len()).is_ok_and(|length| {
            FILE_HEADER_LEN.checked_add(payload.0.len()) == Some(artifact.0.len())
                && artifact.0.get(.. 8) == Some(FILE_MAGIC.as_slice())
                && artifact.0.get(8 .. 12) == Some(FILE_VERSION.to_le_bytes().as_slice())
                && artifact.0.get(12 .. 44) == Some(address.0.as_slice())
                && artifact.0.get(44 .. 76) == Some(backend.0.as_slice())
                && artifact.0.get(76 .. 84) == Some(length.to_le_bytes().as_slice())
                && artifact.0.get(FILE_HEADER_LEN ..) == Some(payload.0)
        }),
        | Err(error) => {
            error == CheckpointStoreError::Rejected && u64::try_from(payload.0.len()).is_err()
        },
    },
)]
fn artifact_bytes(
    address: CheckpointAddress,
    backend: BackendArtifact,
    payload: Bytes<'_>,
) -> Result<ArtifactBytes, CheckpointStoreError>
{
    let length =
        u64::try_from(payload.0.len()).map_err(|_overflow| CheckpointStoreError::Rejected)?;
    let mut bytes = Vec::with_capacity(FILE_HEADER_LEN.saturating_add(payload.0.len()));
    bytes.extend_from_slice(FILE_MAGIC);
    bytes.extend_from_slice(&FILE_VERSION.to_le_bytes());
    bytes.extend_from_slice(&address.0);
    bytes.extend_from_slice(&backend.0);
    bytes.extend_from_slice(&length.to_le_bytes());
    bytes.extend_from_slice(blake3::hash(payload.0).as_bytes());
    bytes.extend_from_slice(payload.0);
    Ok(ArtifactBytes(bytes))
}

/// The contents of every item of `program`, in order.
///
/// # Specification
/// - ensures: one content table per source reference, in source order.
///
/// # Adequacy
/// - hypothesis: L3 — independently allocated programs and selected source
///   reorderings retain the ordered reference census. The predicate does not
///   repeat arena projection or claim that unresolved children are persistable.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `persistence::tests::meaningful_program_changes_and_source_order_change_identity`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[spec(
    ensures: |ret| {
        ret.len() == program.references().len()
            && ret
                .iter()
                .zip(program.references())
                .all(|(content, reference)| content.reference() == reference)
    },
)]
fn contents_of(program: &Program) -> Vec<ItemContent>
{
    (0 .. program.layout().items.len())
        .map(|index| {
            encode_item(program.arena(), program.layout(), ItemOrdinal::from(index)).content
        })
        .collect()
}

/// The content address of `program`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the BLAKE3 digest of the program's canonical bytes: its items'
///   references and contents, in order. Independent construction with the same
///   items preserves the address; order, item contents and names all contribute
///   to the digest. Digest inequality is not an injectivity claim.
/// - fails: [`CheckpointStoreError::UnsupportedPersistence`] naming the first
///   unresolved id met.
/// - panics: none.
///
/// # Errors
/// [`CheckpointStoreError::UnsupportedPersistence`] — an item holds an id its
/// arena does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the content-only inputs and the order,
///   separated by two independently built programs, a reordering, a changed
///   value and a renamed key. The executable success facet checks top-level
///   resolution, not a second encoding or hash; nested unresolved ids have
///   separate refusal witnesses.
/// - witness: `persistence::tests::independently_built_programs_have_identical_bytes_and_addresses`
/// - witness: `persistence::tests::meaningful_program_changes_and_source_order_change_identity`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
#[spec(
    ensures: |ret| match ret {
        | Ok(_) => program.items().iter().all(|item| {
            let signature = match item.declaration().signature() {
                | Maybe::Present(id) => program.arena().value_type(id).is_some(),
                | Maybe::Absent(_) => true,
            };
            let body = match item.declaration().body() {
                | Maybe::Present(id) => program.arena().value(id).is_some(),
                | Maybe::Absent(_) => true,
            };
            signature && body
        }),
        | Err(error) => matches!(
            error,
            CheckpointStoreError::UnsupportedPersistence(_) | CheckpointStoreError::Rejected
        ),
    },
)]
#[inline]
pub fn address_of(program: &Program) -> Result<CheckpointAddress, CheckpointStoreError>
{
    let mut hasher = blake3::Hasher::new();
    write_program(&mut hasher, &contents_of(program))?;
    Ok(CheckpointAddress(*hasher.finalize().as_bytes()))
}

/// The canonical bytes of `checkpoints`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the one canonical encoding, which decodes to the supplied set.
/// - fails: unsupported nodes, capped level offsets or unrepresentable counts.
/// - panics: none.
///
/// # Errors
/// A typed refusal naming the unsupported, capped or unrepresentable input.
///
/// # Adequacy
/// - hypothesis: L3 — a finite semantic corpus round-trips its supported forms;
///   one unresolved id of each sort nested inside a resolved item reports its
///   exact refusal. This does not enumerate all possible programs.
/// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
    ensures: |ret| match ret {
        | Err(CheckpointStoreError::LevelOffsetTooLarge { offset }) => {
            u64::from(offset) >= crate::codec::MAX_DECODED_LEVEL_OFFSET
        },
        | Ok(_)
        | Err(CheckpointStoreError::UnsupportedPersistence(_) | CheckpointStoreError::Rejected) => true,
        | Err(_) => false,
    },
)]
#[inline]
pub fn encode_checkpoints(
    checkpoints: &Checkpoints
) -> Result<CheckpointBytes, CheckpointStoreError>
{
    let bytes = crate::codec::encode_checkpoints(checkpoints)?;
    Ok(bytes)
}

/// The checkpoint set `bytes` spell.
///
/// # Specification
/// - requires: nothing — any bytes are admissible.
/// - ensures: the one set whose canonical bytes are exactly `bytes`.
/// - fails: [`CheckpointStoreError::Corrupt`] for truncated, malformed or
///   trailing bytes; [`CheckpointStoreError::LevelOffsetTooLarge`] for an
///   offset at the cap; [`CheckpointStoreError::NonCanonical`] for a payload
///   that parses but is not canonical.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the structural checks, the cap and the
///   canonical comparison, separated by a truncated, a corrupted and an
///   extended encoding, an oversized offset, and three parseable payloads that
///   are not canonical: a set out of order, a table out of discovery order, and
///   a table with an unreached entry.
/// - witness: `persistence::tests::checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes`
/// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
/// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
#[spec(
    ensures: |ret| {
        matches!(
            ret,
            Ok(_)
                | Err(CheckpointStoreError::Corrupt
                    | CheckpointStoreError::NonCanonical
                    | CheckpointStoreError::LevelOffsetTooLarge { .. })
        )
    },
)]
#[inline]
pub fn decode_checkpoints(bytes: &CheckpointBytes) -> Result<Checkpoints, CheckpointStoreError>
{
    let decoded = crate::codec::decode_checkpoints(Bytes(bytes.as_ref()))?;
    Ok(decoded)
}

/// Store `checkpoints` for `program` and tell `observer`.
///
/// # Specification
/// - requires: `checkpoints` are `program`'s.
/// - ensures: on success the set is stored at the program's address and the
///   observer is told; on failure the observer is told nothing.
/// - fails: the address's or the store's error.
/// - panics: propagates a panic from a supplied store or observer.
///
///
/// # Adequacy
/// - hypothesis: L3 — real memory and file stores notify after successful
///   storage; unresolved addressing and failed file publication notify nobody.
///   The precondition checks reference alignment, not full checkpoint
///   provenance; the success predicate does not repeat hashing or invoke the
///   observer.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
/// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
///
/// # Errors
/// As [`address_of`] and [`CheckpointStore::store`].
#[spec(
    requires: checkpoints.items().len() == program.references().len()
        && checkpoints
            .items()
            .iter()
            .zip(program.references())
            .all(|(checkpoint, reference)| checkpoint.content().reference() == reference),
    ensures: |ret| match ret {
        | Ok(_) => program.items().iter().all(|item| {
            let signature = match item.declaration().signature() {
                | Maybe::Present(id) => program.arena().value_type(id).is_some(),
                | Maybe::Absent(_) => true,
            };
            let body = match item.declaration().body() {
                | Maybe::Present(id) => program.arena().value(id).is_some(),
                | Maybe::Absent(_) => true,
            };
            signature && body
        }),
        | Err(_) => true,
    },
)]
#[inline]
pub fn persist<Store, Observer>(
    store: &mut Store,
    program: &Program,
    backend: BackendArtifact,
    checkpoints: &Checkpoints,
    observer: &mut Observer,
) -> Result<CheckpointAddress, CheckpointStoreError>
where
    Store: CheckpointStore,
    Observer: CheckpointObserver,
{
    let address = address_of(program)?;
    store.store(address, backend, checkpoints)?;
    observer.stored(address);
    Ok(address)
}

/// Restore the set stored for `program` at `address` by `backend`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the stored set when `address` is the program's and a record of
///   `backend` is held there; the observer is told of every restore that
///   returns nothing.
/// - provides: `restored::Absent` naming why nothing was restored.
/// - fails: the address's or the store's error.
/// - panics: propagates a panic from a supplied store or observer.
///
///
/// # Adequacy
/// - hypothesis: L3 — matching records restore, while missing, other-backend
///   and other-program requests notify invalidation. The success predicate
///   checks top-level resolution only; generic store contents and callback
///   histories are observed by the real-store witnesses, not replayed in a
///   postcondition.
/// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
/// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
///
/// # Errors
/// As [`address_of`] and [`CheckpointStore::load`].
#[spec(
    ensures: |ret| match ret {
        | Ok(_) => program.items().iter().all(|item| {
            let signature = match item.declaration().signature() {
                | Maybe::Present(id) => program.arena().value_type(id).is_some(),
                | Maybe::Absent(_) => true,
            };
            let body = match item.declaration().body() {
                | Maybe::Present(id) => program.arena().value(id).is_some(),
                | Maybe::Absent(_) => true,
            };
            signature && body
        }),
        | Err(_) => true,
    },
)]
#[inline]
pub fn restore<Store, Observer>(
    store: &mut Store,
    program: &Program,
    address: CheckpointAddress,
    backend: BackendArtifact,
    observer: &mut Observer,
) -> Result<Maybe<Checkpoints, restored::Absent>, CheckpointStoreError>
where
    Store: CheckpointStore,
    Observer: CheckpointObserver,
{
    let own = address_of(program)?;
    if own != address {
        observer.invalidated(address);
        return Ok(Maybe::Absent(restored::Absent::AddressMismatch));
    }
    let loaded = store.load(address, backend)?;
    match loaded {
        | Maybe::Present(checkpoints) => Ok(Maybe::Present(checkpoints)),
        | Maybe::Absent(reason) => {
            observer.invalidated(address);
            Ok(Maybe::Absent(match reason {
                | stored::Absent::NotStored => restored::Absent::NotStored,
                | stored::Absent::OtherBackend => restored::Absent::OtherBackend,
            }))
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::format;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::body;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelOffset;
    use gandr_kernel_strata::LevelVar;
    use gandr_kernel_strata::LevelVarIndex;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GroundSort;
    use quenchant_shape::shape::Maybe;

    use super::BackendArtifact;
    use super::CheckpointAddress;
    use super::CheckpointObserver;
    use super::CheckpointStore as _;
    use super::CheckpointStoreError;
    use super::FileCheckpointStore;
    use super::MemoryCheckpointStore;
    use super::address_of;
    use super::artifact_bytes;
    use super::decode_checkpoints;
    use super::encode_checkpoints;
    use super::persist;
    use super::restore;
    use super::restored;
    use super::stored;
    use crate::boundary::NodeIndex;
    use crate::boundary::Occurrence;
    use crate::boundary::RecordCount;
    use crate::checkpoint::Answer;
    use crate::checkpoint::Checkpoints;
    use crate::checkpoint::ItemCheckpoint;
    use crate::codec::Bytes;
    use crate::codec::CheckpointBytes;
    use crate::codec::UnsupportedPersistence;
    use crate::codec::reference_bytes;
    use crate::content::ContentNode;
    use crate::content::ItemContent;
    use crate::content::Sort;
    use crate::fixture::Digits;
    use crate::fixture::Key;
    use crate::fixture::Label;
    use crate::fixture::Noise;
    use crate::fixture::Position;
    use crate::fixture::Scratch;
    use crate::fixture::checked;
    use crate::fixture::declaration;
    use crate::fixture::every_former;
    use crate::fixture::integer;
    use crate::fixture::integers;
    use crate::fixture::noisy;
    use crate::footprint::footprint_of;
    use crate::region::Item;
    use crate::region::ItemKey;
    use crate::region::Program;
    use crate::region::Reference;
    use crate::typing::Refusal;
    use crate::typing::Typing;

    /// An observer that records what it is told.
    ///
    /// # Specification
    /// - executable: none — the lists retain notifications, not the operations
    ///   that should have emitted them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — successful stores, absent restores and failed
    ///   publication are observed through the recording lists. Distinct missing
    ///   addresses retain notification order; the observer does not judge the
    ///   persistence operation.
    /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
    /// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
    /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
    #[derive(Debug, Default)]
    struct Recording
    {
        /// The addresses stored.
        stored: Vec<CheckpointAddress>,
        /// The addresses whose restore returned nothing.
        invalidated: Vec<CheckpointAddress>,
    }

    impl CheckpointObserver for Recording
    {
        /// Record the stored address.
        ///
        /// # Specification
        /// - ensures: append this stored address without invalidating an
        ///   address.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — successful memory and file persistence append
        ///   notifications; failed publication leaves the list empty. The
        ///   predicate observes length and last address, not a cloned history
        ///   prefix.
        /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
        /// - witness: `persistence::tests::a_failed_file_store_strands_no_temporary_in_the_record_directory`
        #[spec(
            captures: [
                before = self.stored.len(),
                invalidated = self.invalidated.len(),
            ],
            ensures: |ret| {
                before.checked_add(1) == Some(self.stored.len())
                    && self.stored.last() == Some(&address)
                    && self.invalidated.len() == invalidated
            },
        )]
        fn stored(
            &mut self,
            address: CheckpointAddress,
        )
        {
            self.stored.push(address);
        }

        /// Record the invalidated address.
        ///
        /// # Specification
        /// - ensures: append this invalidated address without recording a
        ///   store.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — distinct missing addresses preserve notification
        ///   order; other-backend and other-program restores are also observed.
        ///   The predicate checks append extent and the final address without
        ///   cloning earlier entries.
        /// - witness: `persistence::tests::memory_records_separate_addresses_backends_and_replacements`
        /// - witness: `persistence::tests::supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file`
        #[spec(
            captures: [before = self.invalidated.len(), stored = self.stored.len()],
            ensures: |ret| {
                before.checked_add(1) == Some(self.invalidated.len())
                    && self.invalidated.last() == Some(&address)
                    && self.stored.len() == stored
            },
        )]
        fn invalidated(
            &mut self,
            address: CheckpointAddress,
        )
        {
            self.invalidated.push(address);
        }
    }

    /// The backend every fixture is judged by.
    ///
    /// # Specification
    /// trivial.
    fn backend() -> BackendArtifact
    {
        BackendArtifact::from(b"core-checker".as_slice())
    }

    /// The program `a = 1; b = 2`.
    ///
    /// # Specification
    /// trivial.
    fn pair() -> Program
    {
        integers(CoreArena::new(), &[
            (Key("a"), Digits("1")),
            (Key("b"), Digits("2")),
        ])
    }

    /// The canonical bytes of `checkpoints`.
    ///
    /// # Specification
    /// - requires: the checkpoint set is encodable.
    /// - ensures: the canonical bytes of that set.
    /// - panics: an unencodable fixture violates the precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the finite semantic corpus and deliberately
    ///   noncanonical tables use encodable fixtures. The partial precondition
    ///   checks unresolved main-content nodes only, not support, typing planes
    ///   or machine widths.
    /// - witness: `persistence::tests::canonical_maps_and_supported_semantic_variants_round_trip`
    /// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
    #[spec(
        requires: checkpoints.items().iter().all(|checkpoint| {
            checkpoint
                .content()
                .nodes()
                .iter()
                .all(|node| !matches!(node, &ContentNode::Unresolved(_)))
        }),
    )]
    fn bytes_of(checkpoints: &Checkpoints) -> CheckpointBytes
    {
        encode_checkpoints(checkpoints).expect("supported")
    }

    /// Decode `bytes`.
    ///
    /// # Specification
    /// trivial.
    fn decoded(bytes: &CheckpointBytes) -> Result<Checkpoints, CheckpointStoreError>
    {
        decode_checkpoints(bytes)
    }

    /// A one-item set whose content is `nodes` under a body root of 0.
    ///
    /// # Specification
    /// - ensures: one unsigned, owed item named hand, with body root zero and
    ///   exactly the supplied node table; structural validity is not required.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reversed discovery, unreachable entries and malformed
    ///   root tables reach the decoder. The predicate checks node count and
    ///   fixed metadata without cloning the moved node vector or certifying its
    ///   graph.
    /// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
    /// - witness: `persistence::tests::file_load_rejects_parseable_noncanonical_payload_after_integrity_checks`
    #[spec(
        captures: [count = nodes.len()],
        ensures: |ret| {
            ret.budget() == CheckBudget::DEFAULT
                && ret.items().len() == 1
                && ret.items().first().is_some_and(|checkpoint| {
                    let content = checkpoint.content();
                    content.nodes().len() == count
                        && content.signature() == Maybe::Absent(signature::Absent::Unsigned)
                        && content.body() == Maybe::Present(NodeIndex::from(0_usize))
                        && checkpoint.support().is_empty()
                        && matches!(checkpoint.typing(), &Typing::Owed)
                        && match *content.reference() {
                            | Reference::Item {
                                ref key,
                                occurrence,
                            } => key.as_ref() == b"hand" && usize::from(occurrence) == 0,
                            | _ => false,
                        }
                })
        },
    )]
    fn hand_made(nodes: Vec<ContentNode>) -> Checkpoints
    {
        let content = ItemContent::from_parts(
            Reference::Item {
                key: ItemKey::from("hand"),
                occurrence: Occurrence::from(0_usize),
            },
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(NodeIndex::from(0_usize)),
            nodes,
        );
        let footprint = footprint_of(&content);
        Checkpoints::new(CheckBudget::DEFAULT, vec![ItemCheckpoint::new(
            content,
            footprint,
            Vec::new(),
            Typing::Owed,
        )])
    }

    /// `bytes` with the first occurrence of `from` replaced by `to`.
    ///
    /// # Specification
    /// - requires: from is nonempty and occurs in bytes.
    /// - ensures: replace only its first occurrence, preserving the prefix and
    ///   suffix even when the replacement length differs.
    /// - panics: a missing or empty pattern violates the precondition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — growing and deleting the first of two occurrences
    ///   preserve the surrounding bytes. Canonicality mutations exercise
    ///   equal-width rewrites; the postcondition compares borrowed slices, not
    ///   a rebuilt output buffer.
    /// - witness: `persistence::tests::rewriting_the_first_frame_preserves_unequal_length_neighbors`
    /// - witness: `persistence::tests::checkpoint_decoder_rejects_parseable_noncanonical_payload`
    #[spec(
        requires: !from.as_ref().is_empty(),
        ensures: |ret| {
            bytes
                .as_ref()
                .windows(from.as_ref().len())
                .position(|window| window == from.as_ref())
                .is_some_and(|at| {
                    match (
                        at.checked_add(from.as_ref().len()),
                        at.checked_add(to.as_ref().len()),
                    ) {
                        | (Some(after), Some(end)) => {
                            ret.as_ref().get(.. at) == bytes.as_ref().get(.. at)
                                && ret.as_ref().get(at .. end) == Some(to.as_ref())
                                && ret.as_ref().get(end ..) == bytes.as_ref().get(after ..)
                        },
                        | _ => false,
                    }
                })
        },
    )]
    fn rewritten(
        bytes: &CheckpointBytes,
        from: &CheckpointBytes,
        to: &CheckpointBytes,
    ) -> CheckpointBytes
    {
        let (bytes, from, to) = (bytes.as_ref(), from.as_ref(), to.as_ref());
        let at = bytes
            .windows(from.len())
            .position(|window| window == from)
            .expect("the pattern occurs");
        let mut out = Vec::with_capacity(bytes.len());
        out.extend_from_slice(bytes.get(.. at).expect("in range"));
        out.extend_from_slice(to);
        out.extend_from_slice(
            bytes
                .get(at.saturating_add(from.len()) ..)
                .expect("in range"),
        );
        CheckpointBytes::from(out)
    }

    /// The program of one item `nested` with `signature` and `body`.
    ///
    /// # Specification
    /// - ensures: one item named nested at origin zero retains the supplied
    ///   roots and arena, including deliberately unresolved identifiers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — foreign and opaque children in all four sorts reach
    ///   exact persistence refusals. The predicate checks item identity and
    ///   root slots; it does not clone the moved arena or certify that those
    ///   roots resolve.
    /// - witness: `persistence::tests::nested_process_local_and_opaque_forms_report_exact_errors`
    /// - witness: `persistence::tests::oversized_level_offset_is_refused_with_exact_error`
    #[spec(
        ensures: |ret| {
            ret.items().len() == 1
                && ret.items().first().is_some_and(|item| {
                    item.declaration().signature() == signature && item.declaration().body() == body
                })
                && ret
                    .references()
                    .first()
                    .is_some_and(|reference| match *reference {
                        | Reference::Item {
                            ref key,
                            occurrence,
                        } => key.as_ref() == b"nested" && usize::from(occurrence) == 0,
                        | _ => false,
                    })
        },
    )]
    fn nested(
        arena: CoreArena,
        signature: Maybe<gandr_core_term::ValueTypeId, signature::Absent>,
        body: Maybe<gandr_core_term::ValueId, body::Absent>,
    ) -> Program
    {
        Program::new(arena, vec![Item::new(
            ItemKey::from("nested"),
            declaration(Position(0_usize), signature, body),
        )])
        .expect("one item ascends")
    }

    /// The kind of a typing, as a name.
    ///
    /// # Specification
    /// trivial.
    fn kind(typing: &Typing) -> Key
    {
        Key(match *typing {
            | Typing::Checked { .. } => "checked",
            | Typing::Synthesised { .. } => "synthesised",
            | Typing::Owed => "owed",
            | Typing::Refused(Refusal::PathCode(_)) => "path-code",
            | Typing::Refused(Refusal::TypeMismatch { .. }) => "type-mismatch",
            | Typing::Refused(Refusal::ShapeMismatch { .. }) => "shape-mismatch",
            | Typing::Refused(Refusal::NotSynthesisable { .. }) => "not-synthesisable",
            | Typing::Refused(Refusal::UnknownConstant { .. }) => "unknown-constant",
            | Typing::Refused(Refusal::OutOfFragment { .. }) => "out-of-fragment",
            | Typing::Refused(Refusal::UnboundIndex { .. }) => "unbound-index",
            | Typing::Refused(Refusal::BudgetExceeded { .. }) => "budget-exceeded",
            | Typing::Refused(Refusal::DanglingNode { .. }) => "dangling-node",
            | Typing::Refused(Refusal::AdmissionOrder) => "admission-order",
            | Typing::Refused(Refusal::MachineInvariant) => "machine-invariant",
            | Typing::Refused(Refusal::SortMismatch { .. }) => "sort-mismatch",
            | Typing::Refused(Refusal::LevelMismatch { .. }) => "level-mismatch",
            | Typing::Refused(Refusal::DependentBind { .. }) => "dependent-bind",
            | Typing::Refused(Refusal::Undecided { .. }) => "undecided",
            | Typing::Refused(Refusal::FamilyArity { .. }) => "family-arity",
            | Typing::Refused(Refusal::FamilyArgumentClassifier { .. }) => {
                "family-argument-classifier"
            },
            | Typing::Refused(Refusal::StaticLambdaArgument { .. }) => "static-lambda-argument",
            | Typing::Refused(Refusal::StaticClassifierExpected { .. }) => {
                "static-classifier-expected"
            },
        })
    }

    #[test]
    fn independently_built_programs_have_identical_bytes_and_addresses()
    {
        let entries = [(Key("a"), Digits("1")), (Key("b"), Digits("2"))];
        let mut quiet = integers(CoreArena::new(), &entries);
        let mut loud = integers(noisy(Noise(4)), &entries);
        assert_eq!(
            address_of(&quiet),
            address_of(&loud),
            "the address reads content, never ids"
        );
        assert_eq!(
            bytes_of(&checked(&mut quiet)),
            bytes_of(&checked(&mut loud)),
            "so do the checkpoint bytes"
        );
    }

    #[test]
    fn meaningful_program_changes_and_source_order_change_identity()
    {
        let variants = [
            vec![(Key("a"), Digits("1")), (Key("b"), Digits("2"))],
            vec![(Key("a"), Digits("1")), (Key("b"), Digits("3"))],
            vec![(Key("b"), Digits("2")), (Key("a"), Digits("1"))],
            vec![(Key("a"), Digits("1")), (Key("c"), Digits("2"))],
            vec![(Key("a"), Digits("1"))],
            vec![(Key("a"), Digits("1")), (Key("a"), Digits("2"))],
        ];
        let addresses: BTreeSet<CheckpointAddress> = variants
            .iter()
            .map(|entries| address_of(&integers(CoreArena::new(), entries)).expect("resolved"))
            .collect();
        assert_eq!(
            addresses.len(),
            variants.len(),
            "a value, an order, a key, a deletion and an occurrence each change the address"
        );
    }

    #[test]
    fn canonical_maps_and_supported_semantic_variants_round_trip()
    {
        let checkpoints = checked(&mut every_former(Noise(0)));
        let kinds: BTreeSet<&str> = checkpoints
            .items()
            .iter()
            .map(|checkpoint| kind(checkpoint.typing()).0)
            .collect();
        let per_item: Vec<(&Reference, &str)> = checkpoints
            .items()
            .iter()
            .map(|checkpoint| {
                (
                    checkpoint.content().reference(),
                    kind(checkpoint.typing()).0,
                )
            })
            .collect();
        for expected in [
            "checked",
            "synthesised",
            "owed",
            "type-mismatch",
            "shape-mismatch",
            "not-synthesisable",
            "unknown-constant",
            "out-of-fragment",
            "unbound-index",
            "family-arity",
            "family-argument-classifier",
            "static-lambda-argument",
            "static-classifier-expected",
        ] {
            assert!(
                kinds.contains(expected),
                "the fixture reaches {expected}: {per_item:?}"
            );
        }
        assert!(
            checkpoints.items().iter().any(|checkpoint| checkpoint
                .support()
                .iter()
                .any(|answered| matches!(*answered.answer(), Answer::Typed(ref ty) if ty.nodes().len() > 1))),
            "some support holds a structured answer"
        );
        let bytes = bytes_of(&checkpoints);
        assert_eq!(
            bytes,
            bytes_of(&checked(&mut every_former(Noise(3)))),
            "built after unrelated nodes, the same program has the same bytes"
        );
        assert_eq!(
            decoded(&bytes),
            Ok(checkpoints),
            "and the bytes decode to the set"
        );
    }

    #[test]
    fn universe_sorts_and_levels_round_trip()
    {
        let level = Level::var(LevelVar::new(LevelVarIndex::from(37_u32)))
            .succ()
            .expect("far from the ceiling");
        let mut arena = CoreArena::new();
        let sorts = [
            gandr_core_term::Sort::Ground(GroundSort::Value),
            gandr_core_term::Sort::Ground(GroundSort::Computation),
            gandr_core_term::Sort::Parameter(gandr_core_term::SortParameter::from(2_u32)),
        ];
        let items = sorts
            .into_iter()
            .enumerate()
            .map(|(position, sort)| {
                let universe = arena.value_type_universe(sort, level.clone());
                Item::new(
                    ItemKey::from(format!("universe-{position}").as_str()),
                    declaration(
                        Position(position),
                        Maybe::Present(universe),
                        Maybe::Absent(body::Absent::Hole),
                    ),
                )
            })
            .collect();
        let checkpoints = checked(&mut Program::new(arena, items).expect("positions ascend"));
        let tables: Vec<Vec<ContentNode>> = checkpoints
            .items()
            .iter()
            .map(|checkpoint| checkpoint.content().nodes().to_vec())
            .collect();
        let expected: Vec<Vec<ContentNode>> = sorts
            .into_iter()
            .map(|sort| {
                vec![ContentNode::Universe {
                    sort,
                    level: level.clone(),
                }]
            })
            .collect();
        assert_eq!(
            expected, tables,
            "each signature's content is its universe, sort and level both"
        );
        assert_eq!(
            decoded(&bytes_of(&checkpoints)),
            Ok(checkpoints),
            "and each sort and its level round trip"
        );
    }

    #[test]
    fn oversized_level_offset_is_refused_with_exact_error()
    {
        let at_offset = |offset: u64| {
            let mut level = Level::var(LevelVar::new(LevelVarIndex::from(0_u32)));
            for _ in 0 .. offset {
                level = level.succ().expect("far from the ceiling");
            }
            let mut arena = CoreArena::new();
            let universe =
                arena.value_type_universe(gandr_core_term::Sort::Ground(GroundSort::Value), level);
            let mut program = Program::new(arena, vec![Item::new(
                ItemKey::from("universe"),
                declaration(
                    Position(0_usize),
                    Maybe::Present(universe),
                    Maybe::Absent(body::Absent::Hole),
                ),
            )])
            .expect("one item ascends");
            checked(&mut program)
        };
        let under = at_offset(4095_u64);
        assert_eq!(
            decoded(&bytes_of(&under)),
            Ok(under),
            "an offset under the cap round trips"
        );
        let capped = at_offset(4096_u64);
        let refusal = CheckpointStoreError::LevelOffsetTooLarge {
            offset: LevelOffset::from(4096_u64),
        };
        assert_eq!(encode_checkpoints(&capped), Err(refusal));
        let raw = crate::codec::checkpoint_frame(&capped).expect("raw capped frame");
        assert_eq!(decoded(&raw), Err(refusal));
    }

    #[test]
    fn checkpoint_decoder_rejects_truncation_corruption_and_trailing_bytes()
    {
        let bytes = Vec::from(bytes_of(&checked(&mut pair())));
        for length in 0 .. bytes.len() {
            let prefix = bytes.get(.. length).expect("in range").to_vec();
            assert_eq!(
                decoded(&CheckpointBytes::from(prefix)),
                Err(CheckpointStoreError::Corrupt),
                "a prefix of {length} bytes is corrupt"
            );
        }
        let mut corrupted = bytes.clone();
        if let Some(first) = corrupted.first_mut() {
            *first ^= 0xFF_u8;
        }
        assert_eq!(
            decoded(&CheckpointBytes::from(corrupted)),
            Err(CheckpointStoreError::Corrupt),
            "a broken magic"
        );
        let mut extended = bytes;
        extended.push(0_u8);
        assert_eq!(
            decoded(&CheckpointBytes::from(extended)),
            Err(CheckpointStoreError::Corrupt),
            "a trailing byte"
        );
    }

    #[test]
    fn checkpoint_decoder_rejects_parseable_noncanonical_payload()
    {
        // r = (a, b): the footprint lists a then b; swapped, the set parses
        // and sorts back, so the payload is not the spelling of its value.
        let mut arena = CoreArena::new();
        let a = arena.value_literal(integer(Digits("1")));
        let b = arena.value_literal(integer(Digits("2")));
        let first = arena.value_constant(ConstantIndex::from(0_usize));
        let second = arena.value_constant(ConstantIndex::from(1_usize));
        let pair = arena.value_pair(first, second);
        let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
        let mut program = Program::new(arena, vec![
            Item::new(
                ItemKey::from("a"),
                declaration(Position(0_usize), unsigned(), Maybe::Present(a)),
            ),
            Item::new(
                ItemKey::from("b"),
                declaration(Position(1_usize), unsigned(), Maybe::Present(b)),
            ),
            Item::new(
                ItemKey::from("r"),
                declaration(Position(2_usize), unsigned(), Maybe::Present(pair)),
            ),
        ])
        .expect("positions ascend");
        let bytes = bytes_of(&checked(&mut program));
        let reference = |key: &str| {
            Vec::from(reference_bytes(&Reference::Item {
                key: ItemKey::from(key),
                occurrence: Occurrence::from(0_usize),
            }))
        };
        let ordered = CheckpointBytes::from([reference("a"), reference("b")].concat());
        let swapped = CheckpointBytes::from([reference("b"), reference("a")].concat());
        assert_eq!(
            decoded(&rewritten(&bytes, &ordered, &swapped)),
            Err(CheckpointStoreError::NonCanonical),
            "a set out of order"
        );

        let literal = |digits: &'static str| ContentNode::Literal(integer(Digits(digits)));
        let out_of_discovery = hand_made(vec![
            ContentNode::Pair(NodeIndex::from(2_usize), NodeIndex::from(1_usize)),
            literal("1"),
            literal("2"),
        ]);
        let raw = crate::codec::checkpoint_frame(&out_of_discovery).expect("raw reordered table");
        assert_eq!(decoded(&raw), Err(CheckpointStoreError::NonCanonical));
        let unreached = hand_made(vec![literal("1"), literal("2")]);
        let raw = crate::codec::checkpoint_frame(&unreached).expect("raw unreachable node");
        assert_eq!(decoded(&raw), Err(CheckpointStoreError::NonCanonical));
    }

    #[test]
    fn file_load_rejects_parseable_noncanonical_payload_after_integrity_checks()
    {
        let scratch = Scratch::new(Label("noncanonical-file"));
        let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
        let address = address_of(&pair()).expect("resolved");
        let payload = crate::codec::checkpoint_frame(&hand_made(vec![
            ContentNode::Literal(integer(Digits("1"))),
            ContentNode::Literal(integer(Digits("2"))),
        ]))
        .expect("raw noncanonical table");
        let artifact =
            artifact_bytes(address, backend(), Bytes(payload.as_ref())).expect("representable");
        std::fs::write(store.record_path(address), &artifact.0).expect("write");
        assert_eq!(
            store.load(
                address,
                BackendArtifact::from(b"another backend".as_slice())
            ),
            Err(CheckpointStoreError::NonCanonical),
            "integrity passes; decoding fails before the backend mismatch is considered"
        );
    }

    #[test]
    fn a_failed_file_store_strands_no_temporary_in_the_record_directory()
    {
        let scratch = Scratch::new(Label("failed-store"));
        let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
        let mut program = pair();
        let address = address_of(&program).expect("resolved");
        std::fs::create_dir_all(store.record_path(address)).expect("occupy the record path");
        let checkpoints = checked(&mut program);
        let mut observer = Recording::default();
        assert_eq!(
            persist(&mut store, &program, backend(), &checkpoints, &mut observer),
            Err(CheckpointStoreError::Io),
            "the rename onto a directory fails"
        );
        assert!(
            observer.stored.is_empty(),
            "a failed publication is not observed as stored"
        );
        assert!(
            observer.invalidated.is_empty(),
            "storage does not invalidate a restore"
        );
        assert_eq!(
            scratch.entries(),
            [address.to_hex()],
            "only the occupying directory remains"
        );
    }

    #[test]
    fn a_store_never_writes_through_a_file_it_did_not_create()
    {
        let scratch = Scratch::new(Label("squatter"));
        let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
        let mut program = pair();
        let address = address_of(&program).expect("resolved");
        let hex = address.to_hex();
        let squatters = [
            format!("{hex}.tmp"),
            format!("{hex}.tmp-{}", std::process::id()),
            format!("{hex}.tmp-{}-0000000000000000", std::process::id()),
        ];
        for name in &squatters {
            std::fs::write(scratch.path().join(name), b"squatter").expect("plant");
        }
        let checkpoints = checked(&mut program);
        store
            .store(address, backend(), &checkpoints)
            .expect("the store succeeds");
        for name in &squatters {
            assert_eq!(
                std::fs::read(scratch.path().join(name)).expect("still there"),
                b"squatter",
                "{name} is byte-identical"
            );
        }
        assert_eq!(
            store.load(address, backend()),
            Ok(Maybe::Present(checkpoints)),
            "the record was published beside them"
        );
        assert_eq!(
            scratch.entries().len(),
            squatters.len() + 1,
            "and nothing else"
        );
    }

    #[test]
    fn concurrent_stores_of_one_address_leave_the_record_and_no_temporary()
    {
        let scratch = Scratch::new(Label("concurrent"));
        let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
        let mut program = pair();
        let address = address_of(&program).expect("resolved");
        let checkpoints = checked(&mut program);
        std::thread::scope(|scope| {
            for _ in 0_usize .. 4_usize {
                let mut store = store.clone();
                let checkpoints = &checkpoints;
                let _handle = scope.spawn(move || {
                    for _ in 0_usize .. 16_usize {
                        store
                            .store(address, backend(), checkpoints)
                            .expect("every store succeeds");
                    }
                });
            }
        });
        assert_eq!(
            scratch.entries(),
            [address.to_hex()],
            "one record, no temporary"
        );
        assert_eq!(
            store.load(address, backend()),
            Ok(Maybe::Present(checkpoints)),
            "and it is whole"
        );
    }

    #[test]
    fn supported_nonempty_checkpoints_round_trip_in_memory_and_reopened_file()
    {
        let mut program = every_former(Noise(0));
        let checkpoints = checked(&mut program);
        let address = address_of(&program).expect("resolved");
        let other = BackendArtifact::from(b"another checker".as_slice());
        let mut observer = Recording::default();

        let mut memory = MemoryCheckpointStore::default();
        assert_eq!(
            persist(
                &mut memory,
                &program,
                backend(),
                &checkpoints,
                &mut observer
            ),
            Ok(address),
            "persisted at the program's address"
        );
        assert_eq!(observer.stored, [address], "and the observer told");
        assert_eq!(
            restore(&mut memory, &program, address, backend(), &mut observer),
            Ok(Maybe::Present(checkpoints.clone())),
            "memory round trip"
        );
        assert_eq!(
            memory.load(address, other),
            Ok(Maybe::Absent(stored::Absent::OtherBackend)),
            "another backend's record is not this one's"
        );

        let scratch = Scratch::new(Label("round-trip"));
        let mut file = FileCheckpointStore::open(scratch.path()).expect("open");
        let _address = persist(&mut file, &program, backend(), &checkpoints, &mut observer)
            .expect("persisted");
        drop(file);
        let mut reopened = FileCheckpointStore::open(scratch.path()).expect("reopen");
        assert_eq!(
            restore(&mut reopened, &program, address, backend(), &mut observer),
            Ok(Maybe::Present(checkpoints)),
            "file round trip through a reopened store"
        );
        assert_eq!(
            restore(&mut reopened, &program, address, other, &mut observer),
            Ok(Maybe::Absent(restored::Absent::OtherBackend)),
            "the backend keys the record"
        );
        assert_eq!(
            restore(&mut reopened, &pair(), address, backend(), &mut observer),
            Ok(Maybe::Absent(restored::Absent::AddressMismatch)),
            "an address is restored only for its own program"
        );
        assert_eq!(
            observer.invalidated,
            [address, address],
            "each empty restore is observed"
        );
    }

    #[test]
    fn nested_process_local_and_opaque_forms_report_exact_errors()
    {
        // Ids past anything the fixture's arena, or the checker's atoms in it,
        // will hold: each resolves in this arena and in no program's.
        let mut foreign = noisy(Noise(64));
        let foreign_value = foreign.value_unit();
        let foreign_unit = foreign.value_unit();
        let foreign_computation = foreign.computation_return(foreign_unit);
        let foreign_value_type = foreign.value_type_unit();
        let foreign_comp_type = foreign.comp_type_returner(foreign_value_type);

        let mut programs: Vec<(Sort, Program)> = Vec::new();
        let mut arena = CoreArena::new();
        let literal = arena.value_literal(integer(Digits("1")));
        let pair = arena.value_pair(literal, foreign_value);
        programs.push((
            Sort::Value,
            nested(
                arena,
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(pair),
            ),
        ));
        let mut arena = CoreArena::new();
        let thunk = arena.value_thunk(foreign_computation);
        programs.push((
            Sort::Computation,
            nested(
                arena,
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(thunk),
            ),
        ));
        let mut arena = CoreArena::new();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let product = arena.value_type_product(integer_type, foreign_value_type);
        programs.push((
            Sort::ValueType,
            nested(
                arena,
                Maybe::Present(product),
                Maybe::Absent(body::Absent::Hole),
            ),
        ));
        let mut arena = CoreArena::new();
        let thunk_type = arena.value_type_thunk(foreign_comp_type);
        programs.push((
            Sort::CompType,
            nested(
                arena,
                Maybe::Present(thunk_type),
                Maybe::Absent(body::Absent::Hole),
            ),
        ));

        for (sort, mut program) in programs {
            let refused = Err(CheckpointStoreError::UnsupportedPersistence(
                UnsupportedPersistence::Dangling(sort),
            ));
            assert_eq!(
                address_of(&program),
                refused,
                "no address for a {sort:?} id of another arena"
            );
            let checkpoints = checked(&mut program);
            assert_eq!(
                encode_checkpoints(&checkpoints).map(|_bytes| ()),
                refused.map(|_address| ()),
                "no bytes either"
            );
            let mut memory = MemoryCheckpointStore::default();
            let mut observer = Recording::default();
            assert_eq!(
                persist(
                    &mut memory,
                    &program,
                    backend(),
                    &checkpoints,
                    &mut observer
                ),
                refused,
                "persisting refuses with the same error"
            );
            assert_eq!(
                memory.record_count(),
                RecordCount::from(0_usize),
                "nothing is stored"
            );
            assert!(observer.stored.is_empty(), "and nothing is observed");
        }
    }

    #[test]
    fn file_load_distinguishes_not_found_from_other_read_errors()
    {
        let scratch = Scratch::new(Label("not-found"));
        let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
        let address = address_of(&pair()).expect("resolved");
        assert_eq!(
            store.load(address, backend()),
            Ok(Maybe::Absent(stored::Absent::NotStored)),
            "a missing record is absent, not an error"
        );
        std::fs::create_dir_all(store.record_path(address)).expect("occupy the record path");
        assert_eq!(
            store.load(address, backend()),
            Err(CheckpointStoreError::Io),
            "a record path that cannot be read is an error"
        );
    }

    #[test]
    fn file_load_rejects_path_mismatch_corruption_truncation_and_trailing_bytes()
    {
        let scratch = Scratch::new(Label("integrity"));
        let mut store = FileCheckpointStore::open(scratch.path()).expect("open");
        let mut program = pair();
        let address = address_of(&program).expect("resolved");
        store
            .store(address, backend(), &checked(&mut program))
            .expect("stored");
        let path = store.record_path(address);
        let record = std::fs::read(&path).expect("read");
        let elsewhere =
            address_of(&integers(CoreArena::new(), &[(Key("c"), Digits("3"))])).expect("resolved");
        std::fs::write(store.record_path(elsewhere), &record).expect("copy");
        assert_eq!(
            store.load(elsewhere, backend()),
            Err(CheckpointStoreError::Corrupt),
            "a record under another address's name"
        );
        let mut flipped = record.clone();
        if let Some(last) = flipped.last_mut() {
            *last ^= 0x01_u8;
        }
        let truncated = record.get(.. record.len() - 1).expect("in range").to_vec();
        let mut extended = record;
        extended.push(0_u8);
        for (damaged, what) in [
            (flipped, "a flipped payload byte"),
            (truncated, "a truncated record"),
            (extended, "a trailing byte"),
        ] {
            std::fs::write(&path, &damaged).expect("damage");
            assert_eq!(
                store.load(address, backend()),
                Err(CheckpointStoreError::Corrupt),
                "{what}"
            );
        }
    }

    #[test]
    fn memory_records_separate_addresses_backends_and_replacements()
    {
        let mut program = pair();
        let first = crate::checkpoint::check_program(&mut program, CheckBudget::from(1_usize))
            .expect("first budget checked")
            .checkpoints()
            .clone();
        let second = crate::checkpoint::check_program(&mut program, CheckBudget::from(2_usize))
            .expect("second budget checked")
            .checkpoints()
            .clone();
        let address = address_of(&program).expect("resolved");
        let lower = BackendArtifact([0; 32]);
        let upper = BackendArtifact([u8::MAX; 32]);
        let mut store = MemoryCheckpointStore::default();
        let mut observer = Recording::default();
        assert_eq!(
            restore(&mut store, &program, address, lower, &mut observer),
            Ok(Maybe::Absent(restored::Absent::NotStored))
        );
        assert_eq!(store.store(address, upper, &second), Ok(()));
        assert_eq!(
            store.load(address, lower),
            Ok(Maybe::Absent(stored::Absent::OtherBackend)),
            "the inclusive upper digest is in the address range"
        );
        assert_eq!(store.store(address, lower, &first), Ok(()));
        assert_eq!(
            store.record_count(),
            crate::boundary::RecordCount::from(2_usize)
        );
        assert_eq!(store.load(address, lower), Ok(Maybe::Present(first)));
        assert_eq!(
            store.load(address, upper),
            Ok(Maybe::Present(second.clone()))
        );
        assert_eq!(store.store(address, lower, &second), Ok(()));
        assert_eq!(
            store.record_count(),
            crate::boundary::RecordCount::from(2_usize)
        );
        assert_eq!(
            store.load(address, lower),
            Ok(Maybe::Present(second.clone()))
        );
        assert_eq!(store.load(address, upper), Ok(Maybe::Present(second)));

        let mut empty = integers(CoreArena::new(), &[]);
        let empty_address = address_of(&empty).expect("empty program resolves");
        assert_eq!(
            restore(&mut store, &empty, empty_address, lower, &mut observer),
            Ok(Maybe::Absent(restored::Absent::NotStored)),
            "records at another address do not occupy this range"
        );
        assert_eq!(observer.invalidated, [address, empty_address]);
        assert!(observer.stored.is_empty());
        let empty_set = checked(&mut empty);
        assert_eq!(store.store(empty_address, lower, &empty_set), Ok(()));
        assert_eq!(
            store.load(empty_address, upper),
            Ok(Maybe::Absent(stored::Absent::OtherBackend)),
            "the inclusive lower digest is in its own address range"
        );
        assert_eq!(
            store.load(empty_address, lower),
            Ok(Maybe::Present(empty_set))
        );
        assert_eq!(
            store.record_count(),
            crate::boundary::RecordCount::from(3_usize)
        );
    }

    #[test]
    fn opening_an_existing_file_as_a_directory_fails_without_changing_it()
    {
        let scratch = Scratch::new(Label("open-file"));
        std::fs::create_dir_all(scratch.path()).expect("fixture directory");
        let path = scratch.path().join("occupied");
        std::fs::write(&path, b"retained bytes").expect("create occupied file");
        assert_eq!(
            FileCheckpointStore::open(&path),
            Err(CheckpointStoreError::Io)
        );
        assert_eq!(
            std::fs::read(&path).expect("read occupied file"),
            b"retained bytes"
        );
    }

    #[test]
    fn rewriting_the_first_frame_preserves_unequal_length_neighbors()
    {
        let bytes = CheckpointBytes::from(vec![8, 1, 2, 3, 1, 2, 4]);
        let pattern = CheckpointBytes::from(vec![1, 2]);
        let grown = rewritten(&bytes, &pattern, &CheckpointBytes::from(vec![9, 10, 11]));
        assert_eq!(grown.as_ref(), &[8, 9, 10, 11, 3, 1, 2, 4]);
        let deleted = rewritten(&bytes, &pattern, &CheckpointBytes::from(Vec::new()));
        assert_eq!(deleted.as_ref(), &[8, 3, 1, 2, 4]);
    }

    #[test]
    fn stores_refuse_capped_levels_without_replacing_records()
    {
        let mut level = Level::var(LevelVar::new(LevelVarIndex::from(0_u32)));
        for _ in 0 .. crate::codec::MAX_DECODED_LEVEL_OFFSET {
            level = level.succ().expect("representable level");
        }
        let mut arena = CoreArena::new();
        let universe =
            arena.value_type_universe(gandr_core_term::Sort::Ground(GroundSort::Value), level);
        let mut capped_program = nested(
            arena,
            Maybe::Present(universe),
            Maybe::Absent(body::Absent::Hole),
        );
        let capped = checked(&mut capped_program);
        let mut program = pair();
        let valid = checked(&mut program);
        let address = address_of(&program).expect("resolved address");
        let refusal = CheckpointStoreError::LevelOffsetTooLarge {
            offset: LevelOffset::from(crate::codec::MAX_DECODED_LEVEL_OFFSET),
        };

        let mut memory = MemoryCheckpointStore::default();
        assert_eq!(memory.store(address, backend(), &valid), Ok(()));
        assert_eq!(memory.store(address, backend(), &capped), Err(refusal));
        assert_eq!(
            memory.record_count(),
            crate::boundary::RecordCount::from(1_usize)
        );
        let loaded = memory.load(address, backend()).expect("old memory record");
        assert!(matches!(loaded, Maybe::Present(ref checkpoints) if checkpoints == &valid));

        let scratch = Scratch::new(Label("capped-store"));
        let mut file = FileCheckpointStore::open(scratch.path()).expect("open");
        assert_eq!(file.store(address, backend(), &valid), Ok(()));
        let before = std::fs::read(file.record_path(address)).expect("old file record");
        assert_eq!(file.store(address, backend(), &capped), Err(refusal));
        assert_eq!(
            std::fs::read(file.record_path(address)).expect("retained file record"),
            before
        );
        assert_eq!(scratch.entries(), [address.to_hex()]);
        let loaded = file.load(address, backend()).expect("old file checkpoints");
        assert!(matches!(loaded, Maybe::Present(ref checkpoints) if checkpoints == &valid));
    }
}
