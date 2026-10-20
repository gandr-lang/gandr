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
//!
//! A capped level cannot replace a readable record. The file record is a header
//! — magic, version, address, backend, length and payload digest — then the
//! payload; the temporary takes a fresh random name, and the store never opens
//! a file it did not create. The store is atomic, not durable: it does not
//! synchronise to the device. `CheckpointStore` is the seam where the storage
//! value plane takes over from the file store, persisting checkpoint sets as
//! values with the storage tier's own integrity and retention.
//!
//! # Decisions
//!
//! | Decision | Alternatives | Reversal |
//! | -------- | ------------ | -------- |
//! | A crate-local canonical binary encoding with a canonicality check | a serialisation framework, which would add a dependency and admit several spellings of one value | the storage tier hosts session checkpoints |
//! | Check the decoder’s level bound before checkpoint encoding | publish records that cannot reload; unbounded decoding; decode an extra copy before storing | level reconstruction no longer requires one successor per offset and the decoder can safely admit the full range |
//! | BLAKE3 through the workspace `blake3` entry, the digest the storage tier uses | the storage tier's digest wrapper, which a `core` crate cannot depend on under the layering; a second hash function | the digest moves to a layer below both |
//! | Exclusive temporary, then rename | write in place; a fixed temporary name, which a squatter or a concurrent store could hijack | a consumer needs durability, which adds a sync before and after the rename |

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
            CodecError::Corrupt => Self::Corrupt,
            CodecError::NonCanonical => Self::NonCanonical,
            CodecError::LevelOffsetTooLarge { offset } => Self::LevelOffsetTooLarge { offset },
            CodecError::Unsupported(form) => Self::UnsupportedPersistence(form),
            CodecError::Unrepresentable => Self::Rejected,
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
            Self::Rejected => f.write_str("the checkpoint record cannot be represented"),
            Self::UnsupportedPersistence(form) => write!(f, "cannot persist: {form}"),
            Self::Corrupt => f.write_str("the checkpoint record is corrupt"),
            Self::LevelOffsetTooLarge { offset } => {
                write!(
                    f,
                    "a level offset of {} passes the decoder's cap",
                    u64::from(offset)
                )
            },
            Self::NonCanonical => f.write_str("the checkpoint payload is not canonical"),
            Self::Io => f.write_str("the checkpoint store's file system failed"),
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body and the check each open the ordered range of one address's records to its first entry, one logarithmic descent"
        )
    )]
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
            Ok(bytes) => bytes,
            Err(ref error) if failure_of(error) == Failure::NotFound => {
                return Ok(Maybe::Absent(stored::Absent::NotStored));
            },
            Err(_error) => return Err(CheckpointStoreError::Io),
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
                Ok(file) => file,
                Err(ref error) if failure_of(error) == Failure::AlreadyExists => continue,
                Err(_error) => return Err(CheckpointStoreError::Io),
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
match *(item.declaration().content()) {
gandr_core_checker::DeclarationContent::Value {ref signature,ref body} => {
        let signature = match *signature {Maybe::Present(id) => program.arena().value_type(id).is_some(),Maybe::Absent(_) => true};
        let body = match *body {Maybe::Present(id) => program.arena().value(id).is_some(),Maybe::Absent(_) => true};
        signature && body
    },
gandr_core_checker::DeclarationContent::Data(ref signature) => signature.parameters().iter().chain(signature.constructors().iter().flatten()).chain(core::iter::once(&signature.kind())).all(|&id| program.arena().value_type(id).is_some()),
gandr_core_checker::DeclarationContent::Abstract(sealed) => program.arena().value_type(sealed.kind()).is_some() && program.arena().value_type(sealed.representation()).is_some(),
gandr_core_checker::DeclarationContent::World => true,
gandr_core_checker::DeclarationContent::Codata(_) => false,
}
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
match *(item.declaration().content()) {
gandr_core_checker::DeclarationContent::Value {ref signature,ref body} => {
        let signature = match *signature {Maybe::Present(id) => program.arena().value_type(id).is_some(),Maybe::Absent(_) => true};
        let body = match *body {Maybe::Present(id) => program.arena().value(id).is_some(),Maybe::Absent(_) => true};
        signature && body
    },
gandr_core_checker::DeclarationContent::Data(ref signature) => signature.parameters().iter().chain(signature.constructors().iter().flatten()).chain(core::iter::once(&signature.kind())).all(|&id| program.arena().value_type(id).is_some()),
gandr_core_checker::DeclarationContent::Abstract(sealed) => program.arena().value_type(sealed.kind()).is_some() && program.arena().value_type(sealed.representation()).is_some(),
gandr_core_checker::DeclarationContent::World => true,
gandr_core_checker::DeclarationContent::Codata(_) => false,
}
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
match *(item.declaration().content()) {
gandr_core_checker::DeclarationContent::Value {ref signature,ref body} => {
        let signature = match *signature {Maybe::Present(id) => program.arena().value_type(id).is_some(),Maybe::Absent(_) => true};
        let body = match *body {Maybe::Present(id) => program.arena().value(id).is_some(),Maybe::Absent(_) => true};
        signature && body
    },
gandr_core_checker::DeclarationContent::Data(ref signature) => signature.parameters().iter().chain(signature.constructors().iter().flatten()).chain(core::iter::once(&signature.kind())).all(|&id| program.arena().value_type(id).is_some()),
gandr_core_checker::DeclarationContent::Abstract(sealed) => program.arena().value_type(sealed.kind()).is_some() && program.arena().value_type(sealed.representation()).is_some(),
gandr_core_checker::DeclarationContent::World => true,
gandr_core_checker::DeclarationContent::Codata(_) => false,
}
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
        Maybe::Present(checkpoints) => Ok(Maybe::Present(checkpoints)),
        Maybe::Absent(reason) => {
            observer.invalidated(address);
            Ok(Maybe::Absent(match reason {
                stored::Absent::NotStored => restored::Absent::NotStored,
                stored::Absent::OtherBackend => restored::Absent::OtherBackend,
            }))
        },
    }
}

#[cfg(test)]
mod tests;
