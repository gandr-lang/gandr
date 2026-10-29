//! The kernel's recorded verdicts on disk: one file per receipt, named by the
//! BLAKE3 digest of its bytes, in a directory the driver names.
//!
//! Each file is a record of [`crate::record`] under no key: the frame checks
//! the receipt's length and digest before the receipt is decoded.
//!
//! The store is untrusted. It answers, for a key, the receipt whose records
//! hold it, and the kernel verifies that receipt's signature, and that its
//! signer is one the run's policy lists, before it believes a record
//! ([`gandr_kernel_core::verdict`]). A file whose frame or receipt does not
//! read is counted and passed over: a damaged record costs a replay, never a
//! verdict. A file the store wrote before the frame is such a file.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the store is untrusted by naming rule, and its
//!   integrity never admits.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::Receipt;
use gandr_kernel_core::verdict::ReceiptSignature;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::VerdictImage;
use gandr_kernel_core::verdict::VerdictKey;
use gandr_kernel_core::verdict::VerdictRecord;
use gandr_kernel_core::verdict::VerdictSource;
use gandr_kernel_core::verdict::stored;
use quenchant_shape::shape::Maybe;

use crate::codec::Bytes;
use crate::record;
use crate::record::Format;
use crate::record::Length;
use crate::record::Payload;
use crate::record::RecordName;
use crate::record::Spelling;

/// The receipt record's format.
const RECEIPTS: Format = Format {
    magic: *b"GVRFILE\0",
    version: 1,
    key: 0,
};

/// The byte length of a receipt's signer, signature and record count.
const SIGNED_LEN: usize = 104;

/// The byte length of a receipt record's key and verdict length.
const RECORD_LEN: usize = 40;

/// Why the store could not do what it was asked.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum VerdictStoreError
{
    /// The directory could not be created or listed.
    Unopened,
    /// A receipt could not be written into it.
    Unwritten,
}

/// How many files the store passed over because they did not read as a
/// receipt.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DamagedCount(usize);

impl From<DamagedCount> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: DamagedCount) -> Self
    {
        count.0
    }
}

/// The receipts a directory holds, indexed by every key their records hold.
///
/// # Specification
/// - ensures: [`VerdictSource::receipts`] answers, for a key, every receipt
///   read from the directory when [`FileVerdictStore::open`] ran whose records
///   hold it.
/// - provides: the verdicts a run recalls from, and the place it records its
///   own.
/// - panics: none.
/// - executable: none — the index's agreement with the directory is a fact
///   about the file system at open.
///
/// # Adequacy
/// - hypothesis: L3 — a receipt kept by one store is answered by another opened
///   over the same directory, two signers' receipts over the same records are
///   both answered, and a damaged file is passed over.
/// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
/// - witness: `verdicts::tests::every_receipt_kept_for_a_key_is_answered`
/// - witness: `verdicts::tests::a_damaged_file_is_passed_over`
#[derive(Clone, Debug)]
pub struct FileVerdictStore
{
    /// The directory holding the receipts.
    root: PathBuf,
    /// Every receipt read at open, by each key its records hold.
    index: BTreeMap<VerdictKey, Vec<Arc<StoredReceipt>>>,
    /// How many files did not read as a receipt.
    damaged: DamagedCount,
}

impl FileVerdictStore
{
    /// Open or create the directory at `path` and read every receipt it
    /// holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the directory exists; the index holds every file named by a
    ///   record's name whose frame and receipt read, and the damaged count
    ///   every such file whose frame or receipt does not. Temporaries and other
    ///   names are left alone.
    /// - fails: [`VerdictStoreError::Unopened`] when the directory cannot be
    ///   created or listed.
    /// - panics: propagates a panic from the supplied `AsRef` implementation.
    ///
    /// # Errors
    /// [`VerdictStoreError::Unopened`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FileVerdictStore`].
    /// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
    /// - witness: `verdicts::tests::a_damaged_file_is_passed_over`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Ok(_) | Err(VerdictStoreError::Unopened)))]
    pub fn open<Location>(path: Location) -> Result<Self, VerdictStoreError>
    where
        Location: AsRef<Path>,
    {
        let root = path.as_ref().to_path_buf();
        std::fs::create_dir_all(&root).map_err(|_error| VerdictStoreError::Unopened)?;
        let mut index = BTreeMap::new();
        let mut damaged = 0_usize;
        for entry in std::fs::read_dir(&root).map_err(|_error| VerdictStoreError::Unopened)? {
            let Ok(entry) = entry
            else {
                continue;
            };
            if RecordName::spelling(&entry.file_name()) != Spelling::Record {
                continue;
            }
            let read = std::fs::read(entry.path());
            let Maybe::Present(receipt) =
                read.as_deref()
                    .map_or(
                        Maybe::Absent(stored::Absent::Unrecorded),
                        |bytes| match RECEIPTS.read(Bytes(bytes)) {
                            Maybe::Present(framed) => decode(framed.payload),
                            Maybe::Absent(_) => Maybe::Absent(stored::Absent::Unrecorded),
                        },
                    )
            else {
                damaged = damaged.saturating_add(1);
                continue;
            };
            let receipt = Arc::new(receipt);
            for record in receipt.records() {
                index
                    .entry(record.key())
                    .or_insert_with(Vec::new)
                    .push(Arc::clone(&receipt));
            }
        }
        Ok(Self {
            root,
            index,
            damaged: DamagedCount(damaged),
        })
    }

    /// Write `stored` into the directory, named by the digest of its bytes,
    /// for a store opened later to read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the directory holds a file whose bytes read back
    ///   as `stored`; this store's index is unchanged.
    /// - fails: [`VerdictStoreError::Unwritten`] when the file cannot be
    ///   written or published.
    /// - panics: none.
    ///
    /// # Errors
    /// [`VerdictStoreError::Unwritten`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FileVerdictStore`].
    /// - witness: `verdicts::tests::a_kept_receipt_is_answered_after_reopening`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Ok(()) | Err(VerdictStoreError::Unwritten)))]
    pub fn keep(
        &self,
        stored: &StoredReceipt,
    ) -> Result<(), VerdictStoreError>
    {
        let reserve = stored.records().iter().fold(SIGNED_LEN, |sum, record| {
            sum.saturating_add(RECORD_LEN)
                .saturating_add(record.encoded().as_ref().len())
        });
        let bytes = RECEIPTS
            .frame(Bytes(&[]), Length(reserve), |out| encode(stored, out))
            .map_err(|_fault| VerdictStoreError::Unwritten)?;
        record::publish(&self.root, &bytes.named_by_digest(), &bytes)
            .map_err(|_fault| VerdictStoreError::Unwritten)
    }

    /// How many files did not read as a receipt at open.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn damaged(&self) -> DamagedCount
    {
        self.damaged
    }
}

impl VerdictSource for FileVerdictStore
{
    /// The receipts read at open whose records hold `key`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn receipts(
        &self,
        key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        self.index.get(&key).map_or(&[], Vec::as_slice)
    }
}

/// Append the payload of `stored` to `out`: the signer, the signature, the
/// record count, then each record as its key and its counted verdict bytes,
/// in the key order the receipt holds them in.
///
/// # Specification
/// trivial.
fn encode(
    stored: &StoredReceipt,
    out: &mut Payload<'_>,
)
{
    let records = stored.records();
    out.append(Bytes(&<[u8; 32]>::from(stored.receipt().signer())));
    out.append(Bytes(&<[u8; 64]>::from(stored.receipt().signature())));
    out.append(Bytes(
        &u64::try_from(records.len())
            .unwrap_or(u64::MAX)
            .to_le_bytes(),
    ));
    for record in records {
        let verdict = record.encoded();
        out.append(Bytes(&<[u8; 32]>::from(record.key())));
        out.append(Bytes(
            &u64::try_from(verdict.as_ref().len())
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        ));
        out.append(Bytes(verdict.as_ref()));
    }
}

/// The receipt [`encode`] wrote as `bytes`; absent when they are not one,
/// whole.
///
/// # Specification
/// trivial.
fn decode(bytes: Bytes<'_>) -> Maybe<StoredReceipt, stored::Absent>
{
    let unread = Maybe::Absent(stored::Absent::Unrecorded);
    let Some((signer, rest)) = bytes.0.split_first_chunk::<32>()
    else {
        return unread;
    };
    let Some((signature, rest)) = rest.split_first_chunk::<64>()
    else {
        return unread;
    };
    let Some((count, mut rest)) = rest.split_first_chunk::<8>()
    else {
        return unread;
    };
    let Ok(count) = usize::try_from(u64::from_le_bytes(*count))
    else {
        return unread;
    };
    let mut records = Vec::with_capacity(count.min(rest.len()));
    for _ in 0 .. count {
        let Some((key, after_key)) = rest.split_first_chunk::<32>()
        else {
            return unread;
        };
        let Some((length, after_length)) = after_key.split_first_chunk::<8>()
        else {
            return unread;
        };
        let Some((verdict, after_verdict)) = usize::try_from(u64::from_le_bytes(*length))
            .ok()
            .and_then(|length| after_length.split_at_checked(length))
        else {
            return unread;
        };
        let Maybe::Present(record) =
            VerdictRecord::decode(VerdictKey::from(*key), VerdictImage::from(verdict))
        else {
            return unread;
        };
        records.push(record);
        rest = after_verdict;
    }
    if !rest.is_empty() {
        return unread;
    }
    Maybe::Present(StoredReceipt::new(
        Receipt::new(
            KernelIdentity::from(*signer),
            ReceiptSignature::from(*signature),
        ),
        records,
    ))
}

#[cfg(test)]
mod tests;
