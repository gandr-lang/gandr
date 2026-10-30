//! The kernel's recorded verdicts on disk: each receipt a value in a
//! [`gandr_storage_store::Store`] the driver names, named by a root under
//! `receipt/` and its pointer's digest.
//!
//! The store is untrusted. It answers, for a key, the receipt whose records
//! hold it, and the kernel verifies that receipt's signature, and that its
//! signer is one the run's policy lists, before it believes a record
//! ([`gandr_kernel_core::verdict`]). A receipt the store's value plane refuses
//! is counted and passed over: a damaged record costs a replay, never a
//! verdict. The next keep of that receipt writes its chunks afresh, as the
//! store writes every object it refused.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — the store is untrusted by naming rule, and its
//!   integrity never admits.
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — lineage: §
//!   build-owner-store — one store on disk serves the build layer and the
//!   verdict cache.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::path::Path;
use std::sync::Mutex;

use anodized::spec;
use gandr_kernel_core::verdict::KernelIdentity;
use gandr_kernel_core::verdict::Receipt;
use gandr_kernel_core::verdict::ReceiptSignature;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::VerdictImage;
use gandr_kernel_core::verdict::VerdictKey;
use gandr_kernel_core::verdict::VerdictRecord;
use gandr_kernel_core::verdict::VerdictSource;
use gandr_storage_store::RootName;
use gandr_storage_store::Store;
use gandr_storage_store::Stored;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use quenchant_shape::shape::Maybe;

/// The tag a kept receipt opens with, and its codec's identifier.
const RECEIPT: u8 = 0x21_u8;

/// The prefix of every root naming a receipt.
const RECEIPT_ROOTS: &str = "receipt/";

/// Why the store could not do what it was asked.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum VerdictStoreError
{
    /// The store could not be opened.
    Unopened,
    /// A receipt could not be written into it.
    Unwritten,
}

/// How many receipts the store passed over because they did not read.
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

/// A receipt as the store holds it.
#[repr(transparent)]
#[derive(Clone, Debug)]
struct Kept(StoredReceipt);

impl CanonicalValue for Kept
{
    /// One constructor: the signer and the signature as bytes, the record
    /// count, then each record as its key and its verdict bytes, in the key
    /// order the receipt holds them in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        let records = self.0.records();
        sink.open(ConstructorTag::from(RECEIPT))?;
        sink.bytes(TokenBytes::from(
            &<[u8; 32]>::from(self.0.receipt().signer())[..],
        ))?;
        sink.bytes(TokenBytes::from(
            &<[u8; 64]>::from(self.0.receipt().signature())[..],
        ))?;
        sink.word(CanonicalWord::from(
            u64::try_from(records.len()).unwrap_or(u64::MAX),
        ))?;
        for record in records {
            sink.bytes(TokenBytes::from(&<[u8; 32]>::from(record.key())[..]))?;
            sink.bytes(TokenBytes::from(record.encoded().as_ref()))?;
        }
        sink.close()
    }

    /// The receipt [`Kept::emit_tokens`] wrote.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A [`ValueError`] when the stream is not one kept receipt.
    #[inline]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let position = reader.position();
        let found = reader.read_tag()?;
        if found != ConstructorTag::from(RECEIPT) {
            return Err(ValueError::UnexpectedConstructor { found, position });
        }
        let malformed = || ValueError::UnexpectedConstructor { found, position };
        let signer = <[u8; 32]>::try_from(<&[u8]>::from(reader.read_bytes()?))
            .map_err(|_short| malformed())?;
        let signature = <[u8; 64]>::try_from(<&[u8]>::from(reader.read_bytes()?))
            .map_err(|_short| malformed())?;
        let mut records = Vec::new();
        for _record in 0_u64 .. u64::from(reader.read_word()?) {
            let key = <[u8; 32]>::try_from(<&[u8]>::from(reader.read_bytes()?))
                .map_err(|_short| malformed())?;
            let Maybe::Present(record) = VerdictRecord::decode(
                VerdictKey::from(key),
                VerdictImage::from(<&[u8]>::from(reader.read_bytes()?)),
            )
            else {
                return Err(malformed());
            };
            records.push(record);
        }
        reader.read_close()?;
        Ok(Self(StoredReceipt::new(
            Receipt::new(
                KernelIdentity::from(signer),
                ReceiptSignature::from(signature),
            ),
            records,
        )))
    }
}

impl Stored for Kept
{
    /// # Specification
    /// trivial.
    #[inline]
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(u16::from(RECEIPT)), CodecVersion::from(1_u16))
    }
}

/// The receipts a store holds, indexed by every key their records hold.
///
/// # Specification
/// - ensures: [`VerdictSource::receipts`] answers, for a key, every receipt
///   read from the store when [`StoredVerdicts::open`] ran whose records hold
///   it.
/// - provides: the verdicts a run recalls from, and the place it records its
///   own.
/// - panics: none.
/// - executable: none — the index's agreement with the store is a fact about
///   the file system at open.
///
/// # Adequacy
/// - hypothesis: L3 — a receipt kept by one store is answered by another opened
///   over the same directory, two signers' receipts over the same records are
///   both answered, and a damaged receipt is passed over until a keep writes it
///   afresh.
/// - witness: `receipts::tests::a_kept_receipt_is_answered_after_reopening`
/// - witness: `receipts::tests::every_receipt_kept_for_a_key_is_answered`
/// - witness: `receipts::tests::a_damaged_receipt_is_passed_over_until_it_is_kept_again`
#[derive(Debug)]
pub struct StoredVerdicts
{
    /// The store holding the receipts.
    store: Mutex<Store>,
    /// Every receipt read at open, by each key its records hold.
    index: BTreeMap<VerdictKey, Vec<Arc<StoredReceipt>>>,
    /// How many receipts did not read.
    damaged: DamagedCount,
}

impl StoredVerdicts
{
    /// Open or create the store at `path` and read every receipt it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the store exists; the index holds every receipt a root under
    ///   `receipt/` names whose value derefs, and the damaged count every such
    ///   root whose value does not.
    /// - fails: [`VerdictStoreError::Unopened`] when the store cannot be
    ///   opened.
    /// - panics: propagates a panic from the supplied `AsRef` implementation.
    ///
    /// # Errors
    /// [`VerdictStoreError::Unopened`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`StoredVerdicts`].
    /// - witness: `receipts::tests::a_kept_receipt_is_answered_after_reopening`
    /// - witness: `receipts::tests::a_damaged_receipt_is_passed_over_until_it_is_kept_again`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Ok(_) | Err(VerdictStoreError::Unopened)))]
    pub fn open<Location>(path: Location) -> Result<Self, VerdictStoreError>
    where
        Location: AsRef<Path>,
    {
        let store = Store::open(path.as_ref()).map_err(|_fault| VerdictStoreError::Unopened)?;
        let mut index = BTreeMap::new();
        let mut damaged = 0_usize;
        for name in store
            .roots()
            .names()
            .filter(|name| name.as_ref().starts_with(RECEIPT_ROOTS))
        {
            let Maybe::Present(pointer) = store.roots().root(name)
            else {
                continue;
            };
            let Ok(Kept(receipt)) = store.deref::<Kept>(pointer)
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
            store: Mutex::new(store),
            index,
            damaged: DamagedCount(damaged),
        })
    }

    /// Commit `stored` to the store and name it, for a store opened later to
    /// read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the store holds `stored` under a root a store
    ///   opened later reads it from; this store's index is unchanged.
    /// - fails: [`VerdictStoreError::Unwritten`] when the receipt cannot be
    ///   committed or named.
    /// - panics: none.
    ///
    /// # Errors
    /// [`VerdictStoreError::Unwritten`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`StoredVerdicts`].
    /// - witness: `receipts::tests::a_kept_receipt_is_answered_after_reopening`
    /// - witness: `receipts::tests::a_damaged_receipt_is_passed_over_until_it_is_kept_again`
    #[inline]
    #[spec(ensures: |ret| matches!(ret, Ok(()) | Err(VerdictStoreError::Unwritten)))]
    pub fn keep(
        &self,
        stored: &StoredReceipt,
    ) -> Result<(), VerdictStoreError>
    {
        let mut store = self
            .store
            .lock()
            .map_err(|_poisoned| VerdictStoreError::Unwritten)?;
        store
            .commit(&Kept(stored.clone()))
            .and_then(|pointer| {
                store.set_root(
                    RootName::new(format!("{RECEIPT_ROOTS}{}", pointer.digest())),
                    pointer,
                )
            })
            .map_err(|_fault| VerdictStoreError::Unwritten)
    }

    /// How many receipts did not read at open.
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

impl VerdictSource for StoredVerdicts
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

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::sync::Arc;

    use gandr_kernel_core::Environment;
    use gandr_kernel_core::verdict::KernelSigner;
    use gandr_kernel_core::verdict::NoVerdicts;
    use gandr_kernel_core::verdict::StoredReceipt;
    use gandr_kernel_core::verdict::TrustPolicy;
    use gandr_kernel_core::verdict::VerdictSource as _;
    use gandr_kernel_term::LevelSignature;
    use gandr_storage_store::Store;
    use quenchant_shape::shape::Maybe;

    use super::RECEIPT_ROOTS;
    use super::StoredVerdicts;

    /// The receipt `signer` gives over a cold admission of two unit
    /// definitions.
    ///
    /// # Specification
    /// trivial.
    fn receipt(signer: &KernelSigner) -> StoredReceipt
    {
        let mut environment = Environment::recalling(
            TrustPolicy::Trusted(BTreeSet::from([signer.identity()])),
            Arc::new(NoVerdicts),
        );
        for _ in 0_u8 .. 2 {
            let staged = {
                let mut staging = environment.stage();
                let declared = staging.arena().value_type_unit();
                let body = staging.arena().value_unit();
                staging.def(LevelSignature::monomorphic(), declared, body)
            };
            let _admitted = environment
                .add_decl(staged)
                .expect("a unit definition admits");
        }
        let Maybe::Present(receipt) = environment.receipt(signer)
        else {
            panic!("a cold admission under keys gives a receipt");
        };
        receipt
    }

    #[test]
    fn a_kept_receipt_is_answered_after_reopening()
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-receipts-{}-{}",
            std::process::id(),
            "a_kept_receipt_is_answered_after_reopening"
        ));
        drop(std::fs::remove_dir_all(&directory));
        let receipt = receipt(&KernelSigner::from([3_u8; 32]));
        let store = StoredVerdicts::open(&directory).expect("the store opens");
        store.keep(&receipt).expect("the receipt is written");
        let first = receipt
            .records()
            .first()
            .expect("the receipt holds records")
            .key();
        assert!(
            store.receipts(first).is_empty(),
            "a store answers only what it read at open"
        );
        let reopened = StoredVerdicts::open(&directory).expect("the store reopens");
        let held = [Arc::new(receipt.clone())];
        for record in receipt.records() {
            assert_eq!(
                reopened.receipts(record.key()),
                held,
                "every key the receipt holds answers it"
            );
        }
        assert_eq!(usize::from(reopened.damaged()), 0);
        drop(std::fs::remove_dir_all(&directory));
    }

    #[test]
    fn every_receipt_kept_for_a_key_is_answered()
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-receipts-{}-{}",
            std::process::id(),
            "every_receipt_kept_for_a_key_is_answered"
        ));
        drop(std::fs::remove_dir_all(&directory));
        let ours = receipt(&KernelSigner::from([3_u8; 32]));
        let theirs = receipt(&KernelSigner::from([4_u8; 32]));
        let store = StoredVerdicts::open(&directory).expect("the store opens");
        store.keep(&ours).expect("our receipt is written");
        store.keep(&theirs).expect("theirs is written");
        let reopened = StoredVerdicts::open(&directory).expect("the store reopens");
        let (ours_held, theirs_held) = (Arc::new(ours.clone()), Arc::new(theirs));
        for record in ours.records() {
            let answered = reopened.receipts(record.key());
            assert_eq!(answered.len(), 2, "both signers' receipts hold the key");
            assert!(
                answered.contains(&ours_held) && answered.contains(&theirs_held),
                "neither receipt hides the other"
            );
        }
        drop(std::fs::remove_dir_all(&directory));
    }

    /// A receipt whose chunk changed on disk is passed over and counted, and
    /// the next keep of it writes the chunk afresh, so a later store answers
    /// it.
    #[test]
    fn a_damaged_receipt_is_passed_over_until_it_is_kept_again()
    {
        let directory = std::env::temp_dir().join(format!(
            "gandr-receipts-{}-{}",
            std::process::id(),
            "a_damaged_receipt_is_passed_over_until_it_is_kept_again"
        ));
        drop(std::fs::remove_dir_all(&directory));
        let receipt = receipt(&KernelSigner::from([3_u8; 32]));
        StoredVerdicts::open(&directory)
            .expect("the store opens")
            .keep(&receipt)
            .expect("the receipt is written");
        let opened = Store::open(&directory).expect("the store reopens");
        let name = opened.roots().names().next().expect("the receipt is named");
        let written = directory.join("chunks").join(
            name.as_ref()
                .strip_prefix(RECEIPT_ROOTS)
                .expect("a receipt's root"),
        );
        let bytes = std::fs::read(&written).expect("the receipt's chunk reads");
        let truncated = bytes.get(.. bytes.len() - 1).expect("in range").to_vec();
        let mut changed = bytes;
        if let Some(last) = changed.last_mut() {
            *last ^= 0x01_u8;
        }
        let held = [Arc::new(receipt.clone())];
        for (damaged, what) in [
            (truncated, "a truncated chunk"),
            (changed, "a changed chunk byte"),
        ] {
            std::fs::write(&written, &damaged).expect("the damage is written");
            let reopened = StoredVerdicts::open(&directory).expect("the store reopens");
            assert_eq!(usize::from(reopened.damaged()), 1, "{what}");
            for record in receipt.records() {
                assert!(reopened.receipts(record.key()).is_empty(), "{what}");
            }
            reopened
                .keep(&receipt)
                .expect("the receipt is written again");
            let repaired = StoredVerdicts::open(&directory).expect("the store reopens");
            assert_eq!(usize::from(repaired.damaged()), 0, "{what}");
            for record in receipt.records() {
                assert_eq!(repaired.receipts(record.key()), held, "{what}");
            }
        }
        drop(std::fs::remove_dir_all(&directory));
    }
}
