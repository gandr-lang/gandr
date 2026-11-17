//! The kernel's recorded verdicts in memory, for the life of one process.
//!
//! A process that keeps no store on disk, as the language server, still
//! readmits the same declarations many times. [`HeldVerdicts`] keeps each
//! receipt that the process's own kernel signs, and answers it by every key
//! its records hold. A readmission reads one [`Held`] snapshot, taken at its
//! start, so no lookup takes a lock and no readmission waits on another's
//! settlement.
//!
//! A snapshot is two indices: a large one that changes seldom, and a small
//! one that each settlement adds its receipt to. A settlement copies the
//! small one alone. Once the small one holds more than [`BOUNDS`]' recent
//! records, it merges into a copy of the large one, and the oldest receipts go
//! past its held records. So the copying a record costs is bounded on average
//! by the large index's size over the recent records.
//!
//! The source is untrusted, as the store on disk is: the kernel verifies each
//! receipt's signature and signer before it believes a record
//! ([`gandr_kernel_core::verdict`]).
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: §
//!   kernel-verdict-reuse — a recalled verdict is the kernel's own, under its
//!   whole input, and the source never admits.

use alloc::collections::BTreeMap;
use alloc::collections::VecDeque;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::sync::Mutex;
use std::sync::PoisonError;

use anodized::spec;
use gandr_kernel_core::verdict::StoredReceipt;
use gandr_kernel_core::verdict::VerdictKey;
use gandr_kernel_core::verdict::VerdictSource;

/// The record counts a held source keeps to.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Bounds
{
    /// The most records the large index holds after a merge. Past it, the
    /// oldest receipt goes.
    held: usize,
    /// The records the small index holds before it merges into the large one.
    recent: usize,
}

/// The bounds of a process's source. A record is a key of 32 bytes and a
/// verdict, so the held records take a few MiB.
const BOUNDS: Bounds = Bounds {
    held: 1 << 16,
    recent: 1 << 10,
};

/// Receipts indexed by every key their records hold, the oldest first.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default)]
struct Index
{
    /// Every receipt held, by each key its records hold.
    by_key: BTreeMap<VerdictKey, Vec<Arc<StoredReceipt>>>,
    /// The receipts held, the oldest first.
    order: VecDeque<Arc<StoredReceipt>>,
    /// How many records the held receipts hold.
    records: usize,
}

impl Index
{
    /// Hold `receipt` after the others.
    ///
    /// # Specification
    /// trivial.
    fn hold(
        &mut self,
        receipt: Arc<StoredReceipt>,
    )
    {
        for record in receipt.records() {
            self.by_key
                .entry(record.key())
                .or_default()
                .push(Arc::clone(&receipt));
        }
        self.records = self.records.saturating_add(receipt.records().len());
        self.order.push_back(receipt);
    }

    /// Let the oldest receipts go until the records held are within `bounds`'
    /// held records, or one receipt alone is held.
    ///
    /// # Specification
    /// trivial.
    fn bound(
        &mut self,
        bounds: Bounds,
    )
    {
        while self.records > bounds.held && self.order.len() > 1 {
            let Some(oldest) = self.order.pop_front()
            else {
                break;
            };
            for record in oldest.records() {
                if let Some(held) = self.by_key.get_mut(&record.key()) {
                    held.retain(|kept| !Arc::ptr_eq(kept, &oldest));
                    if held.is_empty() {
                        let _gone = self.by_key.remove(&record.key());
                    }
                }
            }
            self.records = self.records.saturating_sub(oldest.records().len());
        }
    }

    /// The receipts held whose records hold `key`.
    ///
    /// # Specification
    /// trivial.
    fn receipts(
        &self,
        key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        self.by_key.get(&key).map_or(&[], Vec::as_slice)
    }
}

/// One snapshot of the receipts a process holds.
///
/// # Specification
/// - ensures: [`VerdictSource::receipts`] answers, for a key, the receipts the
///   snapshot's small index holds whose records hold it, or else those its
///   large index holds.
/// - executable: none — the indices' agreement with the receipts is an
///   invariant of [`HeldVerdicts::keep`], which the witnesses check.
///
/// # Adequacy
/// - hypothesis: L3 — as [`HeldVerdicts`].
/// - witness: `held::tests::a_kept_receipt_is_answered_by_the_next_snapshot_alone`
/// - witness: `held::tests::past_the_bound_the_oldest_receipt_goes`
#[derive(Clone, Debug, Default)]
pub struct Held
{
    /// The receipts merged so far, which a settlement shares.
    large: Arc<Index>,
    /// The receipts kept since the last merge, which a settlement copies.
    small: Arc<Index>,
}

impl Held
{
    /// Add `receipt` to the small index, and merge the small index into a
    /// copy of the large one once it holds more than `bounds`' recent
    /// records, letting the oldest receipts go past its held records.
    ///
    /// # Specification
    /// trivial.
    fn add(
        &mut self,
        receipt: StoredReceipt,
        bounds: Bounds,
    )
    {
        // A snapshot a readmission still reads keeps what it holds: the
        // settlement copies the two pointers, then the small index alone.
        let small = Arc::make_mut(&mut self.small);
        small.hold(Arc::new(receipt));
        if small.records > bounds.recent {
            let merged = core::mem::take(small);
            let mut large = Index::clone(&self.large);
            for receipt in merged.order {
                large.hold(receipt);
            }
            large.bound(bounds);
            self.large = Arc::new(large);
        }
    }
}

impl VerdictSource for Held
{
    /// The receipts the small index holds whose records hold `key`, or else
    /// those the large index holds: any one of them attests the same record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn receipts(
        &self,
        key: VerdictKey,
    ) -> &[Arc<StoredReceipt>]
    {
        let recent = self.small.receipts(key);
        if recent.is_empty() {
            self.large.receipts(key)
        }
        else {
            recent
        }
    }
}

/// The receipts a process's own kernel signed, held in memory for the
/// process's life.
///
/// # Specification
/// - ensures: a snapshot taken after [`HeldVerdicts::keep`] answers the kept
///   receipt by each key its records hold; a snapshot taken before answers what
///   it answered; after a merge, the receipts held hold at most the bound's
///   records, unless one receipt alone holds more.
/// - provides: the verdicts a readmission recalls from, without a store on
///   disk.
/// - panics: none.
/// - executable: none — the held snapshot is shared state.
///
/// # Adequacy
/// - hypothesis: L3 — a kept receipt is answered by the next snapshot and not
///   by the one before, and past the bound the oldest receipt goes.
/// - witness: `held::tests::a_kept_receipt_is_answered_by_the_next_snapshot_alone`
/// - witness: `held::tests::past_the_bound_the_oldest_receipt_goes`
#[derive(Debug)]
pub struct HeldVerdicts
{
    /// The latest snapshot.
    held: Mutex<Arc<Held>>,
    /// The record counts the source keeps to.
    bounds: Bounds,
}

impl Default for HeldVerdicts
{
    /// An empty source under [`BOUNDS`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::bounded(BOUNDS)
    }
}

impl HeldVerdicts
{
    /// An empty source that keeps to `bounds`.
    ///
    /// # Specification
    /// trivial.
    fn bounded(bounds: Bounds) -> Self
    {
        Self {
            held: Mutex::new(Arc::new(Held::default())),
            bounds,
        }
    }

    /// The receipts held now, for one readmission to read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn snapshot(&self) -> Arc<Held>
    {
        Arc::clone(&self.held.lock().unwrap_or_else(PoisonError::into_inner))
    }

    /// Hold `receipt` in the snapshots taken after, merging the small index
    /// into the large one past its size, and letting the oldest receipts go
    /// past the bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`HeldVerdicts`]; a snapshot taken before is unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`HeldVerdicts`].
    /// - witness: `held::tests::a_kept_receipt_is_answered_by_the_next_snapshot_alone`
    /// - witness: `held::tests::past_the_bound_the_oldest_receipt_goes`
    #[inline]
    #[spec(ensures: self.snapshot().small.records <= self.bounds.recent)]
    pub fn keep(
        &self,
        receipt: StoredReceipt,
    )
    {
        let mut latest = self.held.lock().unwrap_or_else(PoisonError::into_inner);
        Arc::make_mut(&mut latest).add(receipt, self.bounds);
    }
}

#[cfg(test)]
mod tests;
