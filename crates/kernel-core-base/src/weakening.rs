//! **Support by weakening**: a declaration's check reads only the entries that
//! its content reaches, and the kernel refuses a read outside them.
//!
//! A verdict depends only on the entries that the declaration's content
//! reaches, through its references and through theirs. The kernel checks this
//! and does not assume it. A check starts with the declaration's direct
//! references as its support. When the check reads an entry in the support,
//! the entry's own direct references join the support. When a sort joins, each
//! type of words over the sort joins too, since a case over the sort keeps a
//! loop arm for each.
//!
//! A read outside the support answers as an absent entry, and the support
//! keeps the first position read so. The environment then refuses the
//! declaration with
//! [`KernelError::OutsideSupport`](crate::KernelError::OutsideSupport). So a
//! missing edge in the support is a refusal, never another verdict.
//!
//! The support keeps one stamp for each entry: the number of the check that
//! last joined the entry, doubled, with the low bit set once the entry's own
//! references joined too. Each check takes the next number, so it clears no
//! set and allocates nothing. The stamps are atomic, so an environment stays
//! shareable between threads while one check reads it.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: unit 4 of the
//!   kernel re-assessment (§ kernel-reassessment-units), and a result as a
//!   section over its support (§ kernel-reassessment-design item 2).
//! - `vault:01a178ab-081c-74a0-bd58-f8db4f9573c8` — lineage: the support
//!   discipline. The kernel checks the support as a bound on what a check
//!   reads, and never trusts it.

use alloc::vec::Vec;
use core::sync::atomic::AtomicU32;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use anodized::spec;
use gandr_kernel_term::ArenaLength;
use gandr_kernel_term::ConstantIndex;

/// No position read outside the support.
const INSIDE: usize = usize::MAX;

/// The highest check number: twice it, with the low bit set, still fits a
/// stamp.
const LAST_CHECK: u32 = u32::MAX >> 1;

/// What a read of one entry found in the support.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Read
{
    /// No check runs, so every entry reads.
    Open,
    /// The check reads the entry for the first time: its own references join
    /// the support now.
    First,
    /// The check read the entry before.
    Again,
    /// The entry is outside the support, and the read is refused.
    Outside,
}

/// The support of the check that runs over one environment's entries.
///
/// # Specification
/// - provides: the stamps that say which entries the running check may read,
///   and which of them it read; the first position it read outside them; and
///   how many entries it read.
/// - panics: none.
/// - executable: none — data declaration; [`Self::open`], [`Self::read`] and
///   [`Self::close`] state what a check sees.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration whose check reads an entry its content does
///   not name is refused at that position, and a check after many unrelated
///   entries reads as many entries as after few.
/// - witness: `environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
/// - witness: `environment::tests::an_admission_reads_as_many_entries_after_many_unrelated_ones_2797`
#[derive(Debug, Default)]
pub struct Support
{
    /// For each entry, the check that last joined it, doubled; the low bit is
    /// set once its own references joined too.
    stamps: Vec<AtomicU32>,
    /// The number of the last check opened.
    last: u32,
    /// The stamp of an entry that the running check joined, and zero while no
    /// check runs.
    joined: u32,
    /// The first position the running check read outside its support, or
    /// [`INSIDE`].
    outside: AtomicUsize,
    /// How many entries the running check read.
    reads: AtomicUsize,
}

impl Support
{
    /// Open a check over `length` entries, with an empty support.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a stamp for each of the `length` entries, none of them
    ///   joined, no read outside and no read counted.
    /// - provides: the start of a check: a fresh number, so no stamp is
    ///   cleared, except once each `2^31` checks.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Support`].
    /// - witness: `environment::tests::an_admission_reads_as_many_entries_after_many_unrelated_ones_2797`
    #[spec(ensures: self.stamps.len() >= usize::from(length) && self.joined != 0 && self.joined & 1 == 0)]
    pub fn open(
        &mut self,
        length: ArenaLength,
    )
    {
        let length = usize::from(length);
        if let Some(missing) = length.checked_sub(self.stamps.len()) {
            self.stamps.reserve(missing);
            self.stamps.resize_with(length, AtomicU32::default);
        }
        self.last = match self.last.checked_add(1) {
            Some(next) if next <= LAST_CHECK => next,
            Some(_) | None => {
                for stamp in &mut self.stamps {
                    *stamp.get_mut() = 0;
                }
                1
            },
        };
        self.joined = self.last << 1_u32;
        *self.outside.get_mut() = INSIDE;
        *self.reads.get_mut() = 0;
    }

    /// Close the running check: the first position it read outside its
    /// support, if it read one.
    ///
    /// # Specification
    /// trivial.
    pub fn close(&mut self) -> Option<ConstantIndex>
    {
        self.joined = 0;
        let outside = *self.outside.get_mut();
        (outside != INSIDE).then(|| ConstantIndex::from(outside))
    }

    /// How many entries the running check, or the last one, read.
    ///
    /// # Specification
    /// trivial.
    #[cfg(any(test, feature = "fixture"))]
    pub fn reads(&self) -> ArenaLength
    {
        ArenaLength::from(self.reads.load(Ordering::Relaxed))
    }

    /// Join the entry at `position` to the running check's support.
    ///
    /// # Specification
    /// trivial.
    pub fn join(
        &self,
        position: ConstantIndex,
    )
    {
        if self.joined == 0 {
            return;
        }
        if let Some(stamp) = self.stamps.get(usize::from(position)) {
            // A stamp from an earlier check is below this check's stamps, so
            // the larger keeps an entry read before as read.
            let _earlier = stamp.fetch_max(self.joined, Ordering::Relaxed);
        }
    }

    /// Read the entry at `position` through the running check's support.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Read::Open`] while no check runs. Otherwise [`Read::First`]
    ///   at the first read of a joined entry, which counts it; [`Read::Again`]
    ///   at a later read; and [`Read::Outside`] at an entry outside the
    ///   support, which keeps the first such position.
    /// - provides: the one gate every read of an entry passes during a check.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clauses state a stamp before and after an
    ///   atomic exchange, which a predicate may not capture.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Support`].
    /// - witness: `environment::tests::a_read_outside_the_support_refuses_the_declaration_2797`
    pub fn read(
        &self,
        position: ConstantIndex,
    ) -> Read
    {
        if self.joined == 0 {
            return Read::Open;
        }
        let expanded = self.joined | 1;
        // A load decides each read after the first, so only the first read of
        // an entry pays for an exchange.
        let read = |stamp: &AtomicU32| match stamp.load(Ordering::Relaxed) {
            found if found == expanded => Read::Again,
            found if found == self.joined => stamp
                .compare_exchange(found, expanded, Ordering::Relaxed, Ordering::Relaxed)
                .map_or_else(
                    |raced| {
                        if raced == expanded {
                            Read::Again
                        }
                        else {
                            Read::Outside
                        }
                    },
                    |_| Read::First,
                ),
            _ => Read::Outside,
        };
        let found = self
            .stamps
            .get(usize::from(position))
            .map_or(Read::Outside, read);
        match found {
            Read::First => {
                let _before = self.reads.fetch_add(1, Ordering::Relaxed);
            },
            Read::Outside => {
                let _first = self.outside.compare_exchange(
                    INSIDE,
                    usize::from(position),
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                );
            },
            Read::Open | Read::Again => {},
        }
        found
    }

    /// Read the entry at `position` through the running check's support, and
    /// change nothing: for a specification clause, which may not move what
    /// the check reads. An entry in the support answers [`Read::Again`],
    /// whether the check read it or not.
    ///
    /// # Specification
    /// trivial.
    pub fn peek(
        &self,
        position: ConstantIndex,
    ) -> Read
    {
        if self.joined == 0 {
            return Read::Open;
        }
        let inside = |found: u32| (found | 1) == (self.joined | 1);
        match self.stamps.get(usize::from(position)) {
            Some(stamp) if inside(stamp.load(Ordering::Relaxed)) => Read::Again,
            Some(_) | None => Read::Outside,
        }
    }
}
