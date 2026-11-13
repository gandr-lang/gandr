//! **The reach of an edit**: the entries whose support holds an edited entry,
//! read backward through a reverse index of the direct references.
//!
//! Each entry keeps the positions that its content names, its direct
//! references ([`crate::weakening`]). The reverse index keeps, for each
//! position, the entries that name it. It grows by one row for each reference
//! at an admission, and the rollback of a refused block drops the rows of its
//! members.
//!
//! A check's support holds an entry in three ways, the three reads of a check.
//! The check names the entry, directly or through the entries that it reads.
//! The check is a member of the entry's mutual block, whose members each name
//! the whole block. Or the support holds a sort, and the entry is a type of
//! words over that sort, admitted before the check. The walk follows the first
//! two through the reverse index. For the third, the sort joins the walk with a
//! bound: an entry holds the type of words through the sort only when the
//! entry comes after the type of words.
//!
//! An entry in the reach takes a new verdict input, so each entry whose
//! support holds it is in the reach too. The walk reads the rows of the reach
//! and of the sorts that lead to it, and no other row. So its cost is linear in
//! the reach and its rows, and the entries outside them add nothing.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: a result as a
//!   section over its support (§ kernel-reassessment-design item 2), and the
//!   readmission of an edit (item 4).
//! - `vault:01a178ab-081c-74a0-bd58-f8db4f9573c8` — lineage: the support
//!   discipline. An edit dirties the verdicts whose support holds the edited
//!   entry, and no other.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BinaryHeap;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;
use core::cmp::Reverse;

use anodized::spec;
use gandr_kernel_term::ArenaLength;
use gandr_kernel_term::ConstantIndex;

/// The end of a chain of rows.
const NONE: usize = usize::MAX;

/// One row of the reverse index: an entry that names a position.
#[derive(Clone, Copy, Debug)]
struct Row
{
    /// The entry that names the position.
    dependent: ConstantIndex,
    /// The row admitted before this one for the same position, or [`NONE`].
    next: usize,
}

/// The reverse index of the direct references: for each position, the entries
/// that name it.
///
/// The rows of all positions share one vector, in admission order. Each
/// position keeps its last row, and each row the row before it for the same
/// position. So an admission appends its rows and allocates nothing else, a
/// rollback pops them in the reverse order, and a clone copies two vectors.
///
/// # Specification
/// - provides: the dependents of each position, newest first.
/// - panics: none.
/// - executable: none — data declaration; [`Self::admit`], [`Self::forget`] and
///   [`Self::of`] state what it holds.
///
/// # Adequacy
/// - hypothesis: L3 — the reach of each edit of a generated environment equals
///   the entries whose support holds an edited entry, after refused blocks roll
///   back.
/// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
#[derive(Clone, Debug, Default)]
pub struct Dependents
{
    /// The last row of each position, or [`NONE`].
    last: Vec<usize>,
    /// Every row, in admission order.
    rows: Vec<Row>,
}

impl Dependents
{
    /// Admit the entry at `position`, which names `references`.
    ///
    /// # Specification
    /// - requires: `position` is past each position admitted before, and
    ///   `references` are the entry's direct references.
    /// - ensures: one more row for each reference, and a last row for each
    ///   position up to `position` and each reference.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Dependents`].
    /// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
    #[spec(captures: rows = self.rows.len(), ensures: self.rows.len() == rows.saturating_add(references.len()))]
    pub fn admit(
        &mut self,
        position: ConstantIndex,
        references: &[ConstantIndex],
    )
    {
        // A mutual block's members name the later members too, so a reference
        // can be past the entry.
        let highest = references.iter().copied().fold(position, Ord::max);
        let length = usize::from(highest).saturating_add(1);
        if self.last.len() < length {
            self.last.resize(length, NONE);
        }
        self.rows.reserve(references.len());
        for &reference in references {
            if let Some(last) = self.last.get_mut(usize::from(reference)) {
                let next = core::mem::replace(last, self.rows.len());
                self.rows.push(Row {
                    dependent: position,
                    next,
                });
            }
        }
    }

    /// Drop the rows of the entry admitted last, which names `references`.
    ///
    /// # Specification
    /// - requires: `references` are the direct references of the entry whose
    ///   rows are the last ones.
    /// - ensures: the rows as they were before that entry's admission.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Dependents`].
    /// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
    #[spec(captures: rows = self.rows.len(), ensures: self.rows.len() == rows.saturating_sub(references.len()))]
    pub fn forget(
        &mut self,
        references: &[ConstantIndex],
    )
    {
        for &reference in references.iter().rev() {
            let Some(row) = self.rows.pop()
            else {
                return;
            };
            if let Some(last) = self.last.get_mut(usize::from(reference)) {
                *last = row.next;
            }
        }
    }

    /// Keep the last rows of the positions before `first` alone.
    ///
    /// # Specification
    /// trivial.
    pub fn truncate(
        &mut self,
        first: ConstantIndex,
    )
    {
        self.last.truncate(usize::from(first));
    }

    /// The entries that name `position`, newest first.
    ///
    /// # Specification
    /// trivial.
    fn of(
        &self,
        position: ConstantIndex,
    ) -> impl Iterator<Item = ConstantIndex>
    {
        let mut at = self
            .last
            .get(usize::from(position))
            .copied()
            .unwrap_or(NONE);
        core::iter::from_fn(move || {
            let row = self.rows.get(at)?;
            at = row.next;
            Some(row.dependent)
        })
    }
}

/// How far after the walk's start an entry's support must be to hold an
/// edited entry through a position.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Bound
{
    /// Each entry whose support holds the position holds an edited entry.
    Any,
    /// Only an entry after this type of words holds an edited entry through
    /// the position.
    After(ConstantIndex),
}

impl Bound
{
    /// The bound of the entry at `position` when its support holds a
    /// position at this bound: [`Bound::Any`] once the entry comes after the
    /// type of words.
    ///
    /// # Specification
    /// trivial.
    fn at(
        self,
        position: ConstantIndex,
    ) -> Self
    {
        match self {
            Self::After(words) if position <= words => self,
            Self::Any | Self::After(_) => Self::Any,
        }
    }
}

/// The positions that the walk reached, each at its lowest bound.
#[derive(Debug, Default)]
struct Walk
{
    /// The lowest bound of each position reached.
    bounds: BTreeMap<ConstantIndex, Bound>,
    /// The positions reached at [`Bound::Any`], to read.
    open: Vec<ConstantIndex>,
    /// The positions reached at a bound after a type of words, to read, the
    /// lowest bound first.
    bounded: BinaryHeap<Reverse<(ConstantIndex, ConstantIndex)>>,
}

impl Walk
{
    /// Reach `position` at `bound`, unless the walk reached it at a bound as
    /// low.
    ///
    /// # Specification
    /// trivial.
    fn lower(
        &mut self,
        position: ConstantIndex,
        bound: Bound,
    )
    {
        match self.bounds.entry(position) {
            Entry::Vacant(slot) => {
                let _reached = slot.insert(bound);
            },
            Entry::Occupied(mut slot) => {
                if *slot.get() <= bound {
                    return;
                }
                let _higher = slot.insert(bound);
            },
        }
        match bound {
            Bound::Any => self.open.push(position),
            Bound::After(words) => self.bounded.push(Reverse((words, position))),
        }
    }

    /// The next position to read, at its lowest bound: each one at
    /// [`Bound::Any`] first.
    ///
    /// # Specification
    /// trivial.
    fn next(&mut self) -> Option<(ConstantIndex, Bound)>
    {
        if let Some(position) = self.open.pop() {
            return Some((position, Bound::Any));
        }
        while let Some(Reverse((words, position))) = self.bounded.pop() {
            // A row pushed before the walk lowered the position again is
            // stale.
            if self.bounds.get(&position) == Some(&Bound::After(words)) {
                return Some((position, Bound::After(words)));
            }
        }
        None
    }
}

/// The reach of `edited` over the entries whose reverse index is
/// `dependents`: each edited position, with each entry whose support holds an
/// entry of the reach, ascending.
///
/// `words` gives the sort of a type of words, and nothing for another entry.
/// `length` is the count of the entries, and an edited position past them
/// adds nothing.
///
/// # Specification
/// - requires: `dependents` and `words` read the same entries.
/// - ensures: ascending, each once, and each below `length`.
/// - provides: the entries whose verdict an edit can change: the rest keep
///   their whole verdict input.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the reach of each edit of a generated environment equals
///   the entries whose support holds an edited entry, and a type of words
///   reaches an entry after it through its sort and no entry before it.
/// - witness: `environment::tests::the_reach_holds_each_entry_whose_support_holds_an_edited_one`
/// - witness: `presented::tests::a_type_of_words_reaches_the_entries_after_it_through_its_sort_6621`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(*pair, [earlier, later] if earlier < later)) && ret.iter().all(|&position| position < ConstantIndex::from(length)))]
pub fn reach<Words, Edited>(
    dependents: &Dependents,
    words: Words,
    length: ArenaLength,
    edited: Edited,
) -> Box<[ConstantIndex]>
where
    Words: Fn(ConstantIndex) -> Option<ConstantIndex>,
    Edited: IntoIterator<Item = ConstantIndex>,
{
    let mut walk = Walk::default();
    let end = ConstantIndex::from(length);
    for position in edited {
        if position < end {
            walk.lower(position, Bound::Any);
        }
    }
    while let Some((position, bound)) = walk.next() {
        for dependent in dependents.of(position) {
            walk.lower(dependent, bound.at(dependent));
        }
        if let Some(sort) = words(position) {
            let past = match bound {
                Bound::Any => position,
                Bound::After(other) => position.max(other),
            };
            walk.lower(sort, Bound::After(past));
        }
    }
    walk.bounds
        .into_iter()
        .filter_map(|(position, bound)| (bound == Bound::Any).then_some(position))
        .collect()
}
