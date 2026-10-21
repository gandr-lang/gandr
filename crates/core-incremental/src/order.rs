//! Item identity across revisions, carried by an order-maintenance structure.
//!
//! # Identity rides on the order, not on position
//!
//! Each item of the latest revision holds one handle into an order-maintenance
//! structure whose order is the program's source order. A revision splices the
//! structure rather than rebuilding it: the longest run of surviving items
//! whose base order the edit preserved keeps its handles; every other item
//! takes a fresh handle after its predecessor, and a deleted item's handle, or
//! a moved item's old one, resolves to nothing. A consumer holding a handle —
//! an editor's cursor on a declaration, a stream reader's bookmark — keeps
//! naming the same item across edits elsewhere, and compares two handles'
//! order in constant time. Reuse is decided by content, never by handle: the
//! handle is identity for the consumer, not evidence for the checker.
//!
//! # Handles, not indices
//!
//! Each item holds a handle into an order-maintenance structure whose order is
//! source order. A revision splices it: a longest run of surviving items whose
//! base order the edit preserved keeps its handles (patience sorting, so a move
//! costs the moved item's handle alone), every other item takes a fresh handle
//! after its predecessor, and the rest are removed. Handles are identity for
//! consumers — an editor's cursor, a stream reader's bookmark — and never
//! evidence for the checker: reuse is decided by content.
//!
//! | Decision | Alternatives | Reversal |
//! | -------- | ------------ | -------- |
//! | Identity by content, recalled through the shared memo | positional identity; identity by name | the front end supplies stable item ids that survive every edit |
//! | Keep handles on a longest preserved run | greedy keep-in-order, which loses every handle after a move to the front; a longest common subsequence over contents, quadratic | a consumer needs handles to follow moved items, which needs move detection in the front end |

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;
use gandr_theory_orders::OrderError;
use gandr_theory_orders::OrderMaintenance;
use gandr_theory_orders::Pos;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemCount;
use crate::region::Reference;

quenchant_shape::reason_enum! {
    /// Why a handle answers nothing.
    pub mod handle {
        /// The reason no answer is given.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The handle's item was deleted or reordered by a later revision,
            /// or the handle belongs to another session's order.
            Stale,
        }
    }
}

/// An item's identity across revisions of one session.
///
/// # Specification
/// - requires: interpreted against a session's current item order.
/// - ensures: keeping an item preserves its handle; removal or movement makes
///   its old handle stale, and another session cannot use it.
/// - panics: none.
/// - executable: none — liveness, ownership and ordering require the owning
///   order and its revision history, not just the carried position.
///
/// # Adequacy
/// - hypothesis: L3 — insertion, deletion, a move and a foreign session
///   distinguish lost identity and stale or foreign aliasing by exact handle
///   equality, references and comparison results.
/// - witness: `order::tests::a_handle_survives_an_insertion_before_its_item`
/// - witness: `order::tests::a_deleted_items_handle_goes_stale`
/// - witness: `order::tests::a_moved_item_costs_only_its_own_handle`
/// - witness: `order::tests::comparisons_refuse_stale_and_foreign_operands`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ItemHandle(Pos);

/// What one splice did to the order.
///
/// # Specification
/// - requires: interpreted with the base and edited sequences of one splice.
/// - ensures: kept plus removed counts the base; kept plus inserted counts the
///   edited sequence.
/// - panics: none.
/// - executable: none — the two input sequences are absent from the census; the
///   splice predicate checks the count equations at its return boundary.
///
/// # Adequacy
/// - hypothesis: L3 — empty, fresh, deleted and unchanged orders plus a swap
///   distinguish missing or crossed counters by exact census values and handle
///   survival.
/// - witness: `order::tests::empty_and_unchanged_splices_have_exact_censuses`
/// - witness: `order::tests::handles_compare_in_the_edited_order`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SpliceCensus
{
    /// Items that kept their handle.
    pub kept: ItemCount,
    /// Items that took a fresh handle.
    pub inserted: ItemCount,
    /// Handles of items that left the order.
    pub removed: ItemCount,
}

/// The order of the latest revision's items, one handle per item.
///
/// # Specification
/// - requires: handle operations use this order's current revision.
/// - ensures: every current item has a distinct handle; edits preserve a
///   longest subsequence's handles and retire every other base handle.
/// - panics: none.
/// - executable: none — preservation compares revisions; the data value holds
///   only the current order, and splice predicates check its transition.
///
/// # Adequacy
/// - hypothesis: L3 — duplicate payloads at seeding and insertion, deletion,
///   swap and move transitions distinguish value-based identity, incorrect
///   preservation and stale aliases through handles and lookups. The witnesses
///   exercise small orders, not allocator or identifier ceilings.
/// - witness: `order::tests::seeding_preserves_duplicate_payloads_with_distinct_handles`
/// - witness: `order::tests::a_handle_survives_an_insertion_before_its_item`
/// - witness: `order::tests::a_deleted_items_handle_goes_stale`
/// - witness: `order::tests::a_moved_item_costs_only_its_own_handle`
#[repr(transparent)]
pub struct ItemOrder
{
    /// The structure; each element carries its item's reference.
    order: OrderMaintenance<Reference>,
}

impl ItemOrder
{
    /// An order holding `references` in order, with one fresh handle each.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success one handle per reference, in order.
    /// - fails: when the structure cannot be built or cannot admit an element.
    /// - panics: none.
    ///
    /// # Errors
    /// The order-maintenance structure's own refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and three-entry sequences with duplicate
    ///   references distinguish dropped occurrences, shared handles and wrong
    ///   ordering through exact payloads and comparisons. Construction and
    ///   capacity refusals belong to the underlying order; these finite
    ///   witnesses do not exhaust its identifiers or storage.
    /// - witness: `order::tests::seeding_preserves_duplicate_payloads_with_distinct_handles`
    /// - witness: `order::tests::empty_and_unchanged_splices_have_exact_censuses`
    #[spec(ensures: |ret| match ret {
        Ok((ref order, ref handles)) => handles.len() == references.len()
            && handles.iter().zip(references).all(|(&handle, reference)|
                order.order.get(handle.0) == Some(reference))
            && handles.windows(2).all(|pair| pair.first().zip(pair.last())
                .is_some_and(|(&left, &right)| order.order.cmp(left.0, right.0) == Some(Ordering::Less))),
        Err(_) => true,
    })]
    pub fn seeded(references: &[Reference]) -> Result<(Self, Vec<ItemHandle>), OrderError>
    {
        let mut order = OrderMaintenance::new()?;
        let mut handles = Vec::with_capacity(references.len());
        for reference in references {
            let pos = order.push_back(reference.clone())?;
            handles.push(ItemHandle(pos));
        }
        Ok((Self { order }, handles))
    }

    /// Splice the order from the revision `base` to the revision `edited`.
    ///
    /// # Specification
    /// - requires: `base` holds this order's handles, one per reference of
    ///   `base_references`, in order; each list's references are distinct.
    /// - ensures: on success one handle per reference of `edited`, in order,
    ///   and the order holds exactly those handles in that order. The items
    ///   that keep their base handle are a longest subsequence of `edited`
    ///   whose references occur in `base` in the same order; every other item
    ///   takes a fresh handle after its predecessor's, and every base handle
    ///   not kept is removed.
    /// - provides: stable identity across insertions, deletions and moves
    ///   elsewhere: moving one item costs that item's handle only.
    /// - fails: when the structure cannot admit or remove an element; the order
    ///   is then unusable and the caller seeds a new one.
    /// - panics: none.
    /// - intension: one map build over `base` and one patience-sorting walk
    ///   over `edited`, so the splice is linear up to a logarithm.
    ///
    /// # Errors
    /// The order-maintenance structure's own refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the preserved-run helper is compared to exhaustive
    ///   subset search on four-slot words with distinct present positions from
    ///   zero through three. L3 insertion, deletion, swap, move, empty and
    ///   unchanged orders distinguish incorrect placement, census and
    ///   retirement through exact handles, references and comparisons.
    ///   Allocation and identifier ceilings of the underlying order remain
    ///   outside this finite domain.
    /// - witness: `order::tests::preserved_runs_match_an_exhaustive_subsequence_oracle`
    /// - witness: `order::tests::a_handle_survives_an_insertion_before_its_item`
    /// - witness: `order::tests::a_deleted_items_handle_goes_stale`
    /// - witness: `order::tests::handles_compare_in_the_edited_order`
    /// - witness: `order::tests::a_moved_item_costs_only_its_own_handle`
    /// - witness: `order::tests::empty_and_unchanged_splices_have_exact_censuses`
    #[spec(
        requires: base.len() == base_references.len()
            && base.iter().zip(base_references).all(|(&handle, &reference)|
                self.order.get(handle.0) == Some(reference)),
        ensures: |ret| match ret {
            Ok((ref handles, census)) => handles.len() == edited.len()
                && usize::from(census.kept).checked_add(usize::from(census.removed)) == Some(base.len())
                && usize::from(census.kept).checked_add(usize::from(census.inserted)) == Some(edited.len())
                && handles.iter().zip(edited).all(|(&handle, reference)|
                    self.order.get(handle.0) == Some(reference))
                && handles.windows(2).all(|pair| pair.first().zip(pair.last())
                    .is_some_and(|(&left, &right)| self.order.cmp(left.0, right.0) == Some(Ordering::Less))),
            Err(_) => true,
        },
    )]
    pub fn splice(
        &mut self,
        base: &[ItemHandle],
        base_references: &[&Reference],
        edited: &[Reference],
    ) -> Result<(Vec<ItemHandle>, SpliceCensus), OrderError>
    {
        let index: BTreeMap<&Reference, BasePosition> = base_references
            .iter()
            .enumerate()
            .map(|(position, &reference)| (reference, BasePosition(position)))
            .collect();
        let positions: Vec<Maybe<BasePosition, handle::Absent>> = edited
            .iter()
            .map(|reference| match index.get(reference) {
                Some(&position) => Maybe::Present(position),
                None => Maybe::Absent(handle::Absent::Stale),
            })
            .collect();
        let keep = longest_preserved_run(&positions);
        let mut kept_base = alloc::vec![false; base.len()];
        let mut kept: Vec<Maybe<ItemHandle, handle::Absent>> = Vec::with_capacity(edited.len());
        for position in positions {
            kept.push(match position {
                Maybe::Present(position) if keep.contains(&position) => {
                    match (base.get(position.0), kept_base.get_mut(position.0)) {
                        (Some(&handle), Some(mark)) => {
                            *mark = true;
                            Maybe::Present(handle)
                        },
                        _ => Maybe::Absent(handle::Absent::Stale),
                    }
                },
                Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(handle::Absent::Stale),
            });
        }
        let mut census = SpliceCensus::default();
        for (handle, &was_kept) in base.iter().zip(&kept_base) {
            if !was_kept {
                let _removed = self.order.remove(handle.0)?;
                census.removed = ItemCount::from(usize::from(census.removed).saturating_add(1));
            }
        }
        let mut handles = Vec::with_capacity(edited.len());
        let mut cursor: Maybe<Pos, handle::Absent> = Maybe::Absent(handle::Absent::Stale);
        for (reference, keep) in edited.iter().zip(kept) {
            let pos = match keep {
                Maybe::Present(handle) => {
                    census.kept = ItemCount::from(usize::from(census.kept).saturating_add(1));
                    handle.0
                },
                Maybe::Absent(_) => {
                    census.inserted =
                        ItemCount::from(usize::from(census.inserted).saturating_add(1));
                    match cursor {
                        Maybe::Present(previous) => {
                            self.order.insert_after(previous, reference.clone())?
                        },
                        Maybe::Absent(_) => self.order.push_front(reference.clone())?,
                    }
                },
            };
            cursor = Maybe::Present(pos);
            handles.push(ItemHandle(pos));
        }
        Ok((handles, census))
    }

    /// How two handles' items stand in source order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the order of the two items in the latest revision, decided in
    ///   constant time.
    /// - provides: `handle::Absent::Stale` when either handle names no live
    ///   item.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal and reversed live pairs, with each operand
    ///   separately stale or foreign and both operands the same invalid handle,
    ///   distinguish inverted order, premature equality and one-sided
    ///   validation by exact comparison variants.
    /// - witness: `order::tests::seeding_preserves_duplicate_payloads_with_distinct_handles`
    /// - witness: `order::tests::handles_compare_in_the_edited_order`
    /// - witness: `order::tests::comparisons_refuse_stale_and_foreign_operands`
    #[spec(ensures: |ret| self.order.cmp(left.0, right.0).map_or_else(
        || ret == Maybe::Absent(handle::Absent::Stale),
        |ordering| ret == Maybe::Present(ordering),
    ))]
    pub fn compare(
        &self,
        left: ItemHandle,
        right: ItemHandle,
    ) -> Maybe<Ordering, handle::Absent>
    {
        self.order
            .cmp(left.0, right.0)
            .map_or(Maybe::Absent(handle::Absent::Stale), Maybe::Present)
    }

    /// The reference of the item `handle` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reference the item carried when it took or kept the
    ///   handle.
    /// - provides: `handle::Absent::Stale` for a handle absent from the order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate live payloads, deleted handles and handles
    ///   from another order distinguish wrong payloads and accidental aliasing
    ///   by exact returned references or named absence.
    /// - witness: `order::tests::seeding_preserves_duplicate_payloads_with_distinct_handles`
    /// - witness: `order::tests::a_deleted_items_handle_goes_stale`
    /// - witness: `order::tests::comparisons_refuse_stale_and_foreign_operands`
    #[spec(ensures: |ret| self.order.get(handle.0).map_or_else(
        || ret == Maybe::Absent(handle::Absent::Stale),
        |reference| ret == Maybe::Present(reference),
    ))]
    pub fn reference(
        &self,
        handle: ItemHandle,
    ) -> Maybe<&Reference, handle::Absent>
    {
        self.order
            .get(handle.0)
            .map_or(Maybe::Absent(handle::Absent::Stale), Maybe::Present)
    }
}

/// An item's position in the base revision.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct BasePosition(usize);

/// The base positions of a longest run of edited items whose base order the
/// edit preserved.
///
/// # Specification
/// - requires: the present positions are distinct.
/// - ensures: the positions of a longest strictly ascending subsequence of the
///   present entries of `positions`.
/// - panics: none.
/// - intension: patience sorting: one binary search per entry, then one walk
///   back along the predecessor links.
///
/// # Adequacy
/// - hypothesis: L2 — enumerate all four-slot words over positions zero through
///   three and absence, admitting only distinct present positions. Independent
///   subset search supplies maximal length; input-order membership checks
///   distinguish a wrong predecessor chain or descending selection. L3 also
///   covers the empty slice. Larger input classes are not exhausted.
/// - witness: `order::tests::preserved_runs_match_an_exhaustive_subsequence_oracle`
#[spec(ensures: |ret| {
    let mut previous = None;
    let mut selected = 0_usize;
    let mut ascending = true;
    for &position in positions {
        if let Maybe::Present(position) = position
            && ret.contains(&position)
        {
            ascending &= previous.is_none_or(|earlier| earlier < position);
            previous = Some(position);
            selected = selected.saturating_add(1);
        }
    }
    ascending && selected == ret.len()
})]
fn longest_preserved_run(
    positions: &[Maybe<BasePosition, handle::Absent>]
) -> BTreeSet<BasePosition>
{
    // `tails[k]` ends the run of length `k + 1` with the least base position
    // found so far, beside the edited index that holds it.
    let mut tails: Vec<(BasePosition, usize)> = Vec::new();
    let mut previous: Vec<Option<(BasePosition, usize)>> = alloc::vec![None; positions.len()];
    for (at, &position) in positions.iter().enumerate() {
        let Maybe::Present(position) = position
        else {
            continue;
        };
        let length = tails.partition_point(|&(tail, _)| tail < position);
        if let Some(slot) = previous.get_mut(at) {
            *slot = length
                .checked_sub(1)
                .and_then(|shorter| tails.get(shorter))
                .copied();
        }
        match tails.get_mut(length) {
            Some(tail) => *tail = (position, at),
            None => tails.push((position, at)),
        }
    }
    let mut run = BTreeSet::new();
    let mut cursor = tails.last().copied();
    while let Some((position, at)) = cursor {
        let _fresh = run.insert(position);
        cursor = previous.get(at).copied().flatten();
    }
    run
}

#[cfg(test)]
mod tests;
