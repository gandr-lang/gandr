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

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::cmp::Ordering;

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
    #[anodized::spec(ensures: |ret| match ret {
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
    #[anodized::spec(
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
                | Some(&position) => Maybe::Present(position),
                | None => Maybe::Absent(handle::Absent::Stale),
            })
            .collect();
        let keep = longest_preserved_run(&positions);
        let mut kept_base = alloc::vec![false; base.len()];
        let mut kept: Vec<Maybe<ItemHandle, handle::Absent>> = Vec::with_capacity(edited.len());
        for position in positions {
            kept.push(match position {
                | Maybe::Present(position) if keep.contains(&position) => {
                    match (base.get(position.0), kept_base.get_mut(position.0)) {
                        | (Some(&handle), Some(mark)) => {
                            *mark = true;
                            Maybe::Present(handle)
                        },
                        | _ => Maybe::Absent(handle::Absent::Stale),
                    }
                },
                | Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(handle::Absent::Stale),
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
                | Maybe::Present(handle) => {
                    census.kept = ItemCount::from(usize::from(census.kept).saturating_add(1));
                    handle.0
                },
                | Maybe::Absent(_) => {
                    census.inserted =
                        ItemCount::from(usize::from(census.inserted).saturating_add(1));
                    match cursor {
                        | Maybe::Present(previous) => {
                            self.order.insert_after(previous, reference.clone())?
                        },
                        | Maybe::Absent(_) => self.order.push_front(reference.clone())?,
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
    /// - provides: `handle::Absent::Stale` when either handle no longer names
    ///   an item.
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
    #[anodized::spec(ensures: |ret| self.order.cmp(left.0, right.0).map_or_else(
        || ret == Maybe::Absent(handle::Absent::Stale),
        |ordering| ret == Maybe::Present(ordering),
    ))]
    pub fn compare(
        &self,
        left: ItemHandle,
        right: ItemHandle,
    ) -> Maybe<Ordering, handle::Absent>
    {
        match self.order.cmp(left.0, right.0) {
            | Some(ordering) => Maybe::Present(ordering),
            | None => Maybe::Absent(handle::Absent::Stale),
        }
    }

    /// The reference of the item `handle` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reference the item carried when it took or kept the
    ///   handle.
    /// - provides: `handle::Absent::Stale` for a handle no longer in the order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — duplicate live payloads, deleted handles and handles
    ///   from another order distinguish wrong payloads and accidental aliasing
    ///   by exact returned references or named absence.
    /// - witness: `order::tests::seeding_preserves_duplicate_payloads_with_distinct_handles`
    /// - witness: `order::tests::a_deleted_items_handle_goes_stale`
    /// - witness: `order::tests::comparisons_refuse_stale_and_foreign_operands`
    #[anodized::spec(ensures: |ret| self.order.get(handle.0).map_or_else(
        || ret == Maybe::Absent(handle::Absent::Stale),
        |reference| ret == Maybe::Present(reference),
    ))]
    pub fn reference(
        &self,
        handle: ItemHandle,
    ) -> Maybe<&Reference, handle::Absent>
    {
        match self.order.get(handle.0) {
            | Some(reference) => Maybe::Present(reference),
            | None => Maybe::Absent(handle::Absent::Stale),
        }
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
#[anodized::spec(ensures: |ret| {
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
            | Some(tail) => *tail = (position, at),
            | None => tails.push((position, at)),
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
mod tests
{
    use alloc::vec::Vec;
    use core::cmp::Ordering;

    use quenchant_shape::shape::Maybe;

    use super::ItemOrder;
    use super::handle;
    use crate::boundary::ItemCount;
    use crate::boundary::Occurrence;
    use crate::region::ItemKey;
    use crate::region::Reference;

    /// A fixture item's name.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Name(&'static str);

    /// The references of items named `names`, each the first of its key.
    ///
    /// # Specification
    /// trivial.
    fn references(names: &[Name]) -> Vec<Reference>
    {
        names
            .iter()
            .map(|name| Reference::Item {
                key: ItemKey::from(name.0),
                occurrence: Occurrence::from(0_usize),
            })
            .collect()
    }

    /// Splice an order seeded with `base` to `edited`.
    ///
    /// # Specification
    /// - requires: each name list is distinct, and the order can admit the
    ///   finite fixture.
    /// - ensures: returns the seeded and edited handles and the exact splice
    ///   census, with the order in the edited state.
    /// - panics: when seeding or splicing refuses the fixture.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — insertion, deletion, swap, move, empty and unchanged
    ///   fixtures distinguish incorrect state assembly by exact handle and
    ///   census observations. These inputs do not induce underlying capacity
    ///   refusals.
    /// - witness: `order::tests::a_handle_survives_an_insertion_before_its_item`
    /// - witness: `order::tests::a_deleted_items_handle_goes_stale`
    /// - witness: `order::tests::handles_compare_in_the_edited_order`
    /// - witness: `order::tests::a_moved_item_costs_only_its_own_handle`
    /// - witness: `order::tests::empty_and_unchanged_splices_have_exact_censuses`
    #[anodized::spec(ensures: |ret| ret.1.len() == base.len()
        && ret.2.len() == edited.len()
        && usize::from(ret.3.kept).checked_add(usize::from(ret.3.removed)) == Some(base.len())
        && usize::from(ret.3.kept).checked_add(usize::from(ret.3.inserted)) == Some(edited.len()))]
    fn spliced(
        base: &[Name],
        edited: &[Name],
    ) -> (
        ItemOrder,
        Vec<super::ItemHandle>,
        Vec<super::ItemHandle>,
        super::SpliceCensus,
    )
    {
        let base = references(base);
        let (mut order, before) = ItemOrder::seeded(&base).expect("the order builds");
        let base_references: Vec<&Reference> = base.iter().collect();
        let (after, census) = order
            .splice(&before, &base_references, &references(edited))
            .expect("the splice succeeds");
        (order, before, after, census)
    }

    #[test]
    fn a_handle_survives_an_insertion_before_its_item()
    {
        let (order, before, after, census) =
            spliced(&[Name("a"), Name("b")], &[Name("x"), Name("a"), Name("b")]);
        assert_eq!(after.get(1), before.first(), "a keeps its handle");
        assert_eq!(after.get(2), before.get(1), "b keeps its handle");
        assert_eq!(census.inserted, ItemCount::from(1_usize), "only x is fresh");
        let (Some(&x), Some(&a)) = (after.first(), after.get(1))
        else {
            panic!("three handles");
        };
        assert_eq!(
            order.compare(x, a),
            Maybe::Present(Ordering::Less),
            "the fresh handle sits before a"
        );
    }

    #[test]
    fn a_deleted_items_handle_goes_stale()
    {
        let (order, before, after, census) =
            spliced(&[Name("a"), Name("b"), Name("c")], &[Name("a"), Name("c")]);
        let Some(&b) = before.get(1)
        else {
            panic!("three base handles");
        };
        assert_eq!(
            order.reference(b),
            Maybe::Absent(handle::Absent::Stale),
            "b's handle names nothing"
        );
        assert_eq!(after.first(), before.first(), "a keeps its handle");
        assert_eq!(after.get(1), before.get(2), "c keeps its handle");
        assert_eq!(census.removed, ItemCount::from(1_usize), "one removal");
    }

    #[test]
    fn handles_compare_in_the_edited_order()
    {
        let (order, before, after, census) =
            spliced(&[Name("a"), Name("b")], &[Name("b"), Name("a")]);
        assert_eq!(
            census.kept,
            ItemCount::from(1_usize),
            "one of the swapped pair keeps its handle"
        );
        assert_eq!(
            census.inserted,
            ItemCount::from(1_usize),
            "the other takes a fresh one"
        );
        let (Some(&first), Some(&second)) = (after.first(), after.get(1))
        else {
            panic!("two handles");
        };
        assert_eq!(
            order.compare(first, second),
            Maybe::Present(Ordering::Less),
            "b now precedes a"
        );
        let stale = before
            .iter()
            .filter(|&&handle| order.reference(handle) == Maybe::Absent(handle::Absent::Stale))
            .count();
        assert_eq!(stale, 1_usize, "the moved item's old handle is stale");
    }

    #[test]
    fn a_moved_item_costs_only_its_own_handle()
    {
        let base = [Name("a"), Name("b"), Name("c"), Name("d"), Name("e")];
        let edited = [Name("e"), Name("a"), Name("b"), Name("c"), Name("d")];
        let (order, before, after, census) = spliced(&base, &edited);
        assert_eq!(
            census.kept,
            ItemCount::from(4_usize),
            "a to d keep their handles"
        );
        assert_eq!(after.get(1 ..), before.get(.. 4), "in order");
        let (Some(&e), Some(&a)) = (after.first(), after.get(1))
        else {
            panic!("five handles");
        };
        assert_eq!(
            order.compare(e, a),
            Maybe::Present(Ordering::Less),
            "e moved to the front"
        );
    }

    #[test]
    fn seeding_preserves_duplicate_payloads_with_distinct_handles()
    {
        let payloads = references(&[Name("a"), Name("a"), Name("b")]);
        let (order, handles) = ItemOrder::seeded(&payloads).expect("three entries");
        assert_eq!(handles.len(), 3);
        for (&handle, reference) in handles.iter().zip(&payloads) {
            assert_eq!(order.reference(handle), Maybe::Present(reference));
        }
        let first = handles[0];
        let repeated = handles[1];
        assert_ne!(first, repeated);
        assert_eq!(order.compare(first, first), Maybe::Present(Ordering::Equal));
        assert_eq!(
            order.compare(first, repeated),
            Maybe::Present(Ordering::Less)
        );
        assert_eq!(
            order.compare(repeated, first),
            Maybe::Present(Ordering::Greater)
        );
    }

    #[test]
    fn comparisons_refuse_stale_and_foreign_operands()
    {
        let (order, before, after, _) = spliced(&[Name("a"), Name("b")], &[Name("a")]);
        let (_, foreign) = ItemOrder::seeded(&references(&[Name("a")])).expect("foreign order");
        let live = after[0];
        let stale = before[1];
        let foreign = foreign[0];
        assert_eq!(
            order.reference(foreign),
            Maybe::Absent(handle::Absent::Stale)
        );
        for (left, right) in [
            (live, stale),
            (stale, live),
            (stale, stale),
            (live, foreign),
            (foreign, live),
            (foreign, foreign),
        ] {
            assert_eq!(
                order.compare(left, right),
                Maybe::Absent(handle::Absent::Stale)
            );
        }
    }

    #[test]
    fn empty_and_unchanged_splices_have_exact_censuses()
    {
        for (base, edited, (kept, inserted, removed)) in [
            (&[][..], &[][..], (0_usize, 0_usize, 0_usize)),
            (&[][..], &[Name("a")][..], (0, 1, 0)),
            (&[Name("a")][..], &[][..], (0, 0, 1)),
            (
                &[Name("a"), Name("b")][..],
                &[Name("a"), Name("b")][..],
                (2, 0, 0),
            ),
        ] {
            let (order, before, after, census) = spliced(base, edited);
            assert_eq!(census, super::SpliceCensus {
                kept: ItemCount::from(kept),
                inserted: ItemCount::from(inserted),
                removed: ItemCount::from(removed),
            });
            assert_eq!(after.len(), edited.len());
            if inserted == 0 && removed == 0 {
                assert_eq!(before, after);
            }
            for (&handle, name) in after.iter().zip(edited) {
                assert!(
                    matches!(order.reference(handle), Maybe::Present(&Reference::Item { ref key, occurrence })
                    if key.as_ref() == name.0.as_bytes() && usize::from(occurrence) == 0)
                );
            }
            for old in before {
                if !after.contains(&old) {
                    assert_eq!(order.reference(old), Maybe::Absent(handle::Absent::Stale));
                }
            }
        }
    }

    #[test]
    fn preserved_runs_match_an_exhaustive_subsequence_oracle()
    {
        assert_eq!(
            super::longest_preserved_run(&[]),
            alloc::collections::BTreeSet::new()
        );
        for word in 0_usize .. 625 {
            let mut rest = word;
            let positions: [Maybe<super::BasePosition, handle::Absent>; 4] =
                core::array::from_fn(|_| {
                    let digit = rest.checked_rem(5).expect("nonzero radix");
                    rest = rest.checked_div(5).expect("nonzero radix");
                    if digit == 4 {
                        Maybe::Absent(handle::Absent::Stale)
                    }
                    else {
                        Maybe::Present(super::BasePosition(digit))
                    }
                });
            if positions.iter().enumerate().any(|(index, &position)| {
                matches!(position, Maybe::Present(_))
                    && positions
                        .iter()
                        .skip(index.saturating_add(1))
                        .any(|&later| later == position)
            }) {
                continue;
            }
            let mut longest = 0_usize;
            for mask in 0_usize .. 16 {
                let mut previous = None;
                let mut length = 0_usize;
                let mut ascending = true;
                for (slot, &position) in positions.iter().enumerate() {
                    let bit = 1_usize
                        .checked_shl(u32::try_from(slot).expect("four slots"))
                        .expect("bounded shift");
                    if mask & bit == 0 {
                        continue;
                    }
                    match position {
                        | Maybe::Present(position) => {
                            ascending &= previous.is_none_or(|earlier| earlier < position);
                            previous = Some(position);
                            length = length.saturating_add(1);
                        },
                        | Maybe::Absent(_) => ascending = false,
                    }
                }
                if ascending {
                    longest = longest.max(length);
                }
            }
            let actual = super::longest_preserved_run(&positions);
            assert_eq!(actual.len(), longest, "optimal length for {positions:?}");
            let mut previous = None;
            let mut observed = 0_usize;
            for position in positions {
                if let Maybe::Present(position) = position
                    && actual.contains(&position)
                {
                    assert!(
                        previous.is_none_or(|earlier| earlier < position),
                        "subsequence of {positions:?}"
                    );
                    previous = Some(position);
                    observed = observed.saturating_add(1);
                }
            }
            assert_eq!(observed, actual.len(), "membership for {positions:?}");
        }
    }
}
