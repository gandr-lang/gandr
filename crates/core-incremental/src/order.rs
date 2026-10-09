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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ItemHandle(Pos);

/// What one splice did to the order.
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
    /// - hypothesis: L3 — the surfaces are the keep rule, the removal and the
    ///   placement of fresh handles, separated by an insertion before an item,
    ///   a deletion, a swap and a move to the front, each asserted by handle
    ///   equality, staleness and the order the handles compare in.
    /// - witness: `order::tests::a_handle_survives_an_insertion_before_its_item`
    /// - witness: `order::tests::a_deleted_items_handle_goes_stale`
    /// - witness: `order::tests::handles_compare_in_the_edited_order`
    /// - witness: `order::tests::a_moved_item_costs_only_its_own_handle`
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
    /// trivial.
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
}
