use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;

use super::BottomLabel;
use super::GroupIndex;
use super::GroupLen;
use super::GroupWidth;
use super::LiveLen;
use super::OrderError;
use super::OrderMaintenance;
use super::Pos;
use super::Slot;
use super::SlotGeneration;
use super::SlotIndex;
use super::SlotLimit;
use super::SpreadPosition;
use super::StructureIdCounter;
use super::TopGap;
use super::TopLabel;
use super::TopWidth;
use crate::interval::Interval;

/// Fixtures and structural oracles shared by the unit tests.
mod support
{
    use super::*;

    /// A structure over the production widths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns an empty structure over the full circle with the
    ///   default group width.
    /// - provides: the fixture the focused tests build on.
    /// - panics: panics when no distinct structure identity remains, which a
    ///   focused test run cannot reach.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the fresh fixture has empty ends, zero length and the
    ///   production widths; insertion then distinguishes it from a permanently
    ///   empty facade.
    /// - witness: `order::tests::new_is_empty`
    /// - witness: `order::tests::push_back_preserves_order`
    #[spec(ensures: |ret| ret.len == LiveLen::ZERO && ret.head.is_none() && ret.tail.is_none()
        && ret.width == GroupWidth::DEFAULT && ret.top == TopWidth::FULL)]
    pub(super) fn new_order<T>() -> OrderMaintenance<T>
    {
        OrderMaintenance::new().expect("structure id allocation succeeds in focused tests")
    }

    /// A structure over a narrow circle, narrow groups, or both, so splits,
    /// rebalances and capacity exhaustion are reachable in a handful of
    /// insertions.
    ///
    /// # Specification
    /// - requires: `top` lies in `[1, 64]`.
    /// - ensures: returns an empty structure over the two widths.
    /// - provides: the fixture that puts the relabel paths within a handful of
    ///   insertions.
    /// - panics: panics when no distinct structure identity remains, which a
    ///   focused test run cannot reach.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — narrow splits, rebalances and exact capacity refusal
    ///   distinguish the requested widths from the production ones.
    /// - witness: `order::tests::a_full_group_splits_behind_its_anchor`
    /// - witness: `order::tests::capacity_exhausts_on_a_circle_of_two_labels`
    #[spec(
        requires: (1 ..= 64).contains(&top.0),
        ensures: |ret| ret.len == LiveLen::ZERO && ret.top == top && ret.width == width,
    )]
    pub(super) fn narrow_order<T>(
        top: TopWidth,
        width: GroupWidth,
    ) -> OrderMaintenance<T>
    {
        OrderMaintenance::with_widths(top, width)
            .expect("structure id allocation succeeds in focused tests")
    }

    /// Asserts the structural invariant: every element's group is live and
    /// its label inside the group's universe; keys strictly increase along the
    /// list; each group is one contiguous run whose first, last and count it
    /// records, linked after the run before it; the base is the head's group;
    /// and the forward and backward chains agree with the length and the
    /// ends.
    ///
    /// # Specification
    /// - requires: `order` is any structure, sound or corrupted.
    /// - ensures: returns only when every part of the invariant holds.
    /// - provides: the structural oracle every mutating test asserts through,
    ///   so a broken link, a misplaced group or a repeated key is caught where
    ///   it is introduced.
    /// - panics: panics naming the part of the invariant that failed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite empty and nonempty chains, mutations at both
    ///   ends and an out-of-universe label separate the observer's assertions.
    ///   The constant-time exit certificate covers the ends; the body checks
    ///   both whole chains, the groups and the keys. Cyclic corruptions are
    ///   outside this terminating-walk domain.
    /// - witness: `order::tests::new_is_empty`
    /// - witness: `order::tests::remove_head_and_tail`
    /// - witness: `order::tests::invariant_observer_rejects_an_out_of_universe_label`
    #[spec(ensures: |()| order.head.is_none() == (order.len.0 == 0)
        && order.tail.is_none() == (order.len.0 == 0)
        && order.base.is_none() == (order.len.0 == 0)
        && order.head.is_none_or(|index| order.occupied(index).is_some_and(|occupied| occupied.prev.is_none()))
        && order.tail.is_none_or(|index| order.occupied(index).is_some_and(|occupied| occupied.next.is_none())))]
    pub(super) fn assert_invariant<T>(order: &OrderMaintenance<T>)
    {
        let universe = order.width.universe();
        let mut count: usize = 0;
        let mut previous_key = None;
        let mut last_seen: Option<SlotIndex> = None;
        let mut current: Option<GroupIndex> = None;
        let mut members: u32 = 0;
        let mut cursor = order.head;
        while let Some(index) = cursor {
            let occupied = order.occupied(index).expect("listed slot is occupied");
            assert!(
                u64::from(occupied.label.0) < universe.0,
                "labels stay inside the group's universe"
            );
            let base = order
                .base_label()
                .expect("a listed element's base resolves");
            let key = order
                .key(base, occupied)
                .expect("a listed element's group resolves");
            if let Some(before) = previous_key {
                assert!(key > before, "keys strictly increase in list order");
            }
            if current != Some(occupied.group) {
                if let Some(closed) = current {
                    let group = order.group(closed).expect("a closed group is live");
                    assert_eq!(
                        Some(group.last),
                        last_seen,
                        "a group's last element closes its run"
                    );
                    assert_eq!(group.len.0, members, "a group counts its run");
                    assert_eq!(
                        group.next,
                        Some(occupied.group),
                        "a group follows the run before it"
                    );
                }
                let group = order
                    .group(occupied.group)
                    .expect("an element's group is live");
                assert_eq!(group.first, index, "a group's first element opens its run");
                assert_eq!(
                    group.prev, current,
                    "a group's predecessor is the run before"
                );
                assert!(
                    group.label <= order.top.last(),
                    "group labels stay on the circle"
                );
                current = Some(occupied.group);
                members = 0;
            }
            members = members.saturating_add(1);
            previous_key = Some(key);
            last_seen = Some(index);
            count = count.saturating_add(1);
            cursor = occupied.next;
        }
        if let Some(closed) = current {
            let group = order.group(closed).expect("the last group is live");
            assert_eq!(
                Some(group.last),
                last_seen,
                "the last group closes at the tail"
            );
            assert_eq!(group.len.0, members, "the last group counts its run");
            assert_eq!(group.next, None, "no group follows the last");
        }
        assert_eq!(
            order.base,
            order
                .head
                .map(|index| order.occupied(index).expect("the head is occupied").group),
            "the base is the head's group"
        );
        assert_eq!(count, usize::from(order.len), "forward length matches len");
        assert_eq!(last_seen, order.tail, "tail is the last listed element");

        let mut back_count: usize = 0;
        let mut back_cursor = order.tail;
        let mut first_seen = None;
        while let Some(index) = back_cursor {
            let occupied = order.occupied(index).expect("listed slot is occupied");
            first_seen = Some(index);
            back_count = back_count.saturating_add(1);
            back_cursor = occupied.prev;
        }
        assert_eq!(
            back_count,
            usize::from(order.len),
            "backward length matches len"
        );
        assert_eq!(first_seen, order.head, "head is the first listed element");
    }

    /// Asserts O(1) comparison agrees with list order for every pair, and
    /// that each element compares equal only to itself.
    ///
    /// # Specification
    /// - requires: `order` has resolvable links, since the pairs are drawn by
    ///   walking it.
    /// - ensures: returns only when every ordered pair of handles compares as
    ///   their list ranks do, so each element compares equal to itself alone.
    /// - provides: the comparison oracle — the constant-time answer checked
    ///   against the linear rank it must agree with.
    /// - panics: panics on the first pair whose comparison disagrees with its
    ///   rank pair.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — resolvable ordered links pass the rank comparison,
    ///   while reversed labels on the same links are rejected. The linear exit
    ///   predicate certifies adjacent ordering; the body also checks every rank
    ///   pair and reflexivity.
    /// - witness: `order::tests::a_full_group_splits_behind_its_anchor`
    /// - witness: `order::tests::comparison_observer_rejects_reversed_labels`
    #[spec(ensures: |()| order.iter().map(|(pos, _value)| pos)
        .is_sorted_by(|left, right| order.cmp(*left, *right) == Some(Ordering::Less)))]
    pub(super) fn assert_cmp_consistent<T>(order: &OrderMaintenance<T>)
    {
        let handles = positions(order);
        for (left_rank, &left) in handles.iter().enumerate() {
            for (right_rank, &right) in handles.iter().enumerate() {
                assert_eq!(
                    Some(left_rank.cmp(&right_rank)),
                    order.cmp(left, right),
                    "cmp matches list order for every pair"
                );
            }
        }
    }

    /// The handles in list order.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn positions<T>(order: &OrderMaintenance<T>) -> Vec<Pos>
    {
        order.iter().map(|(pos, _value)| pos).collect()
    }

    /// The payloads in list order.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn ordered<T>(order: &OrderMaintenance<T>) -> Vec<T>
    where
        T: Copy,
    {
        order.iter().map(|(_pos, &value)| value).collect()
    }

    /// The live groups in list order, from the base.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn groups<T>(order: &OrderMaintenance<T>) -> Vec<GroupIndex>
    {
        let mut found = Vec::new();
        let mut cursor = order.base;
        while let Some(index) = cursor {
            found.push(index);
            cursor = order.group(index).expect("a linked group is live").next;
        }
        found
    }

    /// The counts of the live groups in list order.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn group_lens<T>(order: &OrderMaintenance<T>) -> Vec<GroupLen>
    {
        groups(order)
            .into_iter()
            .map(|index| order.group(index).expect("a linked group is live").len)
            .collect()
    }

    /// Points the `next` link of the element at `index` at a slot the arena
    /// does not have, so the next walk over that link must report
    /// [`OrderError::Inconsistent`].
    ///
    /// # Specification
    /// - requires: `index` names a live element of `order`.
    /// - ensures: the element's `next` link names a slot the arena does not
    ///   have, and every other field is untouched.
    /// - provides: the one corruption that makes [`OrderError::Inconsistent`]
    ///   reachable, which no public operation produces.
    /// - panics: panics when `index` does not name a live element.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bounded live fixtures acquire a dangling successor
    ///   that causes typed insertion and removal refusal. Scalar captures
    ///   preserve the target's generation, label and predecessor; generic
    ///   payload identity remains a fixture observation.
    /// - witness: `order::tests::corrupt_link_insert_is_typed`
    /// - witness: `order::tests::corrupt_link_removal_is_typed`
    /// - witness: `order::tests::iterator_follows_links_and_preserves_terminal_absence`
    #[spec(
        requires: order.occupied(index).is_some(),
        captures: unchanged = order.occupied(index).map(|occupied| (occupied.generation, occupied.label, occupied.prev)),
        ensures: |()| order.occupied(index).is_some_and(|occupied|
            unchanged == Some((occupied.generation, occupied.label, occupied.prev))
                && occupied.next.is_some_and(|next| order.slot(next).is_none())),
    )]
    pub(super) fn corrupt_next_link<T>(
        order: &mut OrderMaintenance<T>,
        index: SlotIndex,
    )
    {
        let dangling = SlotIndex(u32::MAX);
        let occupied = order.occupied_mut(index).expect("slot is occupied");
        occupied.next = Some(dangling);
    }
}

use support::assert_cmp_consistent;
use support::assert_invariant;
use support::corrupt_next_link;
use support::group_lens;
use support::groups;
use support::narrow_order;
use support::new_order;
use support::ordered;
use support::positions;

#[test]
fn group_widths_clamp_into_their_range()
{
    for (offered, expected) in [(0, 4), (4, 4), (16, 16), (31, 31), (32, 31), (u32::MAX, 31)] {
        assert_eq!(GroupWidth::from(offered), GroupWidth(expected));
    }
    let widest: OrderMaintenance<()> =
        OrderMaintenance::with_group_width(GroupWidth::from(100)).expect("a structure");
    assert_eq!(widest.width, GroupWidth::MAX);
    assert_eq!(u32::from(widest.width), 31);
}

#[test]
fn a_group_spreads_its_elements_evenly()
{
    let narrow = GroupWidth::MIN.universe();
    assert_eq!(narrow.0, 16);
    let spread: Vec<_> = (1 ..= 3)
        .map(|position| {
            OrderMaintenance::<()>::spread_label(narrow, GroupLen(3), SpreadPosition(position))
        })
        .collect();
    assert_eq!(spread, [
        Some(BottomLabel(4)),
        Some(BottomLabel(8)),
        Some(BottomLabel(12))
    ]);
    assert_eq!(
        OrderMaintenance::<()>::spread_label(narrow, GroupLen(5), SpreadPosition(1)),
        Some(BottomLabel(2)),
        "sixteen over six rounds down"
    );
    let widest = GroupWidth::MAX.universe();
    assert_eq!(
        OrderMaintenance::<()>::spread_label(widest, GroupLen(1), SpreadPosition(1)),
        Some(BottomLabel(0x4000_0000))
    );
    assert_eq!(
        OrderMaintenance::<()>::spread_label(
            widest,
            GroupLen(u32::MAX),
            SpreadPosition(u64::from(u32::MAX))
        ),
        Some(BottomLabel(0x7FFF_FFFF)),
        "the wide product keeps the last label below the universe"
    );
}

#[test]
fn top_labels_are_measured_around_the_circle()
{
    // Five appends at the narrowest width fill the first group and split it.
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth(3), GroupWidth::MIN);
    let [head, _, _, _, tail] = [0, 1, 2, 3, 4].map(|value| {
        order
            .push_back(value)
            .expect("an append on an empty circle fits")
    });
    let [base, later] =
        <[GroupIndex; 2]>::try_from(groups(&order)).expect("five appends make two groups");
    assert_eq!(TopWidth(3).last(), TopLabel(7));
    assert_eq!(TopWidth::FULL.last(), TopLabel(u64::MAX));
    // Put the base at 6 and the later group at 1: one past the circle's end.
    order.group_mut(base).expect("the base").label = TopLabel(6);
    order.group_mut(later).expect("the later group").label = TopLabel(1);
    assert_eq!(order.distance(base, later), Ok(TopGap(3)));
    assert_eq!(order.distance(later, base), Ok(TopGap(5)));
    assert_eq!(order.distance(base, base), Ok(TopGap(8)));
    assert_eq!(
        Some(TopWidth::FULL.universe()),
        1_u128.checked_shl(64).map(TopGap)
    );
    let last = order
        .occupied(order.tail.expect("a tail"))
        .expect("the tail is occupied");
    let base_label = order.base_label().expect("the base resolves");
    assert_eq!(base_label, TopLabel(6));
    assert_eq!(
        order.key(base_label, last).map(|key| key.top),
        Some(TopLabel(3))
    );
    assert_invariant(&order);
    assert_cmp_consistent(&order);
    assert_eq!(
        order.cmp(head, tail),
        Some(Ordering::Less),
        "a wrapped label still follows the base"
    );
}

#[test]
fn slot_indices_preserve_numeric_bounds()
{
    for value in [0_u32, u32::MAX] {
        let position = usize::try_from(value).expect("supported host holds a slot index");
        let index = SlotIndex::try_from(position).expect("index fits");
        assert_eq!(index, SlotIndex(value));
        assert_eq!(usize::try_from(index), Ok(position));
    }
    #[cfg(target_pointer_width = "64")]
    {
        let first_excess = usize::try_from(u64::from(u32::MAX).saturating_add(1))
            .expect("wide host holds the first excess");
        assert!(SlotIndex::try_from(first_excess).is_err());
    }
}

#[test]
fn generation_and_length_refuse_wraparound()
{
    assert_eq!(SlotGeneration::FIRST.successor(), Some(SlotGeneration(1)));
    assert_eq!(
        SlotGeneration(u32::MAX.wrapping_sub(1)).successor(),
        Some(SlotGeneration::LAST)
    );
    assert_eq!(SlotGeneration::LAST.successor(), None);
    assert_eq!(LiveLen::ZERO.incremented(), Some(LiveLen(1)));
    assert_eq!(
        LiveLen(usize::MAX.wrapping_sub(1)).incremented(),
        Some(LiveLen(usize::MAX))
    );
    assert_eq!(LiveLen(usize::MAX).incremented(), None);
    assert_eq!(LiveLen(1).decremented(), Some(LiveLen::ZERO));
    assert_eq!(
        LiveLen(usize::MAX).decremented(),
        Some(LiveLen(usize::MAX.wrapping_sub(1)))
    );
    assert_eq!(LiveLen::ZERO.decremented(), None);
}

#[test]
fn concurrent_identity_allocation_is_disjoint()
{
    extern crate std;

    let counter = StructureIdCounter(core::sync::atomic::AtomicUsize::new(0));
    let mut issued = std::thread::scope(|scope| {
        let workers = core::iter::repeat_with(|| {
            scope.spawn(|| {
                core::iter::repeat_with(|| counter.allocate().expect("bounded counter has room").0)
                    .take(32)
                    .collect::<Vec<_>>()
            })
        })
        .take(4)
        .collect::<Vec<_>>();
        workers
            .into_iter()
            .flat_map(|worker| worker.join().expect("identity worker succeeds"))
            .collect::<Vec<_>>()
    });
    issued.sort_unstable();
    assert_eq!(issued, (0 .. 128).collect::<Vec<_>>());
}

#[test]
fn navigation_rejects_stale_and_foreign_handles()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let stale = order.push_back(10).expect("insert initial value");
    assert_eq!(order.remove(stale), Ok(Some(10)));
    let replacement = order.push_back(20).expect("reuse slot");
    let mut other: OrderMaintenance<u64> = new_order();
    let foreign = other.push_back(30).expect("insert foreign value");
    assert_eq!(order.get(replacement), Some(&20));
    assert!(!bool::from(order.is_empty()));
    for rejected in [stale, foreign] {
        assert_eq!(order.next(rejected), None);
        assert_eq!(order.prev(rejected), None);
    }
}

#[test]
fn arena_observers_distinguish_slot_states()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let live = order.push_back(11).expect("insert live slot");
    assert_eq!(order.pos_at(live.index), Some(live));
    assert_eq!(order.resolve(live).map(|occupied| occupied.value), Some(11));
    order
        .occupied_mut(live.index)
        .expect("live mutable payload")
        .value = 17;
    assert_eq!(order.get(live), Some(&17));
    assert_eq!(order.remove(live), Ok(Some(17)));
    assert!(matches!(order.slot(live.index), Some(&Slot::Free(_))));
    assert_eq!(order.pos_at(live.index), None);
    assert!(order.occupied(live.index).is_none());
    assert!(order.occupied_mut(live.index).is_none());
    let position = usize::try_from(live.index).expect("slot position fits");
    *order
        .slots
        .get_mut(position)
        .expect("retire freed fixture slot") = Slot::Retired;
    assert_eq!(order.pos_at(live.index), None);
    assert!(order.occupied(live.index).is_none());
    assert!(order.occupied_mut(live.index).is_none());
    let absent = SlotIndex(u32::MAX);
    assert!(order.slot(absent).is_none());
    assert!(order.occupied(absent).is_none());
    assert!(order.occupied_mut(absent).is_none());
    assert_eq!(order.pos_at(absent), None);
    assert!(
        order
            .resolve(Pos {
                index: absent,
                ..live
            })
            .is_none()
    );
}

#[test]
fn slot_writes_refuse_dead_indices()
{
    let mut order = new_order();
    let removed = order.push_back(()).expect("insert fixture");
    assert_eq!(order.remove(removed), Ok(Some(())));
    for index in [removed.index, SlotIndex(u32::MAX)] {
        assert_eq!(order.set_prev(index, None), Err(OrderError::Inconsistent));
        assert_eq!(order.set_next(index, None), Err(OrderError::Inconsistent));
    }
}

#[test]
fn allocation_refuses_a_broken_free_list()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let live = order.push_back(11).expect("insert live value");
    order.free_head = Some(live.index);
    assert_eq!(order.push_back(22), Err(OrderError::Inconsistent));
    assert_eq!(order.get(live), Some(&11));
    assert_eq!(usize::from(order.len()), 1);
    assert_eq!(order.first(), Some(live));
    assert_eq!(order.last(), Some(live));
}

#[test]
fn iterator_follows_links_and_preserves_terminal_absence()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let first = order.push_back(1).expect("insert first");
    let second = order.push_back(2).expect("insert second");
    {
        let mut walk = order.iter();
        assert_eq!(walk.next(), Some((first, &1)));
        assert_eq!(walk.next(), Some((second, &2)));
        assert_eq!(walk.next(), None);
        assert_eq!(walk.next(), None);
    }
    corrupt_next_link(&mut order, first.index);
    let mut walk = order.iter();
    assert_eq!(walk.next(), Some((first, &1)));
    assert_eq!(walk.next(), None);
    assert_eq!(walk.next(), None);
}

#[test]
fn invariant_observer_rejects_an_out_of_universe_label()
{
    extern crate std;

    let mut order = new_order();
    let live = order.push_back(()).expect("insert live slot");
    let outside = u32::try_from(order.width.universe().0).expect("the default universe fits");
    order.occupied_mut(live.index).expect("live slot").label = BottomLabel(outside);
    assert!(std::panic::catch_unwind(|| assert_invariant(&order)).is_err());
}

#[test]
fn comparison_observer_rejects_reversed_labels()
{
    extern crate std;

    let mut order = new_order();
    let first = order.push_back(()).expect("insert first");
    let second = order.push_back(()).expect("insert second");
    let higher = order
        .occupied(second.index)
        .expect("second label")
        .label
        .0
        .saturating_add(1);
    order.occupied_mut(first.index).expect("first").label = BottomLabel(higher);
    assert!(std::panic::catch_unwind(|| assert_cmp_consistent(&order)).is_err());
}

#[test]
fn formatter_refusal_is_propagated()
{
    extern crate std;
    use std::io::Write as _;

    let mut bytes = [0_u8; 1];
    let mut output = bytes.as_mut_slice();
    assert!(write!(&mut output, "{}", OrderError::CapacityExhausted).is_err());
}

#[test]
fn new_is_empty()
{
    let order: OrderMaintenance<u64> = new_order();
    assert!(bool::from(order.is_empty()), "a fresh structure is empty");
    assert_eq!(
        0,
        usize::from(order.len()),
        "a fresh structure has no elements"
    );
    assert_eq!(None, order.first(), "no first element");
    assert_eq!(None, order.last(), "no last element");
    assert_eq!(Vec::<u64>::new(), ordered(&order), "iteration is empty");
    assert_invariant(&order);
}

#[test]
fn push_back_preserves_order()
{
    let mut order: OrderMaintenance<u64> = new_order();
    for value in 0 .. 6 {
        order.push_back(value).expect("push_back succeeds");
    }
    assert_eq!(
        vec![0, 1, 2, 3, 4, 5],
        ordered(&order),
        "push_back appends in order"
    );
    assert_eq!(6, usize::from(order.len()), "length tracks insertions");
    let handles = positions(&order);
    assert_eq!(order.first(), handles.first().copied(), "first is the head");
    assert_eq!(order.last(), handles.last().copied(), "last is the tail");
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn push_front_reverses()
{
    let mut order: OrderMaintenance<u64> = new_order();
    for value in 0 .. 6 {
        order.push_front(value).expect("push_front succeeds");
    }
    assert_eq!(
        vec![5, 4, 3, 2, 1, 0],
        ordered(&order),
        "push_front prepends"
    );
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn insert_after_and_before_place_correctly()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let first = order.push_back(0).expect("push_back succeeds");
    let last = order.push_back(9).expect("push_back succeeds");
    let middle = order.insert_after(first, 5).expect("insert_after succeeds");
    order
        .insert_before(middle, 3)
        .expect("insert_before succeeds");
    order
        .insert_before(last, 7)
        .expect("insert_before succeeds");
    assert_eq!(
        vec![0, 3, 5, 7, 9],
        ordered(&order),
        "inserts land at the right spots"
    );
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn remove_middle_unlinks_and_invalidates()
{
    let mut order: OrderMaintenance<u64> = new_order();
    order.push_back(0).expect("push_back succeeds");
    let middle = order.push_back(1).expect("push_back succeeds");
    order.push_back(2).expect("push_back succeeds");
    assert_eq!(
        Ok(Some(1)),
        order.remove(middle),
        "remove returns the payload"
    );
    assert_eq!(vec![0, 2], ordered(&order), "the element is unlinked");
    assert!(
        !bool::from(order.contains(middle)),
        "the removed handle is stale"
    );
    assert_eq!(None, order.get(middle), "get on a stale handle is None");
    assert_eq!(Ok(None), order.remove(middle), "double remove is Ok(None)");
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn remove_head_and_tail()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let head = order.push_back(0).expect("push_back succeeds");
    order.push_back(1).expect("push_back succeeds");
    let tail = order.push_back(2).expect("push_back succeeds");
    assert_eq!(Ok(Some(0)), order.remove(head), "remove head");
    assert_eq!(Ok(Some(2)), order.remove(tail), "remove tail");
    assert_eq!(vec![1], ordered(&order), "only the middle survives");
    assert_invariant(&order);
}

#[test]
fn remove_only_element_empties()
{
    const SOLE_ELEMENT_VALUE: u64 = 42;

    let mut order: OrderMaintenance<u64> = new_order();
    let only = order
        .push_back(SOLE_ELEMENT_VALUE)
        .expect("push_back succeeds");
    assert_eq!(
        Ok(Some(SOLE_ELEMENT_VALUE)),
        order.remove(only),
        "remove the sole element"
    );
    assert!(bool::from(order.is_empty()), "structure is empty again");
    assert_invariant(&order);
    order.push_back(7).expect("reuse after emptying");
    assert_eq!(vec![7], ordered(&order), "can insert after emptying");
    assert_invariant(&order);
}

#[test]
fn a_full_group_splits_from_its_back()
{
    // At the width eight, seven appends fill one group without a split; the
    // split then cuts its last four into a group of their own and leaves the
    // first three, each group spread over its universe.
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth::FULL, GroupWidth(8));
    for value in 0 .. 7 {
        order
            .push_back(value)
            .expect("an append fits the first group");
    }
    assert_eq!(group_lens(&order), [GroupLen(7)]);
    let base = order.base.expect("a base");
    order.split(base).expect("the split succeeds");
    assert_eq!(group_lens(&order), [GroupLen(3), GroupLen(4)]);
    let labels: Vec<u32> = order
        .iter()
        .map(|(pos, _value)| order.resolve(pos).expect("live").label.0)
        .collect();
    assert_eq!(labels, [64, 128, 192, 51, 102, 153, 204]);
    assert_eq!(ordered(&order), [0, 1, 2, 3, 4, 5, 6]);
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn a_full_group_splits_behind_its_anchor()
{
    // The narrowest width fills a group after a few insertions behind one
    // anchor; each further insertion there splits it again.
    const SENTINEL: u64 = 100;

    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth::FULL, GroupWidth::MIN);
    let anchor = order.push_back(0).expect("push_back succeeds");
    order.push_back(SENTINEL).expect("push_back succeeds");
    for value in 1 ..= 20 {
        order
            .insert_after(anchor, value)
            .expect("insert_after succeeds across a split");
        assert_invariant(&order);
        assert_cmp_consistent(&order);
    }
    let mut expected: Vec<u64> = vec![0];
    expected.extend((1 ..= 20).rev());
    expected.push(SENTINEL);
    assert_eq!(ordered(&order), expected, "splits preserve the list order");
    assert!(groups(&order).len() > 1, "the anchor's group split");
}

#[test]
fn a_full_front_group_splits_before_its_head()
{
    // Exhaust the labels before the head so a push_front must split with no
    // predecessor.
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth::FULL, GroupWidth::MIN);
    for value in 0 .. 12 {
        order
            .push_front(value)
            .expect("push_front succeeds across a split");
        assert_invariant(&order);
        assert_cmp_consistent(&order);
    }
    assert_eq!(
        ordered(&order),
        (0 .. 12).rev().collect::<Vec<u64>>(),
        "front splits preserve order"
    );
    assert!(groups(&order).len() > 1, "the front group split");
}

#[test]
fn a_crowded_circle_spreads_the_groups_after_the_full_one()
{
    // Three groups on a circle of sixteen labels, at 0, 1 and 2: the room
    // after the first is spent. The walk passes the second (one label on, at
    // most 1²) and the third (two on, at most 2²) and returns to the first, the
    // whole circle on, more than 3²; the two it passed spread over the circle
    // at 16/3 and 32/3.
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth(4), GroupWidth::MIN);
    for value in 0 .. 7 {
        order.push_back(value).expect("appends fit");
    }
    let [first, second, third] = <[GroupIndex; 3]>::try_from(groups(&order))
        .expect("seven appends at the narrowest width make three groups");
    for (index, label) in [(first, 0), (second, 1), (third, 2)] {
        order.group_mut(index).expect("a group").label = TopLabel(label);
    }
    order.rebalance(first).expect("the circle has room");
    let labels: Vec<u64> = groups(&order)
        .into_iter()
        .map(|index| order.group(index).expect("a group").label.0)
        .collect();
    assert_eq!(labels, [0, 5, 10]);
    assert_invariant(&order);

    // Now 0, 14 and 15: the room after the second is spent, and the walk from
    // it passes the third and wraps to the base, two labels on, at most 2²,
    // then returns to the second. The third and the base spread from 14 by
    // 16/3 and 32/3, to 3 and 8: the base itself moves, and every group keeps
    // its distance's order from it.
    for (index, label) in [(first, 0), (second, 14), (third, 15)] {
        order.group_mut(index).expect("a group").label = TopLabel(label);
    }
    order.rebalance(second).expect("the circle has room");
    let labels: Vec<u64> = groups(&order)
        .into_iter()
        .map(|index| order.group(index).expect("a group").label.0)
        .collect();
    assert_eq!(labels, [8, 14, 3]);
    assert_invariant(&order);
    assert_cmp_consistent(&order);
    assert_eq!(ordered(&order), (0 .. 7).collect::<Vec<u64>>());
}

#[test]
fn appends_wrap_the_rebalance_past_the_last_group()
{
    // Appends split the last group again and again, each new group halfway
    // from it to the base around the circle. With the walk stopping at the
    // last group, the append that spends that room is refused; walking on to
    // the base, every append fits and the base moves. The circle of 2^16
    // labels holds the square of the groups 400 appends make.
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth(16), GroupWidth::MIN);
    let mut base_moved = false;
    for value in 0 .. 400 {
        order
            .push_back(value)
            .expect("an append past the last group wraps to the base");
        let base = order.base.expect("a base");
        base_moved |= order.group(base).expect("the base").label != TopLabel(0);
    }
    assert!(base_moved, "a rebalance wrapped past the last group");
    assert_eq!(ordered(&order), (0 .. 400).collect::<Vec<u64>>());
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn capacity_exhausts_on_a_circle_of_two_labels()
{
    // A circle of two labels holds two groups: the second sits one label on
    // from the first, and a third finds no room in a whole-circle walk. At the
    // narrowest width the two groups hold six appends, and the seventh splits
    // the last group into a third.
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth(1), GroupWidth::MIN);
    for value in 0 .. 6 {
        order.push_back(value).expect("six appends fit two groups");
    }
    assert_eq!(
        Err(OrderError::CapacityExhausted),
        order.push_back(6),
        "a third group on a circle of two labels is refused"
    );
    assert_eq!(
        ordered(&order),
        [0, 1, 2, 3, 4, 5],
        "the refused element left no trace"
    );
    assert_eq!(6, usize::from(order.len()), "the refusal did not count");
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn emptying_the_base_group_frees_it_and_moves_the_base()
{
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth::FULL, GroupWidth::MIN);
    let [first, second, third, _, fifth] =
        [0, 1, 2, 3, 4].map(|value| order.push_back(value).expect("appends fit"));
    let [base, later] =
        <[GroupIndex; 2]>::try_from(groups(&order)).expect("five appends make two groups");
    assert_eq!(group_lens(&order), [GroupLen(2), GroupLen(3)]);
    for pos in [first, second] {
        order
            .remove(pos)
            .expect("a removal")
            .expect("a live element");
        assert_invariant(&order);
    }
    assert_eq!(order.base, Some(later), "the next group is the base");
    assert!(order.group(base).is_none(), "the emptied group is freed");
    assert_eq!(order.free_group, Some(base));
    assert_eq!(order.cmp(third, fifth), Some(Ordering::Less));
    // The next split takes the freed group slot.
    for value in 5 .. 9 {
        order.push_back(value).expect("appends fit");
    }
    assert!(
        groups(&order).contains(&base),
        "a split reuses the freed slot"
    );
    assert_eq!(order.free_group, None);
    assert_invariant(&order);
    assert_cmp_consistent(&order);
}

#[test]
fn structure_id_exhaustion_is_typed()
{
    let counter = StructureIdCounter::nearly_exhausted();
    let mut first: OrderMaintenance<u64> =
        OrderMaintenance::with_widths_from_counter(TopWidth::FULL, GroupWidth::MIN, &counter)
            .expect("the last distinct structure id is available");
    let old = first.push_back(1).expect("insertion succeeds");

    let exhausted = OrderMaintenance::<u64>::with_widths_from_counter(
        TopWidth::FULL,
        GroupWidth::MIN,
        &counter,
    );

    assert_eq!(
        Err(OrderError::StructureIdExhausted),
        exhausted.map(|_ignored: OrderMaintenance<u64>| ()),
        "structure id exhaustion is typed"
    );
    assert_eq!(
        Some(&1),
        first.get(old),
        "an extant position is not aliased by a wrapped structure id"
    );
}

#[test]
fn exhausted_generation_retires_slot_and_allocates_another()
{
    let mut order: OrderMaintenance<u64> = narrow_order(TopWidth::FULL, GroupWidth::MIN);
    let first = order.push_back(0).expect("initial insert succeeds");
    let exhausted = Pos {
        generation: SlotGeneration::LAST,
        ..first
    };
    let occupied = order.occupied_mut(first.index).expect("slot is occupied");
    occupied.generation = SlotGeneration::LAST;

    assert_eq!(
        Ok(Some(0)),
        order.remove(exhausted),
        "remove the exhausted slot"
    );
    assert!(
        matches!(order.slot(exhausted.index), Some(&Slot::Retired)),
        "the exhausted slot is retired permanently"
    );
    let replacement = order.push_back(1).expect("a fresh slot is allocated");
    assert_ne!(
        exhausted.index, replacement.index,
        "the retired slot index is not reused"
    );
    assert_eq!(
        None,
        order.get(exhausted),
        "the stale exhausted-generation handle does not alias the replacement"
    );
    assert_eq!(Some(&1), order.get(replacement), "the replacement resolves");
}

#[test]
fn retired_slot_capacity_exhaustion_is_typed()
{
    let mut order: OrderMaintenance<u64> =
        OrderMaintenance::with_widths_and_slot_limit(TopWidth::FULL, GroupWidth::MIN, SlotLimit(1))
            .expect("bounded test structure can be constructed");
    let first = order
        .push_back(0)
        .expect("initial insert consumes the slot");
    let exhausted = Pos {
        generation: SlotGeneration::LAST,
        ..first
    };
    let occupied = order.occupied_mut(first.index).expect("slot is occupied");
    occupied.generation = SlotGeneration::LAST;

    assert_eq!(Ok(Some(0)), order.remove(exhausted), "retire the only slot");
    assert_eq!(
        Err(OrderError::CapacityExhausted),
        order.push_back(1),
        "when every representable slot is retired, insertion reports typed exhaustion"
    );
    assert_eq!(
        None,
        order.get(exhausted),
        "the retired slot remains unavailable to stale handles"
    );
    assert!(order.base.is_none(), "the refused element left no group");
    assert!(
        order.free_group.is_some(),
        "the group it took is free again"
    );
    assert_invariant(&order);
}

#[test]
fn corrupt_link_removal_is_typed()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let head = order.push_back(0).expect("push_back succeeds");
    order.push_back(1).expect("push_back succeeds");
    corrupt_next_link(&mut order, head.index);
    assert_eq!(
        Err(OrderError::Inconsistent),
        order.remove(head),
        "a dangling successor link surfaces as a typed inconsistency"
    );
}

#[test]
fn corrupt_link_insert_is_typed()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let head = order.push_back(0).expect("push_back succeeds");
    order.push_back(1).expect("push_back succeeds");
    corrupt_next_link(&mut order, head.index);
    assert_eq!(
        Err(OrderError::Inconsistent),
        order.insert_after(head, 2),
        "an insertion beside a dangling successor link is a typed inconsistency"
    );
}

#[test]
fn navigation_walks_both_ways()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let first = order.push_back(0).expect("push_back succeeds");
    let second = order.push_back(1).expect("push_back succeeds");
    let third = order.push_back(2).expect("push_back succeeds");
    assert_eq!(Some(second), order.next(first), "next walks forward");
    assert_eq!(None, order.next(third), "next at the tail is None");
    assert_eq!(Some(second), order.prev(third), "prev walks backward");
    assert_eq!(None, order.prev(first), "prev at the head is None");
    assert_eq!(Some(&1), order.get(second), "get returns the payload");
}

#[test]
fn slot_reuse_distinguishes_generation()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let first = order.push_back(0).expect("push_back succeeds");
    order.push_back(1).expect("push_back succeeds");
    assert_eq!(Ok(Some(0)), order.remove(first), "free the first slot");
    // The next allocation reuses the freed slot with a bumped generation.
    let reused = order.push_back(2).expect("push_back reuses the slot");
    assert_eq!(reused.index, first.index, "the freed slot index is reused");
    assert_ne!(
        first.generation, reused.generation,
        "the generation is bumped"
    );
    assert_eq!(
        None,
        order.get(first),
        "the stale handle does not alias the reuse"
    );
    assert_eq!(Some(&2), order.get(reused), "the fresh handle resolves");
}

#[test]
fn stale_handle_insert_errors()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let only = order.push_back(0).expect("push_back succeeds");
    order.remove(only).expect("remove succeeds");
    assert_eq!(
        Err(OrderError::UnknownPosition),
        order.insert_after(only, 1),
        "insert_after a stale handle errors"
    );
    assert_eq!(
        Err(OrderError::UnknownPosition),
        order.insert_before(only, 1),
        "insert_before a stale handle errors"
    );
}

#[test]
fn foreign_handle_is_rejected()
{
    let mut one: OrderMaintenance<u64> = new_order();
    let mut two: OrderMaintenance<u64> = new_order();
    let foreign = one.push_back(0).expect("push_back succeeds");
    let native = two.push_back(1).expect("push_back succeeds");
    assert_eq!(None, two.get(foreign), "a foreign handle does not resolve");
    assert_eq!(
        None,
        two.cmp(foreign, native),
        "comparing across structures is None"
    );
    assert_eq!(
        None,
        two.cmp(native, foreign),
        "comparing across structures is None in either argument"
    );
    assert_eq!(
        Err(OrderError::UnknownPosition),
        two.insert_after(foreign, 2),
        "inserting at a foreign handle errors"
    );
    assert_eq!(
        Ok(None),
        two.remove(foreign),
        "removing a foreign handle is Ok(None)"
    );
    assert!(
        !bool::from(two.contains(foreign)),
        "a foreign handle is not contained"
    );
}

#[test]
fn interval_containment()
{
    // Pre/post-order points for a tree: outer `[a_lo, a_hi]` wraps inner
    // `[b_lo, b_hi]`; a third point `c` sits after both.
    let mut order: OrderMaintenance<&'static str> = new_order();
    let a_lo = order.push_back("a_lo").expect("push_back succeeds");
    let b_lo = order.push_back("b_lo").expect("push_back succeeds");
    let b_hi = order.push_back("b_hi").expect("push_back succeeds");
    let a_hi = order.push_back("a_hi").expect("push_back succeeds");
    let c = order.push_back("c").expect("push_back succeeds");
    let outer = Interval::new(a_lo, a_hi);
    let inner = Interval::new(b_lo, b_hi);
    let disjoint = Interval::new(c, c);
    assert_eq!(
        Some(true),
        order.interval_contains(outer, inner).map(bool::from),
        "outer contains inner"
    );
    assert_eq!(
        Some(false),
        order.interval_contains(inner, outer).map(bool::from),
        "inner does not contain outer"
    );
    assert_eq!(
        Some(false),
        order.interval_contains(outer, disjoint).map(bool::from),
        "outer does not contain a later point"
    );
    assert_eq!(
        Some(false),
        order.interval_contains(disjoint, outer).map(bool::from),
        "a later point does not contain outer"
    );
    assert_eq!(
        Some(true),
        order.interval_contains(outer, outer).map(bool::from),
        "an interval contains itself"
    );
    assert_eq!(
        Some(true),
        order
            .interval_contains(outer, Interval::new(a_lo, b_hi))
            .map(bool::from),
        "a shared lower endpoint still counts as containment"
    );
    assert_eq!(
        Some(true),
        order
            .interval_contains(outer, Interval::new(b_lo, a_hi))
            .map(bool::from),
        "a shared upper endpoint still counts as containment"
    );
}

#[test]
fn interval_with_stale_endpoint_is_none()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let lo = order.push_back(0).expect("push_back succeeds");
    let hi = order.push_back(1).expect("push_back succeeds");
    let gone = order.push_back(2).expect("push_back succeeds");
    order.remove(gone).expect("remove succeeds");
    let live = Interval::new(lo, hi);
    let stale = Interval::new(gone, gone);
    assert_eq!(
        None,
        order.interval_contains(live, stale),
        "a stale inner endpoint yields None"
    );
    assert_eq!(
        None,
        order.interval_contains(stale, live),
        "a stale outer endpoint yields None"
    );
}

#[test]
fn comparison_is_reflexive_and_total()
{
    let mut order: OrderMaintenance<u64> = new_order();
    let first = order.push_back(0).expect("push_back succeeds");
    let second = order.push_back(1).expect("push_back succeeds");
    assert_eq!(
        Some(Ordering::Equal),
        order.cmp(first, first),
        "an element equals itself"
    );
    assert_eq!(
        Some(Ordering::Less),
        order.cmp(first, second),
        "earlier is Less"
    );
    assert_eq!(
        Some(Ordering::Greater),
        order.cmp(second, first),
        "later is Greater"
    );
}

#[test]
fn error_display_is_distinct_per_variant()
{
    use alloc::string::String;

    let messages: [String; 4] = [
        alloc::string::ToString::to_string(&OrderError::UnknownPosition),
        alloc::string::ToString::to_string(&OrderError::StructureIdExhausted),
        alloc::string::ToString::to_string(&OrderError::CapacityExhausted),
        alloc::string::ToString::to_string(&OrderError::Inconsistent),
    ];
    for (left_rank, left) in messages.iter().enumerate() {
        for right in messages.iter().skip(left_rank.saturating_add(1)) {
            assert_ne!(left, right, "distinct failures remain distinguishable");
        }
    }
}

/// The sequence model over the narrow widths: every generated edit is applied
/// to a structure whose groups are the narrowest and whose circle has `2^16`
/// labels, so splits, rebalances and walks past the last group all occur,
/// and to a `Vec` of the payloads; the two agree after every edit and the
/// structure's invariant holds.
mod model
{
    use alloc::collections::VecDeque;

    use proptest::prelude::ProptestConfig;
    use proptest::prelude::Strategy;
    use proptest::prelude::any;
    use proptest::prop_oneof;
    use proptest::proptest;

    use super::*;

    /// One edit, its rank reduced modulo the length when applied.
    #[derive(Clone, Copy, Debug)]
    enum Edit
    {
        /// Append a value.
        Back(u64),
        /// Prepend a value.
        Front(u64),
        /// Insert a value after the element at a rank.
        After(usize, u64),
        /// Insert a value before the element at a rank.
        Before(usize, u64),
        /// Remove the element at a rank.
        Remove(usize),
    }

    /// The edit alphabet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each of the five edits; the insertions behind a rank
    ///   are weighted so groups fill and split.
    /// - provides: the edits the model replays.
    /// - panics: none.
    /// - executable: none — the attribute backend cannot instrument the opaque
    ///   returned strategy.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replay's own assertions observe every variant it
    ///   is handed.
    /// - witness: `order::tests::model::narrow_structures_match_a_sequence_model`
    fn edit() -> impl Strategy<Value = Edit>
    {
        prop_oneof![
            2 => any::<u64>().prop_map(Edit::Back),
            1 => any::<u64>().prop_map(Edit::Front),
            4 => (any::<usize>(), any::<u64>()).prop_map(|(rank, value)| Edit::After(rank, value)),
            2 => (any::<usize>(), any::<u64>()).prop_map(|(rank, value)| Edit::Before(rank, value)),
            2 => any::<usize>().prop_map(Edit::Remove),
        ]
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        /// A generated edit sequence replayed against the structure and a
        /// `Vec`, which agree after every edit.
        #[test]
        fn narrow_structures_match_a_sequence_model(edits in proptest::collection::vec(edit(), 0 .. 400))
        {
            let mut order: OrderMaintenance<u64> = narrow_order(TopWidth(16), GroupWidth::MIN);
            let mut values: VecDeque<u64> = VecDeque::new();
            let mut handles: VecDeque<Pos> = VecDeque::new();
            for edit in edits {
                match edit {
                    Edit::Back(value) => {
                        handles.push_back(order.push_back(value).expect("an append fits"));
                        values.push_back(value);
                    },
                    Edit::Front(value) => {
                        handles.push_front(order.push_front(value).expect("a prepend fits"));
                        values.push_front(value);
                    },
                    Edit::After(rank, value) | Edit::Before(rank, value) => {
                        let Some(at) = rank.checked_rem(handles.len()) else { continue };
                        let anchor = *handles.get(at).expect("a drawn handle");
                        let (inserted, place) = if matches!(edit, Edit::After(..)) {
                            (order.insert_after(anchor, value), at.saturating_add(1))
                        } else {
                            (order.insert_before(anchor, value), at)
                        };
                        handles.insert(place, inserted.expect("an insertion fits"));
                        values.insert(place, value);
                    },
                    Edit::Remove(rank) => {
                        let Some(at) = rank.checked_rem(handles.len()) else { continue };
                        let handle = handles.remove(at).expect("a drawn handle");
                        let removed = order.remove(handle).expect("a removal");
                        proptest::prop_assert_eq!(removed, values.remove(at));
                    },
                }
                assert_invariant(&order);
                proptest::prop_assert_eq!(&values, &ordered(&order));
                proptest::prop_assert_eq!(&handles, &positions(&order));
            }
            assert_cmp_consistent(&order);
        }
    }
}
