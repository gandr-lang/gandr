//! The combinators this crate's specification clauses read the melder's head
//! caches through.
//!
//! The melder keeps three ascending index caches over its slope (the open
//! frontiers, the operators and every form tile), so a head query reads a
//! cache top instead of scanning the slope. A clause that re-derives a cache
//! from the whole slope costs a slope scan at every push, which is the cost
//! the caches exist to remove. [`indexed_from`] checks a cache against the
//! slope only from the lowest position a mutation touched, and it states a
//! `# Clause cost` bound. A mutation's clause therefore reads what the
//! mutation wrote, and the entries below it rest on the clause of the
//! mutation that wrote them. The generic sequence claims live in
//! `gandr-theory-spec-combinators`.

use anodized::spec;
use gandr_theory_spec_combinators::Holds;
use gandr_theory_spec_combinators::Mark;

/// Whether the entries of `index` at or above `floor` are, in ascending
/// order, exactly the positions at or above `floor` of the items `select`
/// picks.
///
/// # Specification
/// - requires: `index` ascends, so its entries at or above `floor` form a
///   suffix of it.
/// - ensures: holds exactly when the entries of `index` at or above `floor`
///   strictly ascend, each names an item of `items` that `select` picks, and
///   they are as many as the items at or above `floor` that `select` picks.
/// - provides: the check a mutation of an index cache makes from the lowest
///   position it touched, rather than over the whole sequence.
/// - panics: none.
///
/// # Clause cost
/// - bound: one binary search of `index` for `floor`, then one read of each
///   item at or above `floor`; checking its own clause adds the entries of
///   `index` at or above `floor` and a second read of each of those items.
///
/// # Adequacy
/// - hypothesis: L3 — over items with a selected and an unselected kind, the
///   exact positions hold from the base, from a middle floor and from past the
///   end; a missing, extra, duplicated or out-of-range entry fails; a wrong
///   entry below the floor still holds, so the check reads only above the
///   floor. The bound is a property over every depth beneath the floor up to
///   the witness's bound: `select` runs once per item above the floor, three
///   times in an enforcing build.
/// - witness: `spec::tests::indexed_from_holds_for_exactly_the_selected_positions`
/// - witness: `spec::tests::indexed_from_reads_only_above_the_floor`
#[spec(ensures: |ret| bool::from(ret) == {
    let floor = <usize as From<Mark>>::from(floor);
    let listed = index.get(index.partition_point(|&position| usize::from(position) < floor) ..).unwrap_or_default();
    listed.first().is_none_or(|&position| usize::from(position) >= floor)
        && listed.iter().zip(listed.iter().skip(1)).all(|(&lower, &higher)| usize::from(lower) < usize::from(higher))
        && listed.iter().all(|&position| items.get(usize::from(position)).is_some_and(|item| bool::from(select(item))))
        && listed.len() == items.get(floor ..).unwrap_or_default().iter().filter(|item| bool::from(select(item))).count()
})]
#[inline]
#[must_use]
pub fn indexed_from<Item, Position, Select>(
    items: &[Item],
    index: &[Position],
    floor: Mark,
    select: Select,
) -> Holds
where
    Position: Copy,
    usize: From<Position>,
    Select: Fn(&Item) -> Holds,
{
    let floor = <usize as From<Mark>>::from(floor);
    let listed = index
        .get(index.partition_point(|&position| usize::from(position) < floor) ..)
        .unwrap_or_default();
    let selected = items
        .get(floor ..)
        .unwrap_or_default()
        .iter()
        .enumerate()
        .filter(|&(_, item)| bool::from(select(item)))
        .map(|(offset, _)| floor.saturating_add(offset));
    Holds::from(selected.eq(listed.iter().map(|&position| usize::from(position))))
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use core::cell::Cell;

    use gandr_theory_spec_combinators::Holds;
    use gandr_theory_spec_combinators::Mark;

    use super::indexed_from;

    /// The deepest run of items beneath the floor the bound witness builds.
    const DEEPEST: usize = 256;

    /// How many times `select` reads each item above the floor: once, and
    /// twice more for the combinator's own clause in an enforcing build.
    const READS: usize = if cfg!(anodized_panic) { 3 } else { 1 };

    #[test]
    fn indexed_from_holds_for_exactly_the_selected_positions()
    {
        let items = [false, true, false, true, true];
        let holds = |index: &[usize], floor: usize| {
            bool::from(indexed_from(&items, index, Mark::from(floor), |&item| {
                Holds::from(item)
            }))
        };
        assert!(holds(&[1, 3, 4], 0));
        assert!(holds(&[1, 3, 4], 2));
        assert!(holds(&[1, 3, 4], 5));
        assert!(holds(&[1, 3, 4], 9));
        assert!(!holds(&[1, 4], 0));
        assert!(!holds(&[1, 2, 3, 4], 0));
        assert!(!holds(&[1, 3, 3, 4], 0));
        assert!(!holds(&[1, 3, 4, 5], 0));
        assert!(!holds(&[1, 4], 2));
        assert!(!holds(&[1, 3, 4, 9], 7));
        assert!(holds(&[0, 3, 4], 2));
        assert!(!holds(&[0, 3, 4], 0));
    }

    #[test]
    fn indexed_from_reads_only_above_the_floor()
    {
        let tally = Cell::new(0_usize);
        let select = |&item: &bool| {
            tally.set(tally.get().saturating_add(1));
            Holds::from(item)
        };
        let above = [true, false, true];
        let mut items = Vec::new();
        let mut index = Vec::new();
        for depth in 0 ..= DEEPEST {
            let mut whole = items.clone();
            whole.extend(above);
            let mut cached = index.clone();
            cached.extend([depth, depth.saturating_add(2)]);
            tally.set(0);
            assert!(bool::from(indexed_from(
                &whole,
                &cached,
                Mark::from(depth),
                select
            )));
            assert!(tally.get() <= READS.saturating_mul(above.len()));
            tally.set(0);
            assert!(bool::from(indexed_from(
                &whole,
                &cached,
                Mark::from(whole.len()),
                select
            )));
            assert_eq!(tally.get(), 0);
            if depth.is_multiple_of(2) {
                index.push(depth);
                items.push(true);
            }
            else {
                items.push(false);
            }
        }
    }
}
