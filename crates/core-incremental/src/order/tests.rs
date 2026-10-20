use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;
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
/// - requires: each name list is distinct, and the order can admit the finite
///   fixture.
/// - ensures: returns the seeded and edited handles and the exact splice
///   census, with the order in the edited state.
/// - panics: when seeding or splicing refuses the fixture.
///
/// # Adequacy
/// - hypothesis: L3 — insertion, deletion, swap, move, empty and unchanged
///   fixtures distinguish incorrect state assembly by exact handle and census
///   observations. These inputs do not induce underlying capacity refusals.
/// - witness: `order::tests::a_handle_survives_an_insertion_before_its_item`
/// - witness: `order::tests::a_deleted_items_handle_goes_stale`
/// - witness: `order::tests::handles_compare_in_the_edited_order`
/// - witness: `order::tests::a_moved_item_costs_only_its_own_handle`
/// - witness: `order::tests::empty_and_unchanged_splices_have_exact_censuses`
#[spec(ensures: |ret| ret.1.len() == base.len()
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
    let (order, before, after, census) = spliced(&[Name("a"), Name("b")], &[Name("b"), Name("a")]);
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
        let kept: std::collections::HashSet<_> = after.iter().collect();
        for old in before {
            if !kept.contains(&old) {
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
                    Maybe::Present(position) => {
                        ascending &= previous.is_none_or(|earlier| earlier < position);
                        previous = Some(position);
                        length = length.saturating_add(1);
                    },
                    Maybe::Absent(_) => ascending = false,
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
