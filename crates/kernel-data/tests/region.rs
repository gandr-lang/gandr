//! The region: its values under a budget, and each of its three crossings.

use gandr_kernel_data::Budget;
use gandr_kernel_data::Id;
use gandr_kernel_data::Key;
use gandr_kernel_data::scoped;

/// The bytes of one first bucket of `u64` values with their cells, and a
/// little more: room for one bucket and not for the second.
const ONE_BUCKET: usize = 1_536;

/// A budget that holds every value a test mints: one mebibyte.
const LARGE: usize = 0x10_0000;

/// Values minted across two buckets read back at their ids, and the value
/// past a budget that holds one bucket is refused.
#[test]
fn a_region_reads_each_value_at_its_id_and_refuses_past_its_budget()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let ids: Vec<Id<'_>> = (0_u64 .. 100_u64)
            .map(|value| region.mint(&mut mint, value))
            .collect::<Result<_, _>>()
            .expect("the budget holds two buckets");
        ids.iter()
            .map(|&id| region.get(id).copied())
            .collect::<Option<Vec<u64>>>()
    });
    assert_eq!(
        read,
        Some((0_u64 .. 100_u64).collect()),
        "each id reads the value minted at it"
    );
    let refused = scoped(Budget::from(ONE_BUCKET), |region, mut mint| {
        (0_u64 .. 64_u64).try_for_each(|value| region.mint(&mut mint, value).map(drop))?;
        region.mint(&mut mint, 64_u64).map(drop)
    });
    assert!(
        refused.is_err(),
        "the 65th value needs a second bucket past the budget"
    );
}

/// A child reads a value of its parent through `adopt`, and its own first id
/// stands apart from it.
#[test]
fn a_child_reads_a_value_of_its_parent_through_adopt()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let parent = region.mint(&mut mint, 7_u64).expect("the budget holds it");
        region
            .fork::<(), _>(&mut mint, |child, mut own, adopt| {
                let adopted = adopt.adopt(parent);
                let first = child.mint(&mut own, 9_u64).ok()?;
                (adopted != first
                    && child.get(adopted) == Some(&7_u64)
                    && child.get(first) == Some(&9_u64))
                .then_some(())
            })
            .expect("the join holds no suffix past the budget")
    });
    assert_eq!(
        read,
        Some(()),
        "the child reads the parent's value and its own"
    );
}

/// A child that agrees folds its values into the parent at the offsets it
/// minted them at; the parent reads them at the ids the join gives, and its
/// next id follows them.
#[test]
fn a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let before = region.mint(&mut mint, 1_u64).expect("the budget holds it");
        let joined = region
            .fork::<Option<Id<'static>>, _>(&mut mint, |child, mut own, _adopt| {
                let _second = child.mint(&mut own, 2_u64).ok()?;
                Some(Some(child.mint(&mut own, 3_u64).ok()?))
            })
            .expect("the budget holds the suffix")
            .flatten()
            .expect("the child agrees");
        let after = region.mint(&mut mint, 4_u64).expect("the budget holds it");
        (
            u32::from(before.key()),
            u32::from(joined.key()),
            region.get(joined).copied(),
            u32::from(after.key()),
        )
    });
    assert_eq!(
        read,
        (0_u32, 2_u32, Some(3_u64), 3_u32),
        "the suffix lands at offsets 1 and 2, and the parent goes on at 3"
    );
}

/// A child that disagrees drops its suffix whole: the parent's next id stands
/// at the mark, and no value of the child reads in the parent.
#[test]
fn a_fork_that_disagrees_drops_its_suffix_whole()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let _before = region.mint(&mut mint, 1_u64).expect("the budget holds it");
        let joined = region
            .fork::<(), _>(&mut mint, |child, mut own, _adopt| {
                let _dropped = child.mint(&mut own, 2_u64).ok()?;
                None
            })
            .expect("a dropped suffix draws nothing");
        let after = region.mint(&mut mint, 5_u64).expect("the budget holds it");
        (joined, u32::from(after.key()), region.get(after).copied())
    });
    assert_eq!(
        read,
        (None, 1_u32, Some(5_u64)),
        "the parent's next value takes the mark, offset 1"
    );
}

/// A key of each of two values seats back as its own id, and a key past the
/// region is refused.
#[test]
fn a_key_seats_back_in_its_region_and_a_key_past_it_is_refused()
{
    let read = scoped(Budget::from(LARGE), |region, mut mint| {
        let first = region.mint(&mut mint, 10_u64).expect("the budget holds it");
        let second = region.mint(&mut mint, 20_u64).expect("the budget holds it");
        (
            region.seat(first.key()) == Some(first),
            region.seat(second.key()) == Some(second),
            region.seat(Key::from(2_u32)).is_none(),
        )
    });
    assert_eq!(
        read,
        (true, true, true),
        "each key seats back, and the key past the region is refused"
    );
}
