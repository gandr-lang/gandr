use alloc::vec::Vec;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use super::*;

/// An item: its slice position and the order of each visit it received.
#[derive(Debug)]
struct Visited
{
    /// The item's position in the slice.
    position: usize,
    /// The running count at each visit.
    visits: Vec<usize>,
}

#[test]
fn serial_runs_each_item_in_order_from_one_state()
{
    for count in [0_usize, 1, 5] {
        let made = AtomicUsize::new(0);
        let mut items: Vec<Visited> = (0 .. count)
            .map(|position| Visited {
                position,
                visits: Vec::new(),
            })
            .collect();
        Serial.each(
            &mut items,
            || {
                made.fetch_add(1, Ordering::Relaxed);
                0_usize
            },
            |seen, item| {
                item.visits.push(*seen);
                *seen = seen.checked_add(1).unwrap();
            },
        );
        assert_eq!(
            made.load(Ordering::Relaxed),
            usize::from(count > 0),
            "states made for {count} items"
        );
        for item in &items {
            assert_eq!(item.visits, [item.position], "one visit, in slice order");
        }
    }
}

/// An item of a schedule: the running count when its job ran and when it was
/// folded.
#[derive(Debug, Default)]
struct Stamped
{
    /// The count at each run of the item's job.
    jobs: Vec<usize>,
    /// The count at each fold of the item.
    folds: Vec<usize>,
}

#[test]
fn serial_runs_each_job_then_its_fold_in_order()
{
    for count in [0_usize, 1, 5] {
        let made = AtomicUsize::new(0);
        let clock = AtomicUsize::new(0);
        let tick = || clock.fetch_add(1, Ordering::Relaxed);
        let mut items: Vec<Stamped> = (0 .. count).map(|_| Stamped::default()).collect();
        let chain = Dependences::new((1 .. count).map(|after| (after.checked_sub(1).unwrap(), after))).unwrap();
        Serial.schedule(
            &mut items,
            &chain,
            || {
                made.fetch_add(1, Ordering::Relaxed);
            },
            |_state, item| item.jobs.push(tick()),
            |item| item.folds.push(tick()),
        );
        assert_eq!(
            made.load(Ordering::Relaxed),
            usize::from(count > 0),
            "states made for {count} items"
        );
        for (position, item) in items.iter().enumerate() {
            let job = position.checked_mul(2).unwrap();
            assert_eq!(item.jobs, [job], "item {position}'s job, once, in order");
            assert_eq!(
                item.folds,
                [job.checked_add(1).unwrap()],
                "item {position}'s fold, once, right after its job"
            );
        }
    }
}

#[test]
fn dependences_keep_forward_edges_once_in_order()
{
    let kept = Dependences::new([(2, 5), (0, 1), (2, 5), (0, 3)]).unwrap();
    assert_eq!(kept.edges(), [(0, 1), (0, 3), (2, 5)]);
    assert_eq!(Dependences::new([]).unwrap(), Dependences::default());
    assert_eq!(
        Dependences::new([(0, 1), (3, 3)]),
        Err(Backward {
            before: 3,
            after: 3
        }),
        "an item cannot wait on itself"
    );
    assert_eq!(
        Dependences::new([(4, 2)]),
        Err(Backward {
            before: 4,
            after: 2
        }),
        "an item cannot wait on a later one"
    );
}
