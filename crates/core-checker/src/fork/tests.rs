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
