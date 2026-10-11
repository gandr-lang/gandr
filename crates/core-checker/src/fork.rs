//! The driver's fork: where a staged program's independent jobs run.
//!
//! The checker names no thread. A program check hands its independent jobs —
//! one per source, per certificate, per family — to a [`Fork`] the driver
//! supplies, and the driver owns the threads, their number and their pool, as
//! a walk's width is the driver's. [`Serial`] runs every job on the calling
//! thread in order, and is the reference a forked check equals.

/// Runs independent jobs on the workers the driver provides.
///
/// # Specification
/// - provides: the two shapes a program check forks by: one job per item, each
///   worker carrying state of its own, and two independent halves run beside
///   each other.
/// - panics: none of its own; a job's panic is the job's.
/// - executable: none — the trait states obligations its implementations carry;
///   [`Serial`] carries them on the calling thread.
pub trait Fork: Sync
{
    /// Run `job` once on every item, each on a worker whose state `start`
    /// made.
    ///
    /// # Specification
    /// - requires: nothing; items may run in any order, on any worker, at once.
    /// - ensures: on return `job` has run exactly once on every item, and every
    ///   state it was handed was made by `start` on the worker running it and
    ///   was never handed to two jobs at once.
    /// - panics: a panic of `start` or `job`, wherever it ran.
    /// - executable: none — "exactly once" and the state's ownership are
    ///   properties of the implementation's schedule, which a postcondition
    ///   over the items cannot observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each implementation's witness counts every item's
    ///   visits and the states made.
    /// - declaration-only: the obligation is each implementation's schedule;
    ///   the trait has no body to witness.
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync;

    /// Run two independent halves, possibly at once, and return both
    /// results.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each half has run exactly once to completion; the pair is
    ///   their results, in argument order.
    /// - panics: a panic of either half.
    /// - executable: none — the schedule is the implementation's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the program check's width witnesses compare both
    ///   halves' results with the serial reference's.
    /// - declaration-only: the obligation is each implementation's schedule;
    ///   the trait has no body to witness.
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send;
}

/// Every job on the calling thread, in order: the serial reference.
///
/// # Specification
/// - provides: a [`Fork`] that runs items in slice order from one state made
///   only when there is an item, and the left half before the right.
/// - panics: none.
/// - executable: none — a unit marker; its methods carry the behavior.
///
/// # Adequacy
/// - hypothesis: L2 — a program checked at the serial width is the reference
///   every forked width is compared with, report for report and term for term.
/// - witness: `staging::tests::every_width_checks_the_serial_program`
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Serial;

impl Fork for Serial
{
    /// Run `job` on every item in slice order, from one state.
    ///
    /// # Specification
    /// - ensures: `start` runs once when there is an item and never otherwise;
    ///   `job` runs on each item in order.
    /// - panics: a panic of `start` or `job`.
    /// - executable: none — call order is the observation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no item, one item and several items, each counting
    ///   the states made and the visits in order, distinguish a state made for
    ///   nothing, a state per item, a skipped item and a reordered one.
    /// - witness: `fork::tests::serial_runs_each_item_in_order_from_one_state`
    #[inline]
    fn each<Item, State, Start, Job>(
        &self,
        items: &mut [Item],
        start: Start,
        job: Job,
    ) where
        Item: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
    {
        if items.is_empty() {
            return;
        }
        let mut state = start();
        for item in items {
            job(&mut state, item);
        }
    }

    /// Run the left half, then the right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn join<Left, Right, LeftOutput, RightOutput>(
        &self,
        left: Left,
        right: Right,
    ) -> (LeftOutput, RightOutput)
    where
        Left: FnOnce() -> LeftOutput + Send,
        Right: FnOnce() -> RightOutput + Send,
        LeftOutput: Send,
        RightOutput: Send,
    {
        let left = left();
        let right = right();
        (left, right)
    }
}

#[cfg(test)]
mod tests
{
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
}
