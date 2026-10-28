//! The fork: where a check's independent jobs run.
//!
//! A `no_std` crate names no thread. A check hands its independent jobs to a
//! [`Fork`] that the driver supplies. The jobs are one per source, per
//! certificate or per family. The driver owns the threads, their number and
//! their pool, as it owns a walk's width. [`Serial`] runs every job on the
//! calling thread in order. It is the reference that a forked check equals.
//!
//! The trait lives in a crate of its own. So a consumer at any layer from the
//! core upward takes it without a dependency on the checker.
//!
//! The `pool_only_threads` lint of the policy wall holds the rule. A call that
//! starts a thread or a pool outside the driver's pool is refused. A site that
//! owns its thread states why in an expectation at the site.
//!
//! # References
//!
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-sax): a cut's reader waits for its writer, so a join's right
//!   half may wait for its left half, and never the reverse.

#![no_std]

#[cfg(test)]
extern crate alloc;

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

    /// Run two halves, possibly at once, and return both results. The right
    /// half may wait for the left one, and never the reverse.
    ///
    /// # Specification
    /// - requires: the left half never waits for the right half.
    /// - ensures: each half has run exactly once to completion; the pair is
    ///   their results, in argument order. The left half begins before the join
    ///   waits for the right half to end, so a right half that waits for the
    ///   left one ends.
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
/// - hypothesis: L3 — no item, one item and several items, and a join that
///   records which half ran first, distinguish a state made for nothing, a
///   state per item, a skipped or reordered item and swapped halves.
/// - witness: `tests::serial_runs_each_item_in_order_from_one_state`
/// - witness: `tests::serial_runs_the_left_half_before_the_right`
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
    /// - witness: `tests::serial_runs_each_item_in_order_from_one_state`
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
mod tests;
