//! The driver's fork: where a staged program's jobs run.
//!
//! The checker names no thread. A program check hands its jobs — one per
//! source, per certificate, per family — to a [`Fork`] the driver supplies,
//! and the driver owns the threads, their number and their pool, as a walk's
//! width is the driver's. [`Serial`] runs every job on the calling thread in
//! order, and is the reference a forked check equals.
//!
//! # Jobs in dependence order
//!
//! [`Fork::schedule`] runs one job per item, each once the jobs it depends on
//! have returned, and folds every item into state the caller holds, on the
//! calling thread and in slice order, as soon as the item's own job has
//! returned. A check whose next step needs one item at a time folds behind its
//! jobs instead of after all of them: the staged check merges each source's
//! segment while later sources are still normalizing. [`Dependences`] names
//! the edges, each from an earlier item to a later one, so slice order is
//! always a valid schedule and the serial one.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

/// Runs a program check's jobs on the workers the driver provides.
///
/// # Specification
/// - provides: the three shapes a program check forks by: one job per item,
///   each worker carrying state of its own; two independent halves run beside
///   each other; and jobs in dependence order, each item folded on the calling
///   thread in slice order.
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

    /// Run `job` once on every item, each once the jobs of the items it
    /// depends on have returned, and `fold` on every item on the calling
    /// thread, in slice order.
    ///
    /// # Specification
    /// - requires: nothing; an edge of `after` naming an item past the slice
    ///   is ignored.
    /// - ensures: on return `job` has run exactly once on every item, after
    ///   the job of every item `after` names before it has returned, from a
    ///   state handed as [`Fork::each`] hands it; `fold` has run exactly once
    ///   on every item, on the calling thread, in slice order, each after the
    ///   item's own job has returned.
    /// - panics: a panic of `start`, `job` or `fold`, wherever it ran.
    /// - executable: none — when each job and each fold ran is a property of
    ///   the implementation's schedule, which a postcondition over the items
    ///   cannot observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each implementation's witness stamps every job's
    ///   start and end and every fold, over graphs with no edge, a chain and a
    ///   scattered fan.
    /// - declaration-only: the obligation is each implementation's schedule;
    ///   the trait has no body to witness.
    fn schedule<Item, State, Start, Job, Fold>(
        &self,
        items: &mut [Item],
        after: &Dependences,
        start: Start,
        job: Job,
        fold: Fold,
    ) where
        Item: Send,
        State: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
        Fold: FnMut(&mut Item);
}

/// The jobs each job of a [`Fork::schedule`] waits on, by slice position.
///
/// # Specification
/// - provides: edges `(before, after)`, each from an earlier item to a later
///   one, sorted and without repeats; the job of the item at `after` waits on
///   the job of the item at `before`. The default has no edge.
/// - panics: none.
/// - executable: none — [`Dependences::new`] states the order it keeps.
///
/// # Adequacy
/// - hypothesis: L3 — an edge to an earlier item, or to the item itself, is
///   refused, and repeated edges are kept once in order.
/// - witness: `fork::tests::dependences_keep_forward_edges_once_in_order`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Dependences
{
    /// Every edge, `(before, after)`, sorted and without repeats.
    edges: Vec<(usize, usize)>,
}

impl Dependences
{
    /// The dependences `edges` names, each `(before, after)`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the edges, sorted by their earlier item and then their later
    ///   one, each kept once.
    /// - fails: [`Backward`] for the first edge whose waiting item does not
    ///   come after the item it waits on.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`Backward`] edge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Dependences`].
    /// - witness: `fork::tests::dependences_keep_forward_edges_once_in_order`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|dependences| {
        dependences.edges.iter().all(|&(before, after)| before < after)
            && dependences.edges.iter().zip(dependences.edges.iter().skip(1)).all(|(first, second)| first < second)
    }))]
    #[inline]
    pub fn new(edges: impl IntoIterator<Item = (usize, usize)>) -> Result<Self, Backward>
    {
        let mut kept = Vec::new();
        for (before, after) in edges {
            if before >= after {
                return Err(Backward { before, after });
            }
            kept.push((before, after));
        }
        kept.sort_unstable();
        kept.dedup();
        Ok(Self { edges: kept })
    }

    /// Every edge, `(before, after)`, sorted by its earlier item and then its
    /// later one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn edges(&self) -> &[(usize, usize)]
    {
        &self.edges
    }
}

/// An edge whose waiting item does not come after the item it waits on, so
/// slice order would not be a schedule.
///
/// # Specification
/// - provides: the edge as given.
/// - panics: none.
/// - executable: none — a plain record of [`Dependences::new`]'s refusal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Backward
{
    /// The item waited on.
    pub before: usize,
    /// The item waiting, at or before `before`.
    pub after: usize,
}

impl fmt::Display for Backward
{
    /// Names the edge.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            formatter,
            "item {} cannot wait on item {}, which does not come before it",
            self.after, self.before
        )
    }
}

impl core::error::Error for Backward
{
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

    /// Run every item's job and then its fold, in slice order, from one
    /// state.
    ///
    /// # Specification
    /// - ensures: `start` runs once when there is an item and never otherwise;
    ///   each item's job runs, then its fold, before the next item's job.
    ///   Every edge runs from an earlier item to a later one, so slice order
    ///   waits on every edge.
    /// - panics: a panic of `start`, `job` or `fold`.
    /// - executable: none — call order is the observation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no item, one item and several items under a chain,
    ///   each stamping its job and its fold, distinguish a state made for
    ///   nothing, a fold before its job and a reordered item.
    /// - witness: `fork::tests::serial_runs_each_job_then_its_fold_in_order`
    #[inline]
    fn schedule<Item, State, Start, Job, Fold>(
        &self,
        items: &mut [Item],
        _after: &Dependences,
        start: Start,
        job: Job,
        mut fold: Fold,
    ) where
        Item: Send,
        State: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
        Fold: FnMut(&mut Item),
    {
        if items.is_empty() {
            return;
        }
        let mut state = start();
        for item in items {
            job(&mut state, item);
            fold(item);
        }
    }
}

#[cfg(test)]
mod tests;
