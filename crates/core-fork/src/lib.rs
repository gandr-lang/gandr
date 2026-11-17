//! The fork: where a check's independent jobs run.
//!
//! A `no_std` crate names no thread. A check hands its independent jobs to a
//! [`Fork`] that the driver supplies. The jobs are one per source, per
//! certificate or per family. The driver owns the threads, their number and
//! their pool, as it owns a walk's width. [`Serial`] runs every job on the
//! calling thread in order. It is the reference that a forked check equals.
//! The trait lives in a crate of its own, so any layer takes it without the
//! checker.
//!
//! A job whose start and whose wait are apart runs in a scope. [`Fork::scope`]
//! opens one, and its body spawns through a [`Spawn`]. A wait runs a job that
//! has not started on the waiting thread. While a started job runs elsewhere,
//! the waiting worker runs other pending work, so a wait never holds a worker
//! idle. Each job is a [`Scoped`] computation, generic over the spawner, so a
//! job spawns its own jobs through whichever spawner its worker holds.
//!
//! The `pool_only_threads` lint of the policy wall holds the rule. A call that
//! starts a thread or a pool outside the driver's pool is refused. A site that
//! owns its thread states why in an expectation at the site.
//!
//! Jobs that read each other's results go to [`Fork::schedule`], in the order
//! that [`Dependences`] names.
//!
//! With the `instrument` feature, the `activity` module records which task
//! each worker runs, and when. Each worker writes into a lock-free ring of its
//! own, and the hub folds the rings. Without the feature, the crate carries
//! none of the module's bytes.
//!
//! # References
//!
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-sax): a cut's reader waits for its writer, so a join's right
//!   half may wait for its left half, and never the reverse. A spawned job's
//!   wait is that reader's wait, which runs or helps its writer.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — newest: the checks of one
//!   environment run over the dependence graph of their supports, and one
//!   committer folds them. [`Fork::schedule`] is the seam that this schedule
//!   runs on.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use core::fmt;
use core::time::Duration;

use anodized::spec;
use quenchant_shape::shape::Maybe;

#[cfg(feature = "instrument")]
pub mod activity;

/// Runs independent jobs on the workers the driver provides.
///
/// # Specification
/// - provides: the four shapes a program forks by: one job per item, each
///   worker carrying state of its own; two independent halves run beside each
///   other; a scope whose jobs start apart from their waits; and jobs in
///   dependence order, each released in slice order and committed as it
///   returns, both on the calling thread.
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

    /// Run `body` in a scope, handing it a spawner whose jobs end before the
    /// scope does.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `body` runs once, and the call returns its result. Each job
    ///   that the scope spawned has ended, or its handle was dropped before the
    ///   job started and the job never runs.
    /// - provides: by default the serial spawner, which runs each job at its
    ///   wait on the waiting thread; a fork over threads overrides it.
    /// - panics: a panic of `body` or of a spawned job.
    /// - executable: none — the end of the spawned jobs is the schedule's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested spawn tree summed in the serial scope equals
    ///   the sum of its leaves, and a job whose handle was dropped never runs.
    /// - witness: `tests::a_nested_serial_spawn_sums_the_leaves`
    /// - witness: `tests::serial_runs_a_spawned_job_at_its_wait`
    #[inline]
    fn scope<'scope, Body>(
        &self,
        body: Body,
    ) -> Body::Output
    where
        Body: Scoped<'scope> + Send,
        Body::Output: Send,
    {
        body.run(&Serial)
    }

    /// Release each item on the calling thread in slice order, run each job
    /// that a release gives on any worker, and commit each item on the
    /// calling thread as its job returns.
    ///
    /// # Specification
    /// - requires: an edge of `after` that names an item past the slice is
    ///   ignored.
    /// - ensures: on return `release` ran on every item, on the calling thread,
    ///   in slice order. An item's first release came after `commit` ran on
    ///   every item that `after` names before it. A release that answered
    ///   [`Releasing::Held`] while a job ran ran again once the item that it
    ///   names was committed, or, when it names none, once each job then
    ///   running was committed. `run` ran exactly once on each job that a
    ///   release gave. `commit` ran exactly once on every item, on the calling
    ///   thread: with its job's result once the job returned, or with the
    ///   result that its release gave.
    /// - provides: by default the serial schedule, which releases each item,
    ///   runs its job and commits it, in slice order. No job runs at a release,
    ///   so a held release commits the result that it holds. A fork over
    ///   threads overrides it.
    /// - panics: a panic of `release`, `run` or `commit`, wherever it ran.
    /// - executable: none — when each release, job and commit ran is a property
    ///   of the implementation's schedule, which a postcondition over the items
    ///   cannot observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no item, one item and several items under a chain,
    ///   each stamping its release, its job and its commit, distinguish a job
    ///   run before its release, a commit before its job and a reordered item.
    ///   A settled and a held release distinguish a job run for a result found
    ///   at the release. Each fork over threads stamps every release, job and
    ///   commit over graphs with no edge, a chain and a scattered fan.
    /// - witness: `tests::serial_releases_runs_and_commits_each_item_in_order`
    #[inline]
    fn schedule<Item, Job, Out, Release, Run, Commit>(
        &self,
        items: &mut [Item],
        _after: &Dependences,
        mut release: Release,
        run: Run,
        mut commit: Commit,
    ) where
        Job: Send,
        Out: Send,
        Release: FnMut(ItemIndex, &mut Item) -> Releasing<Job, Out>,
        Run: Fn(Job) -> Out + Sync,
        Commit: FnMut(ItemIndex, &mut Item, Out),
    {
        // Every edge goes from an earlier item to a later one, so slice order
        // commits each item that a release waits on, and the serial schedule
        // reads no edge.
        for (position, item) in items.iter_mut().enumerate() {
            let position = ItemIndex(position);
            let out = match release(position, item) {
                Releasing::Run(job) => run(job),
                Releasing::Settled(out) | Releasing::Held(out, ..) => out,
            };
            commit(position, item, out);
        }
    }
}

/// What the release of one item of [`Fork::schedule`] answers.
///
/// # Specification
/// - provides: a job to run, a result found at the release, or a release that
///   waits on a running job, with the result to commit when no job runs, the
///   kernel's reason for the wait and the item whose commit frees it.
/// - panics: none.
/// - executable: none — a type-level block: a plain record that the caller's
///   release makes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Releasing<Job, Out>
{
    /// A job to run on any worker. Its result goes to the item's commit.
    Run(Job),
    /// The result, found at the release with no job to run.
    Settled(Out),
    /// The release reads the commit of a job that runs, for the reason that
    /// the [`gandr_kernel_core::Hold`] names. When the hold names the item
    /// whose commit frees it, the schedule releases the item again after
    /// that commit. Otherwise it commits each running job first, then
    /// releases the item again. When no job runs, the schedule commits the
    /// result held here.
    Held(
        Out,
        gandr_kernel_core::Hold,
        Maybe<ItemIndex, gandr_kernel_core::held_on::Absent>,
    ),
}

/// The items that the release of each item of a [`Fork::schedule`] waits on,
/// by slice position, and the size of each item.
///
/// # Specification
/// - provides: edges `(before, after)`, each from an earlier item to a later
///   one, sorted and without repeats. The release of the item at `after` waits
///   on the commit of the item at `before`. And the size of each item by slice
///   position, which a schedule prices to tell what the item's job is expected
///   to cost. The default has no edge and sizes no item.
/// - panics: none.
/// - executable: none — a type-level block; [`Dependences::new`] states the
///   order that it keeps.
///
/// # Adequacy
/// - hypothesis: L3 — an edge to an earlier item, or to the item itself, is
///   refused, and repeated edges are kept once in order.
/// - witness: `tests::dependences_keep_forward_edges_once_in_order`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Dependences
{
    /// Every edge, sorted and without repeats.
    edges: Vec<Dependence>,
    /// The size of each item by slice position: the count of nodes that its
    /// job reads. Empty when no item is sized.
    sizes: Vec<ItemSize>,
}

impl Dependences
{
    /// The dependences that `edges` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the edges, sorted by their earlier item and then by their
    ///   later one, each kept once.
    /// - fails: [`Backward`] for the first edge whose waiting item does not
    ///   come after the item that it waits on.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the first [`Backward`] edge.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Dependences`].
    /// - witness: `tests::dependences_keep_forward_edges_once_in_order`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|dependences| {
        dependences.edges.iter().all(|edge| edge.before < edge.after)
            && dependences.edges.iter().zip(dependences.edges.iter().skip(1)).all(|(first, second)| first < second)
    }))]
    #[inline]
    pub fn new<Edges>(edges: Edges) -> Result<Self, Backward>
    where
        Edges: IntoIterator<Item = Dependence>,
    {
        let mut kept = Vec::new();
        for edge in edges {
            if edge.before >= edge.after {
                return Err(Backward { edge });
            }
            kept.push(edge);
        }
        kept.sort_unstable();
        kept.dedup();
        Ok(Self {
            edges: kept,
            sizes: Vec::new(),
        })
    }

    /// These dependences, with the item at each slice position of `sizes`
    /// sized as it gives.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sized(
        self,
        sizes: Vec<ItemSize>,
    ) -> Self
    {
        Self { sizes, ..self }
    }

    /// The size of each item by slice position; empty when no item is sized.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sizes(&self) -> &[ItemSize]
    {
        &self.sizes
    }

    /// Every edge, sorted by its earlier item and then by its later one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn edges(&self) -> &[Dependence]
    {
        &self.edges
    }

    /// What a schedule of jobs that cost `costs` can reach under these
    /// dependences, at any width.
    ///
    /// # Specification
    /// - requires: nothing; an edge that names an item past `costs` is ignored,
    ///   as [`Fork::schedule`] ignores it.
    /// - ensures: the serial cost is the sum of the costs. The critical path is
    ///   the longest chain of dependences, each item weighted by its cost: a
    ///   job starts when the jobs that it waits on return. The released bound
    ///   is the last commit of [`Fork::schedule`]. There each release comes in
    ///   slice order, once the items that it waits on are committed, and each
    ///   commit comes at its job's return. A release and a commit cost nothing.
    ///   The chain holds the items of the critical path in slice order, and its
    ///   costs sum to the critical path. The critical path is at most the
    ///   released bound, and the released bound is at most the serial cost.
    /// - provides: the bound that no width beats, the bound of the release in
    ///   slice order, and the chain that names the first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — jobs with no edge, a chain, an edge past the costs
    ///   and a cheap dependence behind a costly item distinguish a sum for the
    ///   critical path, a release out of slice order and a chain read from the
    ///   wrong end.
    /// - witness: `tests::the_bound_of_jobs_with_no_edge_is_the_costliest_job`
    /// - witness: `tests::the_bound_of_a_chain_is_its_whole_cost`
    /// - witness: `tests::a_release_in_slice_order_waits_behind_a_costly_item`
    #[spec(ensures: |ret| ret.critical <= ret.released && ret.released <= ret.serial
        && ret.chain.len() <= costs.len())]
    #[inline]
    #[must_use]
    pub fn bound(
        &self,
        costs: &[Duration],
    ) -> Bound
    {
        let count = costs.len();
        // The latest return among the jobs that each item waits on, and the
        // item whose return that is.
        let mut ready = alloc::vec![(Duration::ZERO, None::<usize>); count];
        // The latest commit among the items that each item waits on.
        let mut waits = alloc::vec![Duration::ZERO; count];
        let mut serial = Duration::ZERO;
        // The release of the item before, since the releases come in slice
        // order.
        let mut release = Duration::ZERO;
        let mut released = Duration::ZERO;
        let mut last = (Duration::ZERO, None::<usize>);
        let mut edges = self.edges.iter().peekable();
        for (item, &cost) in costs.iter().enumerate() {
            let start = ready.get(item).map_or(Duration::ZERO, |&(start, _)| start);
            release = release.max(waits.get(item).copied().unwrap_or_default());
            serial = serial.saturating_add(cost);
            let end = start.saturating_add(cost);
            if end > last.0 || last.1.is_none() {
                last = (end, Some(item));
            }
            let commit = release.saturating_add(cost);
            released = released.max(commit);
            // The edges are sorted by the item waited on, so the edges out of
            // this item come next.
            while let Some(edge) = edges.next_if(|edge| edge.before == item) {
                if let Some(waiting) = ready.get_mut(edge.after)
                    && end > waiting.0
                {
                    *waiting = (end, Some(item));
                }
                if let Some(waiting) = waits.get_mut(edge.after) {
                    *waiting = (*waiting).max(commit);
                }
            }
        }
        let mut chain = Vec::new();
        let mut at = last.1;
        while let Some(item) = at {
            chain.push(ItemIndex(item));
            at = ready.get(item).and_then(|&(_, before)| before);
        }
        chain.reverse();
        Bound {
            serial,
            critical: last.0,
            released,
            chain,
        }
    }
}

/// What a schedule over [`Dependences`] can reach, read from each job's
/// serial cost.
///
/// # Specification
/// - provides: the serial cost, the critical path, the released bound and the
///   chain of the critical path, as [`Dependences::bound`] states them.
/// - panics: none.
/// - executable: none — a plain record; [`Dependences::bound`] states what it
///   holds.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Bound
{
    /// The sum of the costs: the wall time at width one.
    serial: Duration,
    /// The longest chain of dependences, weighted by cost.
    critical: Duration,
    /// The last commit when each release comes in slice order, once the items
    /// that it waits on are committed.
    released: Duration,
    /// The items of the critical path, in slice order.
    chain: Vec<ItemIndex>,
}

impl Bound
{
    /// The sum of the costs: the wall time at width one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn serial(&self) -> Duration
    {
        self.serial
    }

    /// The longest chain of dependences, weighted by cost: no width ends
    /// sooner.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn critical(&self) -> Duration
    {
        self.critical
    }

    /// The last commit when each release comes in slice order, once the items
    /// that it waits on are committed, and each commit comes at its job's
    /// return: the bound of [`Fork::schedule`] at any width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn released(&self) -> Duration
    {
        self.released
    }

    /// The items of the critical path, in slice order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chain(&self) -> &[ItemIndex]
    {
        &self.chain
    }
}

/// An item of a schedule, by its slice position.
///
/// # Specification
/// - provides: the position as given; the order is the slice order.
/// - panics: none.
/// - executable: none — a type-level block: a plain record that
///   [`Dependences::bound`] makes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ItemIndex(usize);

impl From<ItemIndex> for usize
{
    /// The slice position of `item`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(item: ItemIndex) -> Self
    {
        item.0
    }
}

impl From<usize> for ItemIndex
{
    /// The item at slice position `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

/// The size of an item of a schedule: the count of nodes that its job reads.
///
/// # Specification
/// - provides: the count as given; the order is the order of the counts.
/// - panics: none.
/// - executable: none — a type-level block: a plain record that
///   [`Dependences::sized`] holds.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ItemSize(usize);

impl From<ItemSize> for usize
{
    /// The count of nodes of `size`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(size: ItemSize) -> Self
    {
        size.0
    }
}

impl From<usize> for ItemSize
{
    /// The size of `nodes` nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(nodes: usize) -> Self
    {
        Self(nodes)
    }
}

/// One edge of [`Dependences`], by slice position: the release of the item at
/// `after` waits on the commit of the item at `before`.
///
/// # Specification
/// - provides: the two positions as given; the order is by `before`, then by
///   `after`.
/// - panics: none.
/// - executable: none — a type-level block: a plain record that
///   [`Dependences::new`] orders and checks.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dependence
{
    /// The item waited on.
    pub before: usize,
    /// The item that waits.
    pub after: usize,
}

/// An edge whose waiting item does not come after the item that it waits on,
/// so slice order would not be a schedule.
///
/// # Specification
/// - provides: the edge as given.
/// - panics: none.
/// - executable: none — a type-level block: a plain record of the refusal of
///   [`Dependences::new`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Backward
{
    /// The edge as given, whose item that waits is at or before the item
    /// that it waits on.
    pub edge: Dependence,
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
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "item {} cannot wait on item {}, which does not come before it",
            self.edge.after, self.edge.before
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
///   only when there is an item, and the left half before the right; as a
///   [`Spawn`], it holds each job until its wait and runs it there. Its
///   schedule is the serial one: each item's job, then its fold, in slice
///   order, from one state.
///
/// # Adequacy
/// - hypothesis: L3 — no item, one item and several items, and a join that
///   records which half ran first, distinguish a state made for nothing, a
///   state per item, a skipped or reordered item and swapped halves. A job
///   counted at its spawn, at its wait and after its handle was dropped
///   distinguishes an eager spawn and a dropped job that still runs.
/// - witness: `tests::serial_runs_each_item_in_order_from_one_state`
/// - witness: `tests::serial_runs_the_left_half_before_the_right`
/// - witness: `tests::serial_runs_a_spawned_job_at_its_wait`
/// - witness: `tests::serial_releases_runs_and_commits_each_item_in_order`
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

/// A computation run inside a fork's scope, handed the scope's spawner.
///
/// # Specification
/// - provides: the body of [`Fork::scope`] and every job a [`Spawn`] starts.
///   The method is generic over the spawner, so a job runs under whichever
///   spawner the worker that runs it holds, and spawns its own jobs there.
/// - panics: none of its own; a computation's panic is its own.
/// - executable: none — the trait states the shape a consumer's computation
///   takes.
pub trait Scoped<'scope>
{
    /// What the computation answers.
    type Output;

    /// Run the computation, spawning its jobs through `spawner`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the implementation's own result.
    /// - panics: the implementation's own.
    /// - executable: none — the computation is the consumer's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested spawn tree run under each spawner sums its
    ///   leaves.
    /// - declaration-only: the computation is each implementation's; the trait
    ///   has no body to witness.
    fn run<Spawner>(
        self,
        spawner: &Spawner,
    ) -> Self::Output
    where
        Spawner: Spawn<'scope>;
}

/// Starts jobs inside a fork's scope, and waits for each job it started.
///
/// # Specification
/// - provides: the spawn and the wait that a scope's body and its jobs share. A
///   wait runs a job that has not started on the waiting thread. While a
///   started job runs elsewhere, the waiting worker runs other pending jobs,
///   and it never idles.
/// - panics: none of its own; a job's panic is the job's.
/// - executable: none — the trait states obligations its implementations carry;
///   [`Serial`] carries them on the waiting thread.
pub trait Spawn<'scope>
{
    /// What a spawn answers: the handle that its wait takes. A handle dropped
    /// before its job started keeps the job from starting. A handle stays with
    /// the computation that spawned its job.
    type Spawned<Job>
    where
        Job: Scoped<'scope> + 'scope;

    /// Start `job`, possibly on another worker, and answer its handle.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `job` runs at most once, under a spawner of this scope. It
    ///   runs no later than its wait, or than the end of the scope.
    /// - panics: none of its own.
    /// - executable: none — when the job starts is the schedule's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each implementation's witness counts a job's runs at
    ///   its spawn, at its wait and after its handle was dropped.
    /// - declaration-only: the obligation is each implementation's schedule;
    ///   the trait has no body to witness.
    fn spawn<Job>(
        &self,
        job: Job,
    ) -> Self::Spawned<Job>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope;

    /// Wait for the job behind `spawned`, and answer its result.
    ///
    /// # Specification
    /// - requires: the computation that spawned the job waits for it, so the
    ///   waits follow the spawn tree. A wait that other jobs run on top of then
    ///   never waits for a frame below it.
    /// - ensures: `Ok` holds the job's result. A job that had not started ran
    ///   on this thread. Otherwise this thread ran other pending jobs until the
    ///   job ended.
    /// - fails: [`Unwound`] when the job panicked on another worker; its panic
    ///   resumes where the scope ends.
    /// - panics: a panic of the job when it ran on this thread.
    /// - executable: none — where the job ran is the schedule's.
    ///
    /// # Errors
    /// Returns [`Unwound`] for a job that panicked on another worker.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each implementation's witness waits for a job that
    ///   has not started and for one that runs elsewhere, and compares a nested
    ///   spawn tree's sum with the sum of its leaves.
    /// - declaration-only: the obligation is each implementation's schedule;
    ///   the trait has no body to witness.
    fn wait<Job>(
        &self,
        spawned: Self::Spawned<Job>,
    ) -> Result<Job::Output, Unwound>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope;
}

/// A spawned job panicked on another worker. Its panic resumes where its scope
/// ends, so its waiter only stops waiting.
///
/// # Specification
/// - provides: the failure of [`Spawn::wait`] for a job that unwound away from
///   its waiter.
/// - panics: none.
/// - executable: none — a unit marker.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unwound;

/// A job that the serial spawner holds until its wait.
///
/// # Specification
/// - provides: the handle of [`Serial`]'s spawn. Dropping it drops the job
///   unrun.
/// - panics: none.
/// - executable: none — a holder; [`Serial`]'s wait runs the job.
#[derive(Debug)]
#[repr(transparent)]
pub struct Deferred<Job>(Job);

impl<'scope> Spawn<'scope> for Serial
{
    type Spawned<Job>
        = Deferred<Job>
    where
        Job: Scoped<'scope> + 'scope;

    /// Hold `job` until its wait.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn spawn<Job>(
        &self,
        job: Job,
    ) -> Deferred<Job>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope,
    {
        Deferred(job)
    }

    /// Run the held job on the waiting thread, under the serial spawner.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` of the job's result, and never [`Unwound`], because the
    ///   job's panic unwinds through this call.
    /// - panics: a panic of the job.
    /// - executable: none — the result is the job's.
    ///
    /// # Errors
    /// Never returns [`Unwound`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a job counted at its spawn, at its wait and after its
    ///   handle was dropped distinguishes an eager spawn and a dropped job that
    ///   still runs.
    /// - witness: `tests::serial_runs_a_spawned_job_at_its_wait`
    /// - witness: `tests::a_nested_serial_spawn_sums_the_leaves`
    #[inline]
    fn wait<Job>(
        &self,
        spawned: Deferred<Job>,
    ) -> Result<Job::Output, Unwound>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope,
    {
        Ok(spawned.0.run(self))
    }
}

#[cfg(test)]
mod tests;
