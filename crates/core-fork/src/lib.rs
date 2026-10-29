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
//! # References
//!
//! - `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design
//!   (§ futures-sax): a cut's reader waits for its writer, so a join's right
//!   half may wait for its left half, and never the reverse. A spawned job's
//!   wait is that reader's wait, which runs or helps its writer.

#![no_std]

#[cfg(test)]
extern crate alloc;

/// Runs independent jobs on the workers the driver provides.
///
/// # Specification
/// - provides: the three shapes a program forks by: one job per item, each
///   worker carrying state of its own; two independent halves run beside each
///   other; and a scope whose jobs start apart from their waits.
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
}

/// Every job on the calling thread, in order: the serial reference.
///
/// # Specification
/// - provides: a [`Fork`] that runs items in slice order from one state made
///   only when there is an item, and the left half before the right; as a
///   [`Spawn`], it holds each job until its wait and runs it there.
/// - panics: none.
/// - executable: none — a unit marker; its methods carry the behavior.
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
