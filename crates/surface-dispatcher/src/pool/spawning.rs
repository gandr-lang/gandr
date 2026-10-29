//! The spawner of a scope on the driver's pool.
//!
//! A spawn puts a job's slot on the pool, and the handle keeps a second
//! reference to the slot. The worker that takes the job and the waiter race to
//! claim the slot through one atomic swap. So a wait that comes before any
//! worker took the job runs the job on the waiting thread. While a claimed job
//! runs elsewhere, the waiter runs other pending jobs of the pool through
//! `rayon::yield_now`. When none is pending, it spins and never parks. A
//! worker that waits for a job therefore never holds the job's progress back.
//!
//! **The slot's lock never contends.** The claim is the atomic swap. The job's
//! runner locks the slot to take the job and again to store the result, and
//! the waiter locks it once, after the runner has marked the end. So no two
//! parties hold the lock at once. A ring is not needed for two parties that
//! take turns.
//!
//! **A job's panic stays with the scope.** The runner marks the slot as unwound
//! and lets the panic go on to `rayon`, which resumes it where the scope ends.
//! The waiter sees the mark, stops waiting, and answers [`Unwound`].
//!
//! **A handle stays with its spawner.** A [`Pending`] is not `Send`, so only
//! the computation that spawned a job waits for it, and the waits follow the
//! spawn tree. A waiting worker runs other jobs on top of its frame. Each of
//! them waits only for jobs that it spawned itself, never for a job below it
//! on the same worker, so each of them ends.
//!
//! **A wait nests frames.** A job that the wait runs here, and a job that it
//! helps with, runs on top of the waiting frame. A chain of nested waits
//! therefore nests as deep as its spawn tree.

use alloc::sync::Arc;
use core::hint;
use core::marker::PhantomData;
use core::mem;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use std::sync::Mutex;
use std::sync::MutexGuard;

use gandr_core_fork::Scoped;
use gandr_core_fork::Spawn;
use gandr_core_fork::Unwound;

/// The spawner of a scope on the driver's pool: the `rayon` scope that the
/// worker running the current job holds.
///
/// # Specification
/// - provides: a [`Spawn`] that starts each job on the pool and whose wait runs
///   an unstarted job here and helps the pool while a started one runs.
/// - panics: none of its own.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L3 — a wait that comes before any worker took its job, a wait
///   for a job that waits for a later spawn, a dropped handle and a job that
///   panics on another worker distinguish a waiter that blocks, a job that runs
///   twice or never, and a waiter that waits forever.
/// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
/// - witness: `pool::tests::a_job_that_panics_elsewhere_ends_its_wait`
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Spawning<'borrow, 'scope>(&'borrow rayon::Scope<'scope>);

impl<'borrow, 'scope> Spawning<'borrow, 'scope>
{
    /// The spawner of the `rayon` scope `scope`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(scope: &'borrow rayon::Scope<'scope>) -> Self
    {
        Self(scope)
    }
}

/// A job spawned on the pool, until its wait.
///
/// # Specification
/// - provides: the handle of [`Spawning`]'s spawn. Dropping it before a worker
///   took the job keeps the job from running. It is neither `Send` nor `Sync`,
///   so it stays with the computation that spawned the job.
/// - panics: none.
/// - executable: none — a reference to the slot that the job's runner shares.
#[derive(Debug)]
pub struct Pending<Job, Output>(Arc<Slot<Job, Output>>, PhantomData<*const ()>);

/// What a spawned job's runner and its waiter share.
#[derive(Debug)]
struct Slot<Job, Output>
{
    /// Set by the first of the job's worker and its waiter to take the job.
    claimed: AtomicBool,
    /// Set once the job's result or its unwinding is in `state`.
    ended: AtomicBool,
    /// The job, then its progress, then its result.
    state: Mutex<State<Job, Output>>,
}

/// Where a spawned job is.
#[derive(Debug)]
enum State<Job, Output>
{
    /// Spawned, and taken by no one yet.
    Waiting(Job),
    /// Taken, and running.
    Running,
    /// Ended with its result.
    Answered(Output),
    /// Ended by a panic, which resumes where the scope ends.
    Unwound,
    /// Its result was taken, or its handle dropped it unrun.
    Taken,
}

impl<Job, Output> Slot<Job, Output>
{
    /// The lock on the slot's state. A poisoned lock still gives the state:
    /// no lock is held while the job runs, so no panic leaves a state half
    /// written.
    ///
    /// # Specification
    /// trivial.
    fn state(&self) -> MutexGuard<'_, State<Job, Output>>
    {
        match self.state.lock() {
            Ok(state) => state,
            Err(poisoned) => poisoned.into_inner(),
        }
    }

    /// Run the job under `spawner`, unless its worker or its waiter took it
    /// first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the job runs at most once over every call. A call that takes
    ///   the job marks the slot as ended once the job returns or unwinds.
    /// - panics: a panic of the job, after the slot was marked as unwound.
    /// - executable: none — the claim's winner is the schedule's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    fn run_once<'scope, Spawner>(
        &self,
        spawner: &Spawner,
    ) where
        Job: Scoped<'scope, Output = Output>,
        Spawner: Spawn<'scope>,
    {
        if self.claimed.swap(true, Ordering::AcqRel) {
            return;
        }
        let mut state = self.state();
        let job = match mem::replace(&mut *state, State::Running) {
            State::Waiting(job) => job,
            // The claim is taken once, and only a waiting slot is unclaimed;
            // any other state goes back as it was.
            other @ (State::Running | State::Answered(_) | State::Unwound | State::Taken) => {
                *state = other;
                return;
            },
        };
        drop(state);
        let ending = Ending(self);
        let output = job.run(spawner);
        *self.state() = State::Answered(output);
        drop(ending);
    }
}

/// Marks a slot as ended when its job returns or unwinds.
#[repr(transparent)]
struct Ending<'slot, Job, Output>(&'slot Slot<Job, Output>);

impl<Job, Output> Drop for Ending<'_, Job, Output>
{
    /// Mark the slot as unwound if the job left no result, then as ended.
    ///
    /// # Specification
    /// - ensures: the slot is ended, and holds the job's result or the unwound
    ///   mark.
    /// - panics: none.
    /// - executable: none — runs during an unwind as well.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::a_job_that_panics_elsewhere_ends_its_wait`
    fn drop(&mut self)
    {
        let mut state = self.0.state();
        if matches!(*state, State::Running) {
            *state = State::Unwound;
        }
        drop(state);
        self.0.ended.store(true, Ordering::Release);
    }
}

impl<Job, Output> Drop for Pending<Job, Output>
{
    /// Drop the job unrun if no worker and no waiter took it.
    ///
    /// # Specification
    /// - ensures: a job taken by no one is never run; a taken job is left to
    ///   its runner.
    /// - panics: a panic of the job's own drop.
    /// - executable: none — the claim's winner is the schedule's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    fn drop(&mut self)
    {
        if !self.0.claimed.swap(true, Ordering::AcqRel) {
            let unrun = mem::replace(&mut *self.0.state(), State::Taken);
            drop(unrun);
        }
    }
}

impl<'scope> Spawn<'scope> for Spawning<'_, 'scope>
{
    type Spawned<Job>
        = Pending<Job, Job::Output>
    where
        Job: Scoped<'scope> + 'scope;

    /// Put `job` on the pool, and keep a handle on its slot.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the job's runner is queued on the pool, and it runs the job
    ///   under the spawner of the worker that takes it unless the waiter or a
    ///   dropped handle claimed the job first.
    /// - panics: none of its own.
    /// - executable: none — when the job starts is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    /// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
    #[inline]
    fn spawn<Job>(
        &self,
        job: Job,
    ) -> Pending<Job, Job::Output>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope,
    {
        let slot = Arc::new(Slot {
            claimed: AtomicBool::new(false),
            ended: AtomicBool::new(false),
            state: Mutex::new(State::Waiting(job)),
        });
        let runner = Arc::clone(&slot);
        self.0.spawn(move |scope| runner.run_once(&Spawning(scope)));
        Pending(slot, PhantomData)
    }

    /// Run the job here if no worker took it, else run the pool's other jobs
    /// until it ends, and answer its result.
    ///
    /// # Specification
    /// - requires: the computation that spawned the job waits for it.
    /// - ensures: `Ok` holds the job's result. While the job runs elsewhere,
    ///   this thread runs the pool's pending jobs, and spins when none is
    ///   pending.
    /// - fails: [`Unwound`] when the job panicked on another worker.
    /// - panics: a panic of the job when it ran here.
    /// - executable: none — where the job ran is the pool's.
    ///
    /// # Errors
    /// Returns [`Unwound`] for a job that panicked on another worker.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    /// - witness: `pool::tests::a_job_that_panics_elsewhere_ends_its_wait`
    #[inline]
    fn wait<Job>(
        &self,
        spawned: Pending<Job, Job::Output>,
    ) -> Result<Job::Output, Unwound>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope,
    {
        let slot = &spawned.0;
        slot.run_once(self);
        while !slot.ended.load(Ordering::Acquire) {
            match rayon::yield_now() {
                Some(rayon::Yield::Executed) => {},
                Some(rayon::Yield::Idle) | None => hint::spin_loop(),
            }
        }
        match mem::replace(&mut *slot.state(), State::Taken) {
            State::Answered(output) => Ok(output),
            // An ended slot holds a result or the unwound mark, and only this
            // wait takes the result.
            State::Unwound | State::Waiting(_) | State::Running | State::Taken => Err(Unwound),
        }
    }
}
