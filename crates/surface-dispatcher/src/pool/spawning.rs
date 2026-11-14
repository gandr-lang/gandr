//! The spawner of a scope on the driver's workers.
//!
//! A spawn puts a reference to the job's slot in an idle worker's seat, or in
//! the pool's queue when no worker is idle. The handle keeps a second
//! reference to the slot. The worker that takes the job and the waiter race to
//! claim the slot through one atomic swap. So a wait that comes before any
//! worker took the job runs the job on the waiting thread. While a claimed job
//! runs elsewhere, the waiter runs queued spawns of the pool, and parks when
//! none is queued until the job ends. A thread that waits for a job therefore
//! never holds the job's progress back.
//!
//! **The slot's lock never contends.** The claim is the atomic swap. The job's
//! runner locks the slot to take the job and again to store the result, and
//! the waiter locks it once, after the runner has marked the end. So no two
//! parties hold the lock at once. A ring is not needed for two parties that
//! take turns.
//!
//! **A job's panic stays with the scope.** The runner marks the slot as unwound
//! and keeps the panic in the scope, which resumes it where the scope ends.
//! The waiter sees the mark, stops waiting, and answers [`Unwound`].
//!
//! **A handle stays with its spawner.** A [`Pending`] is not `Send`, so only
//! the computation that spawned a job waits for it, and the waits follow the
//! spawn tree. A waiting thread runs queued spawns on top of its frame. Each of
//! them waits only for jobs that it spawned itself, never for a job below it
//! on the same thread, so each of them ends.
//!
//! **A scope ends once its spawns end.** Each spawn counts the scope up, and
//! the run of its slot counts the scope down, whether the job ran there or
//! not. The scope's end runs queued spawns until the count is zero, so no
//! scope waits for a spawn that no thread takes.
//!
//! **A wait nests frames.** A job that the wait runs here, and a job that it
//! helps with, runs on top of the waiting frame. A chain of nested waits
//! therefore nests as deep as its spawn tree.

use alloc::sync::Arc;
use core::hint;
use core::marker::PhantomData;
use core::mem;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::thread::Thread;

use gandr_core_fork::Scoped;
use gandr_core_fork::Spawn;
use gandr_core_fork::Unwound;

use super::Spin;
use super::workers::FirstPanic;
use super::workers::Helped;
use super::workers::JobRef;
use super::workers::Part;
use super::workers::Workers;

/// A scope over the driver's workers: its spawns that have not ended, the
/// thread that waits at its end, and the first panic of a spawn.
///
/// # Specification
/// - provides: the count that each spawn raises and each run of a slot lowers,
///   and the panic that the scope resumes at its end.
/// - panics: none of its own.
/// - executable: none — a type-level block; [`Scope::open`] carries the
///   obligations.
#[derive(Debug)]
pub struct Scope
{
    /// The spawns whose slot no thread ran yet.
    outstanding: AtomicUsize,
    /// The thread that opened the scope and waits at its end.
    waiter: Thread,
    /// The first panic of a spawned job.
    panic: FirstPanic,
}

impl Scope
{
    /// Run `body` on the calling thread in a scope over `workers`, then end
    /// the scope.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `body` ran once with the scope's spawner. The call returns
    ///   once the slot of each job that the scope spawned has run, so no worker
    ///   holds a job of the scope. While it waits, the calling thread runs
    ///   queued spawns, then polls up to `spin` times and parks until the last
    ///   slot wakes it.
    /// - panics: the panic of `body`, or else the first panic of a spawned job,
    ///   once the scope ended.
    /// - executable: none — where each job ran is the workers'.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested spawn tree on two and four workers, a wait
    ///   for a queued job, and a job that panics on a worker.
    /// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    /// - witness: `pool::tests::a_job_that_panics_elsewhere_ends_its_wait`
    pub fn open<'scope, Body>(
        workers: &Workers,
        spin: Spin,
        body: Body,
    ) -> Body::Output
    where
        Body: Scoped<'scope>,
    {
        let scope = Self {
            outstanding: AtomicUsize::new(0),
            waiter: std::thread::current(),
            panic: FirstPanic::default(),
        };
        let spawning = Spawning {
            workers,
            scope: &scope,
            spin,
            scoped: PhantomData,
        };
        let ran = std::panic::catch_unwind(AssertUnwindSafe(|| body.run(&spawning)));
        let mut polls = 0_u32;
        while scope.outstanding.load(Ordering::Acquire) != 0 {
            if workers.help() == Helped::Ran {
                polls = 0;
            }
            else if polls < spin.0 {
                polls = polls.saturating_add(1);
                hint::spin_loop();
            }
            else {
                workers.park_lent();
            }
        }
        let out = ran.unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        scope.panic.resume();
        out
    }
}

/// The spawner of a scope on the driver's workers: the workers, the scope and
/// the spin budget of each wait.
///
/// # Specification
/// - provides: a [`Spawn`] that hands each job to an idle worker or the pool's
///   queue, and whose wait runs an unstarted job here and runs queued spawns
///   while a started one runs.
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
pub struct Spawning<'borrow, 'scope>
{
    /// The workers that take the spawns.
    workers: &'borrow Workers,
    /// The scope that counts the spawns.
    scope: &'borrow Scope,
    /// How many empty polls a wait makes before it parks.
    spin: Spin,
    /// The lifetime of what the jobs borrow, held invariant.
    scoped: PhantomData<fn(&'scope ()) -> &'scope ()>,
}

/// A job spawned on the workers, until its wait.
///
/// # Specification
/// - provides: the handle of [`Spawning`]'s spawn. Dropping it before a worker
///   took the job keeps the job from running. It is neither `Send` nor `Sync`,
///   so it stays with the computation that spawned the job.
/// - panics: none.
/// - executable: none — a reference to the slot that the job's runner shares.
#[derive(Debug)]
pub struct Pending<'borrow, 'scope, Job, Output>(
    Arc<Slot<'borrow, 'scope, Job, Output>>,
    PhantomData<*const ()>,
);

/// What a spawned job's runner and its waiter share.
#[derive(Debug)]
struct Slot<'borrow, 'scope, Job, Output>
{
    /// Set by the first of the job's worker and its waiter to take the job.
    claimed: AtomicBool,
    /// Set once the job's result or its unwinding is in `state`.
    ended: AtomicBool,
    /// The job, then its progress, then its result.
    state: Mutex<State<Job, Output>>,
    /// The thread that spawned the job, which waits for it.
    waiter: Thread,
    /// The spawner that the job runs under.
    spawner: Spawning<'borrow, 'scope>,
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

impl<Job, Output> Slot<'_, '_, Job, Output>
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
struct Ending<'slot, 'borrow, 'scope, Job, Output>(&'slot Slot<'borrow, 'scope, Job, Output>);

impl<Job, Output> Drop for Ending<'_, '_, '_, Job, Output>
{
    /// Mark the slot as unwound if the job left no result, then as ended, and
    /// wake its waiter.
    ///
    /// # Specification
    /// - ensures: the slot is ended, and holds the job's result or the unwound
    ///   mark; the waiter is unparked.
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
        // A worker's token for this slot goes back before the waiter wakes.
        super::workers::release(self.0);
        self.0.ended.store(true, Ordering::Release);
        self.0.waiter.unpark();
    }
}

impl<Job, Output> Drop for Pending<'_, '_, Job, Output>
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

/// A slot whose job a worker runs from a counted reference.
///
/// # Specification
/// - provides: the run of the slot's job under its spawner, and the count of
///   its scope down.
/// - panics: none.
/// - executable: none — a seam between the slot's type and its runner.
trait Runner
{
    /// Run the job unless its waiter took it, keep its panic in the scope,
    /// drop this reference, and count the scope down.
    ///
    /// # Specification
    /// trivial.
    fn run_counted(self: Arc<Self>);
}

impl<'scope, Job> Runner for Slot<'_, 'scope, Job, Job::Output>
where
    Job: Scoped<'scope> + 'scope,
{
    /// Run the job unless its waiter took it, then count the scope down. The
    /// last slot wakes the thread at the scope's end.
    ///
    /// # Specification
    /// - ensures: the job ran at most once; a panic of it is the scope's. The
    ///   call reads nothing of the scope after the count falls, so the scope
    ///   may end at once.
    /// - panics: none.
    /// - executable: none — the scope reads the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
    /// - witness: `pool::tests::a_job_that_panics_elsewhere_ends_its_wait`
    fn run_counted(self: Arc<Self>)
    {
        let spawner = self.spawner;
        if let Err(panic) = std::panic::catch_unwind(AssertUnwindSafe(|| self.run_once(&spawner))) {
            spawner.scope.panic.keep(panic);
        }
        // A worker's token for this slot goes back before the scope's count
        // falls, unless the slot's end gave it back already.
        super::workers::release(&*self);
        drop(self);
        let waiter = spawner.scope.waiter.clone();
        if spawner.scope.outstanding.fetch_sub(1, Ordering::AcqRel) == 1 {
            waiter.unpark();
        }
    }
}

/// Run the slot of type `Counted` that `frame` holds a counted reference to.
///
/// # Specification
/// trivial.
///
/// # Safety
/// - unsafe invariants: `frame` came from [`Arc::into_raw`] on an
///   `Arc<Counted>`, and no other call takes that reference back.
unsafe fn run_spawned<Counted>(
    frame: *const (),
    _part: Part,
) where
    Counted: Runner,
{
    // SAFETY: the spawn made `frame` with `Arc::into_raw`, and a job reference
    // runs once, so this call takes its count back once.
    let slot = unsafe { Arc::from_raw(frame.cast::<Counted>()) };
    slot.run_counted();
}

impl<'borrow, 'scope> Spawn<'scope> for Spawning<'borrow, 'scope>
{
    type Spawned<Job>
        = Pending<'borrow, 'scope, Job, Job::Output>
    where
        Job: Scoped<'scope> + 'scope;

    /// Hand `job` to an idle worker or to the pool's queue, and keep a handle
    /// on its slot.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the scope counts the job, and its slot is in a worker's seat
    ///   or the pool's queue. Its runner runs the job under this spawner unless
    ///   the waiter or a dropped handle claimed the job first.
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
    ) -> Pending<'borrow, 'scope, Job, Job::Output>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope,
    {
        let slot = Arc::new(Slot {
            claimed: AtomicBool::new(false),
            ended: AtomicBool::new(false),
            state: Mutex::new(State::Waiting(job)),
            waiter: std::thread::current(),
            spawner: *self,
        });
        self.scope.outstanding.fetch_add(1, Ordering::Relaxed);
        let frame = Arc::into_raw(Arc::clone(&slot)).cast::<()>();
        // SAFETY: `frame` holds one count of the slot, which its runner takes
        // back once. The job and its result are `Send`, so the slot runs on any
        // worker.
        let runner = unsafe {
            JobRef::new(
                frame,
                Part(0),
                run_spawned::<Slot<'borrow, 'scope, Job, Job::Output>>,
            )
        };
        // SAFETY: the count that `frame` holds keeps the slot alive until its
        // runner ends.
        unsafe {
            self.workers.spawn(runner);
        }
        Pending(slot, PhantomData)
    }

    /// Run the job here if no worker took it, else run queued spawns until it
    /// ends, and answer its result.
    ///
    /// # Specification
    /// - requires: the computation that spawned the job waits for it.
    /// - ensures: `Ok` holds the job's result. While the job runs elsewhere,
    ///   this thread runs queued spawns, then polls up to the spin budget and
    ///   parks until the job ends.
    /// - fails: [`Unwound`] when the job panicked on another thread.
    /// - panics: a panic of the job when it ran here.
    /// - executable: none — where the job ran is the pool's.
    ///
    /// # Errors
    /// Returns [`Unwound`] for a job that panicked on another thread.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spawning`].
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    /// - witness: `pool::tests::a_job_that_panics_elsewhere_ends_its_wait`
    #[inline]
    fn wait<Job>(
        &self,
        spawned: Pending<'borrow, 'scope, Job, Job::Output>,
    ) -> Result<Job::Output, Unwound>
    where
        Job: Scoped<'scope> + Send + 'scope,
        Job::Output: Send + 'scope,
    {
        let slot = &spawned.0;
        slot.run_once(self);
        let mut polls = 0_u32;
        while !slot.ended.load(Ordering::Acquire) {
            if self.workers.help() == Helped::Ran {
                polls = 0;
            }
            else if polls < self.spin.0 {
                polls = polls.saturating_add(1);
                hint::spin_loop();
            }
            else {
                self.workers.park_lent();
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
