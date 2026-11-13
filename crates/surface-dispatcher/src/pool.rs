//! The driver's pool: the one set of worker threads a process forks on.
//!
//! # One pool, held by the driver
//!
//! The driver makes one [`Pool`] at its [`Width`] and hands it to every verb
//! that forks. A walk forks its components on it, a formatting its sources,
//! and a staging each program's stages. The threads start the first time a fork
//! has two items or more, so a visit of one source never asks the host for its
//! topology and never starts a thread. Later forks reuse the same threads.
//! At one thread no pool is built, and every fork runs on the calling thread,
//! the serial reference that every wider fork is tested against.
//!
//! The `no_std` crates name no thread. `gandr-core-fork`'s
//! [`Fork`] is their seam: [`Pooled`] runs a staged check's stages on this
//! pool, and the walk and the formatting spawn their jobs on it directly,
//! because each hands its steps over on the calling thread. [`Pool`]
//! implements [`Fork`] itself, so a session's molding and its trials fork on
//! the same threads, and a scope's jobs spawn there too.
//!
//! **A schedule hands its jobs over rings.** The calling thread releases each
//! item of a [`Fork::schedule`] in slice order, once each item that it waits
//! on is committed. Each task beside it owns a lane: one ring of jobs from the
//! calling thread and one ring of results back, each with one producer and
//! one consumer. The calling thread hands each job that a release gives to a
//! lane with room, and keeps the rest. It commits each job as its result
//! comes back, and each commit counts down the items that wait on the
//! committed one. While it can neither release nor commit, it runs a job that
//! it keeps, or a job of a lane whose task does not run. A task that finds its
//! lane empty spins up to the pool's [`Spin`] budget, then leaves the lane and
//! ends, so that its worker goes back to the pool. The calling thread starts a
//! task again for a lane that it hands a job while no task attends the lane.
//! The calling thread with no result to commit spins up to the budget, then
//! parks. The default budget stops each party at once, so an idle party holds
//! no core. No hand-off takes a lock. The schedule allocates its lanes once,
//! and each task that it starts again costs one spawn on the pool. A task
//! never parks on its worker, because a fork inside a job waits for the
//! pool's workers.
//!
//! **An `each` hands each task its share as one slice.** A fork's items are
//! all known before it starts, so each task takes one slice of them, at most
//! one item longer than any other share, and no task takes a lock or touches
//! a shared counter. The share is the ring's one batch.
//!
//! **One pool, not one per verb.** Before, the walk started scoped threads for
//! each visit and the staging built a `rayon` pool for each run. A process
//! that walks twice, or walks and stages, started its threads more than once.
//! A long-lived process kept none of them warm. The alternative was to keep
//! both pools and share a width, which leaves two sets of threads that can
//! oversubscribe the cores when both are busy. The choice reverses if a
//! consumer measures slower on the shared pool than on threads of its own.
//!
//! **The hand-off is `rayon`'s, and a fork of one item stays on the calling
//! thread.** The admission measurements found that busy-polling rings beat
//! `rayon` on large families, and that `rayon` costs nothing on small ones
//! without a tuned threshold. So the pool is `rayon`, and a fork that has one
//! item runs it on the calling thread. Rings for the admission families are a
//! later rung, measured against this pool.
//!
//! `rayon` is the ecosystem's standard data-parallel pool, maintained by many
//! contributors, with default features off. It brings `rayon-core` and the
//! `crossbeam` deque and epoch crates. The alternatives were these:
//!
//! - _`std::thread::scope` per fork._ This was the walk's pool. A per-item fork
//!   inside each half of a join starts a second set of threads beside the
//!   first, and no thread outlives its fork. Reversal: a process that forks
//!   once and never nests.
//! - _[`chili`](https://crates.io/crates/chili), a heartbeat-scheduled `join`._
//!   It offers `join` without a scope for the per-item fork, and one maintainer
//!   carries it. Reversal: a scope and a release history in it, and a measured
//!   gain on a verb.
//!
//! The choice of `rayon` reverses on any of these: an advisory against `rayon`
//! or `rayon-core` that no release fixes, an unmaintained mark, or a measured
//! loss against scoped threads on a verb.
//!
//! **No scheduling class.** Raising every pool thread to the user-interactive
//! quality-of-service class changed no admission cell over three runs, so the
//! pool's threads keep the host's default. The choice reverses on a
//! measurement that shows a class pays on a verb.

mod lane;
#[cfg(feature = "instrument")]
pub mod recording;
mod spawning;

use alloc::collections::VecDeque;
use alloc::sync::Arc;
use core::any::Any;
use core::fmt;
use core::num::NonZeroUsize;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_fork::Dependence;
use gandr_core_fork::Dependences;
use gandr_core_fork::Fork;
use gandr_core_fork::Releasing;
use gandr_core_fork::Scoped;
use gandr_core_fork::Serial;
use gandr_kernel_core::fork::ForkWidth;
use gandr_kernel_core::fork::Job;
use gandr_kernel_core::fork::ObligationFork;
use quenchant_shape::shape::Maybe;

use self::lane::Attendance;
use self::lane::DEPTH;
use self::lane::Feed;
use self::lane::Lane;
use self::lane::Sleeper;
use self::lane::Tending;
use self::spawning::Spawning;
use crate::width::Threads;
use crate::width::Width;

quenchant_shape::reason_enum! {
    /// Why a fork runs on the calling thread alone.
    pub(crate) mod alone {
        /// The reason no pool takes the fork.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// The fork has one item or none, or the width is one thread.
            Serial,
            /// The host refused the pool's threads.
            Refused,
        }
    }
}

/// The driver's worker threads: one pool at one width, started on the first
/// fork that has two items or more and reused by every later fork.
///
/// # Specification
/// - provides: the threads every forking verb of one process runs on, and the
///   width they number.
/// - panics: none.
/// - executable: none — the threads are started and kept by `rayon`.
///
/// # Adequacy
/// - hypothesis: L2 — a walk and a staging forked on one pool at three threads
///   and at the host's width give the serial visit's and the serial run's
///   output.
/// - witness: `tests::walk::a_tree_is_walked_in_order`
/// - witness: `stage::tests::every_width_stages_the_serial_run`
#[derive(Debug)]
pub struct Pool
{
    /// How many threads the pool runs.
    width: Width,
    /// How many empty polls a party of a schedule makes before it stops.
    spin: Spin,
    /// The threads, once a fork asked for them.
    started: OnceLock<Result<Started, PoolFault>>,
}

/// How many empty polls a waiting party of a schedule makes before it stops:
/// a task whose lane holds no job leaves the lane and ends, and the calling
/// thread with no result to commit parks.
///
/// The default, [`Spin::PARK`], stops at once, so an idle party holds no core.
/// A park and its unpark cost about 26 µs at the median on the `riscv64` host,
/// and about 540 ns under a budget of 10,000 polls, which holds about 0.9 of a
/// core for each idle party. The policy group of the speculative readmission
/// sets the budget by the kind of run.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Spin(u32);

impl Spin
{
    /// No poll: a party stops as soon as it finds no work.
    pub const PARK: Self = Self(0);
}

impl From<u32> for Spin
{
    /// A budget of `polls` empty polls before a party stops.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(polls: u32) -> Self
    {
        Self(polls)
    }
}

/// A pool's threads, as its width resolved on the host.
#[derive(Debug)]
struct Started
{
    /// How many threads the width resolved to.
    threads: Threads,
    /// The pool, at two threads or more.
    pool: Maybe<rayon::ThreadPool, alone::Absent>,
}

impl Pool
{
    /// A pool of `width` threads, none of them started yet, whose schedules
    /// park at once.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(width: Width) -> Self
    {
        Self {
            width,
            spin: Spin::PARK,
            started: OnceLock::new(),
        }
    }

    /// The pool, whose schedules poll up to `spin` times before a party
    /// parks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn spinning(
        mut self,
        spin: Spin,
    ) -> Self
    {
        self.spin = spin;
        self
    }

    /// The width the pool was made at.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn width(&self) -> Width
    {
        self.width
    }

    /// The pool's threads, started on the first call.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same answer on every call: the width resolved on the host
    ///   and, at two threads or more, a `rayon` pool of that many threads; at
    ///   one thread, no pool.
    /// - fails: [`PoolFault`] when the host refused the pool's threads, on this
    ///   call and every later one.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the [`PoolFault`] of the one build attempt.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a serial pool starts no thread; a wider pool runs
    ///   each fork's items once from a state per busy worker.
    /// - witness: `pool::tests::a_serial_pool_starts_no_thread`
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "pool: this is the workspace's one work pool, built once at the host's width"
        )
    )]
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|started| (started.threads == Threads::ONE) == matches!(started.pool, Maybe::Absent(_))))]
    fn started(&self) -> &Result<Started, PoolFault>
    {
        self.started.get_or_init(|| {
            let threads = self.width.threads();
            if threads == Threads::ONE {
                return Ok(Started {
                    threads,
                    pool: Maybe::Absent(alone::Absent::Serial),
                });
            }
            rayon::ThreadPoolBuilder::new()
                .num_threads(NonZeroUsize::from(threads).get())
                .build()
                .map(|pool| Started {
                    threads,
                    pool: Maybe::Present(pool),
                })
                .map_err(|error| PoolFault(Arc::new(error)))
        })
    }

    /// The threads a fork of `items` runs on beside the calling thread, and
    /// the pool that runs them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for two items or more, the started pool and one helper fewer
    ///   than the smaller of its threads and the items; the calling thread is
    ///   the last of them.
    /// - provides: [`alone::Absent::Serial`] for one item or none, or a pool of
    ///   one thread, and [`alone::Absent::Refused`] when the host refused the
    ///   pool's threads; neither asks the host twice.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Pool`].
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `pool::tests::a_serial_pool_starts_no_thread`
    #[spec(ensures: |ret| items.len() > 1_usize || matches!(ret, Maybe::Absent(alone::Absent::Serial)))]
    pub(crate) fn helpers<T>(
        &self,
        items: &[T],
    ) -> Maybe<(&rayon::ThreadPool, Threads), alone::Absent>
    {
        if items.len() <= 1 {
            return Maybe::Absent(alone::Absent::Serial);
        }
        match *self.started() {
            Ok(Started {
                threads,
                pool: Maybe::Present(ref pool),
            }) => {
                let helpers = NonZeroUsize::from(threads)
                    .get()
                    .min(items.len())
                    .saturating_sub(1);
                NonZeroUsize::new(helpers).map_or(Maybe::Absent(alone::Absent::Serial), |helpers| {
                    Maybe::Present((pool, Threads::from(helpers)))
                })
            },
            Ok(Started {
                pool: Maybe::Absent(_),
                ..
            }) => Maybe::Absent(alone::Absent::Serial),
            Err(_) => Maybe::Absent(alone::Absent::Refused),
        }
    }

    /// The fork a staged check runs on, and the pool to enter for it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: at one thread, no pool and the serial fork; wider, the
    ///   started pool and [`Pooled`] at its threads.
    /// - fails: [`PoolFault`] when the host refused the pool's threads.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the pool's [`PoolFault`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Pool`].
    /// - witness: `stage::tests::every_width_stages_the_serial_run`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|forked| matches!(*forked, Forked::Serial) == (self.width.threads() == Threads::ONE)))]
    pub(crate) fn forked(&self) -> Result<Forked<'_>, PoolFault>
    {
        match *self.started() {
            Ok(Started {
                threads,
                pool: Maybe::Present(ref pool),
            }) => Ok(Forked::Pooled(pool, Pooled {
                threads,
                spin: self.spin,
            })),
            Ok(Started {
                pool: Maybe::Absent(_),
                ..
            }) => Ok(Forked::Serial),
            Err(ref fault) => Err(fault.clone()),
        }
    }

    /// The threads standing work is spawned on, whatever its count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: at two threads or more, the started pool.
    /// - provides: [`alone::Absent::Serial`] at one thread and
    ///   [`alone::Absent::Refused`] when the host refused the pool's threads;
    ///   the work then runs on the calling thread.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a submission at one thread runs on the caller, and
    ///   one on four threads runs beside it.
    /// - witness: `generation::tests::a_serial_pool_runs_each_job_on_the_caller`
    /// - witness: `generation::tests::a_conflicting_submission_retires_the_older_generation`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(alone::Absent::Serial)) == (self.width.threads() == Threads::ONE))]
    pub(crate) fn standing(&self) -> Maybe<&rayon::ThreadPool, alone::Absent>
    {
        match *self.started() {
            Ok(Started {
                pool: Maybe::Present(ref pool),
                ..
            }) => Maybe::Present(pool),
            Ok(Started {
                pool: Maybe::Absent(_),
                ..
            }) => Maybe::Absent(alone::Absent::Serial),
            Err(_) => Maybe::Absent(alone::Absent::Refused),
        }
    }
}

impl Default for Pool
{
    /// A pool of one thread: every fork runs on the calling thread.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new(Width::SERIAL)
    }
}

/// Where the walk's lowering jobs run: the pool itself, or a recording fork
/// over it that marks each job.
///
/// # Specification
/// - provides: the pool that the jobs run on, and the run of one job, which the
///   pool runs as it stands and a recording runs between two marks.
/// - panics: none of its own.
/// - executable: none — a seam between the walk and the pool.
pub trait Helped: Sync
{
    /// The pool that the jobs run on.
    ///
    /// # Specification
    /// trivial.
    fn pool(&self) -> &Pool;

    /// Run `work` as one job that names no declaration.
    ///
    /// # Specification
    /// trivial.
    fn job<Out>(
        &self,
        work: impl FnOnce() -> Out,
    ) -> Out;
}

impl Helped for Pool
{
    /// The pool itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pool(&self) -> &Pool
    {
        self
    }

    /// Run `work` as it stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn job<Out>(
        &self,
        work: impl FnOnce() -> Out,
    ) -> Out
    {
        work()
    }
}

/// The pool as a fork that any consumer is handed: the items run on the pool's
/// own threads, or on the calling thread when the fork cannot use them.
impl Fork for Pool
{
    /// Run `job` on every item on the pool's threads, each task running one
    /// share of the items.
    ///
    /// # Specification
    /// - ensures: `job` runs once per item. One item or none, a pool of one
    ///   thread and a pool the host refused run every item on the calling
    ///   thread from one state, and none of them starts a thread. Otherwise the
    ///   items run on the pool's own threads as [`Pooled`] runs them.
    /// - panics: a job's panic, at the end of the fork.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one item, many items and a serial pool, each
    ///   recording the thread that every item ran on, distinguish a fork that
    ///   starts the pool for one item, a fork that runs outside the pool's
    ///   threads and a skipped item.
    /// - witness: `pool::tests::a_pool_forks_on_its_own_threads`
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
        if items.len() <= 1 {
            Serial.each(items, start, job);
            return;
        }
        match self.forked() {
            Ok(Forked::Pooled(threads, fork)) => {
                let (start, job) = (&start, &job);
                threads.install(move || fork.each(items, start, job));
            },
            Ok(Forked::Serial) | Err(_) => Serial.each(items, start, job),
        }
    }

    /// Run both halves on the pool's threads through `rayon::join`, or the
    /// left and then the right on the calling thread when the pool has one
    /// thread or the host refused it.
    ///
    /// # Specification
    /// - ensures: each half runs once, and the pair is their results in
    ///   argument order. The left half begins before the join waits for the
    ///   right one: `rayon::join` runs it on the joining worker, and the
    ///   calling thread runs it first.
    /// - panics: a panic of either half.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a join on a wide pool and on a serial pool, each
    ///   recording where its halves ran, distinguish halves run outside the
    ///   pool and swapped results; a right half that waits for its left half's
    ///   signal sees it at either width, where a join that waited for the right
    ///   half first would leave it waiting.
    /// - witness: `pool::tests::a_pool_forks_on_its_own_threads`
    /// - witness: `pool::tests::a_right_half_may_wait_for_the_left_one`
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
        match self.forked() {
            Ok(Forked::Pooled(threads, fork)) => threads.install(move || fork.join(left, right)),
            Ok(Forked::Serial) | Err(_) => Serial.join(left, right),
        }
    }

    /// Run `body` in a scope on the pool's threads, or in the serial scope
    /// when the pool has one thread or the host refused it.
    ///
    /// # Specification
    /// - ensures: as [`Fork::scope`]. At two threads or more, `body` runs on a
    ///   pool worker in a scope that [`Pooled`] opens, and every job on any
    ///   worker of the pool; otherwise each job runs at its wait on the calling
    ///   thread.
    /// - panics: a panic of `body`, or of a spawned job, at the end of the
    ///   scope.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested spawn tree on a serial pool, on two threads
    ///   and on four sums its leaves; a wait that would block its worker leaves
    ///   a job that its own job waits for unrun.
    /// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
    /// - witness: `pool::tests::a_wait_runs_its_job_here_or_helps_until_it_ends`
    #[inline]
    fn scope<'scope, Body>(
        &self,
        body: Body,
    ) -> Body::Output
    where
        Body: Scoped<'scope> + Send,
        Body::Output: Send,
    {
        match self.forked() {
            Ok(Forked::Pooled(threads, fork)) => threads.install(move || fork.scope(body)),
            Ok(Forked::Serial) | Err(_) => Serial.scope(body),
        }
    }

    /// Release each item on the calling thread in slice order, run each job
    /// on the pool's threads, and commit each item on the calling thread as
    /// its job returns.
    ///
    /// # Specification
    /// - ensures: as [`Fork::schedule`]. One item or none, a pool of one thread
    ///   and a pool the host refused run the serial schedule on the calling
    ///   thread, and none of them starts a thread. Otherwise the jobs run on
    ///   the pool's own threads as [`Pooled`] runs them, and on the calling
    ///   thread while it waits; the calling thread releases and commits every
    ///   item.
    /// - panics: a panic of `release`, `run` or `commit`, on the calling
    ///   thread.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one item, many items and a serial pool, each
    ///   recording the thread of every release, job and commit, distinguish a
    ///   schedule that starts the pool for one item, a job run on a thread that
    ///   is neither the pool's nor the caller's, and a release or a commit off
    ///   the calling thread.
    /// - witness: `pool::tests::a_pool_schedules_on_its_own_threads_and_commits_on_the_caller`
    #[inline]
    fn schedule<Item, Job, Out, Release, Run, Commit>(
        &self,
        items: &mut [Item],
        after: &Dependences,
        release: Release,
        run: Run,
        commit: Commit,
    ) where
        Job: Send,
        Out: Send,
        Release: FnMut(gandr_core_fork::ItemIndex, &mut Item) -> Releasing<Job, Out>,
        Run: Fn(Job) -> Out + Sync,
        Commit: FnMut(gandr_core_fork::ItemIndex, &mut Item, Out),
    {
        if items.len() <= 1 {
            Serial.schedule(items, after, release, run, commit);
            return;
        }
        match self.forked() {
            Ok(Forked::Pooled(threads, fork)) => schedule_indexed(
                Some(threads),
                fork,
                items,
                after,
                release,
                |_index, job| run(job),
                commit,
            ),
            Ok(Forked::Serial) | Err(_) => Serial.schedule(items, after, release, run, commit),
        }
    }
}

/// The pool as the fork of a kernel check's obligations: the parts of a
/// declaration's last drain run as [`Fork::each`] runs its items.
impl ObligationFork for Pool
{
    /// Run each part once, as [`Fork::each`] runs an item, with no state for
    /// a worker.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Fork::each`] ensures.
    /// - panics: a part's panic, at the end of the fork.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pool of four threads and a serial pool each run 16
    ///   parts of a drain, and each part runs once.
    /// - witness: `pool::tests::the_pool_runs_each_part_of_a_drain_once_at_its_width`
    #[inline]
    fn run_jobs(
        &self,
        jobs: &mut [&mut dyn Job],
    )
    {
        self.each(jobs, || (), |_worker, job| job.run());
    }

    /// The threads the pool runs, as the host resolved its width: one when
    /// the host refused the pool's threads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same width on each call, the threads that [`Fork::each`]
    ///   runs the parts on.
    /// - panics: none.
    /// - executable: none — the width is the host's, resolved once.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pool of four threads gives four workers, and a
    ///   serial pool gives one.
    /// - witness: `pool::tests::the_pool_runs_each_part_of_a_drain_once_at_its_width`
    #[inline]
    fn workers(&self) -> ForkWidth
    {
        let threads = self
            .started()
            .as_ref()
            .map_or(Threads::ONE, |started| started.threads);
        ForkWidth::from(NonZeroUsize::from(threads))
    }
}

/// Where a staged check's jobs run.
#[derive(Debug)]
pub enum Forked<'pool>
{
    /// The calling thread alone.
    Serial,
    /// The driver's pool, and the fork over it.
    Pooled(&'pool rayon::ThreadPool, Pooled),
}

/// The pool as the checker's fork: each forked stage hands one share of its
/// items to each of at most one task per worker, and a schedule hands its
/// jobs over one lane for each task.
///
/// # Specification
/// - provides: a [`Fork`] whose every task makes its worker state once, on its
///   first item, so a stage clones no more snapshots than it has workers with
///   work; halves join through `rayon::join`, and a scope's jobs spawn on the
///   pool through `rayon::in_place_scope`.
/// - panics: none of its own; a job's panic resumes at the fork.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L2 — programs checked at three workers and at the host's width
///   print the serial run, digest and verdict.
/// - witness: `stage::tests::every_width_stages_the_serial_run`
#[derive(Clone, Copy, Debug)]
pub struct Pooled
{
    /// The pool's threads.
    threads: Threads,
    /// How many empty polls a party of a schedule makes before it parks.
    spin: Spin,
}

impl Fork for Pooled
{
    /// Run `job` on every item from one task per worker, each running one
    /// share of the items.
    ///
    /// # Specification
    /// - ensures: `job` runs once per item; each task makes its state on its
    ///   first item and keeps it for the rest. A stage of one item, or a pool
    ///   of one worker, runs on the calling thread.
    /// - panics: a job's panic, at the end of the scope.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no item, one item, fewer items than workers and many
    ///   more, counting each item's visits and the states made, distinguish a
    ///   skipped or repeated item and a state made per item or per idle worker.
    /// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
    /// - witness: `pool::tests::one_item_runs_on_the_caller_and_many_on_the_workers`
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
        each_indexed(self.threads, items, start, |state, _index, item| {
            job(state, item);
        });
    }

    /// Run both halves through `rayon::join`, which runs the left half on the
    /// joining worker before it waits for the right one.
    ///
    /// # Specification
    /// trivial.
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "pool: `Fork::join` on the driver's pool, which its caller installs before it forks"
        )
    )]
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
        rayon::join(left, right)
    }

    /// Run `body` in a `rayon` scope opened on the calling worker, handing it
    /// the pooled spawner.
    ///
    /// # Specification
    /// - ensures: as [`Fork::scope`]; the scope ends once every job it spawned
    ///   has ended or was dropped unrun.
    /// - panics: a panic of `body`, or of a spawned job, at the end of the
    ///   scope.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pool`]'s scope.
    /// - witness: `pool::tests::nested_spawns_sum_the_leaves_at_every_width`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "pool: `Fork::scope` on the driver's pool, which its caller installs before it forks"
        )
    )]
    #[inline]
    fn scope<'scope, Body>(
        &self,
        body: Body,
    ) -> Body::Output
    where
        Body: Scoped<'scope> + Send,
        Body::Output: Send,
    {
        rayon::in_place_scope(|scope| body.run(&Spawning::new(scope)))
    }

    /// Release each item on the calling thread in slice order, run each job
    /// on the pool, and commit each item on the calling thread as its job
    /// returns.
    ///
    /// # Specification
    /// - ensures: as [`Fork::schedule`]. Each item holds a count of the items
    ///   that it waits on and that are not committed. The calling thread
    ///   releases the next item in slice order once its count is zero and no
    ///   release holds. One task for each other pool thread owns a lane: a ring
    ///   of jobs and a ring of results. After each release that gives a job,
    ///   the calling thread hands the jobs that it keeps to lanes with room, a
    ///   lane with no job first, and keeps the rest in release order. It
    ///   commits each job as its result comes back, and each commit counts down
    ///   the items that wait on the committed one. A held release waits until
    ///   each job that it keeps or that a lane holds is committed. While the
    ///   calling thread can neither release nor commit, it runs the oldest job
    ///   that it keeps, or else a job of a lane whose task does not run, and it
    ///   parks only when neither is left. A schedule of one item, or a pool of
    ///   one worker, runs on the calling thread.
    /// - panics: a panic of `release`, `run` or `commit`, resumed on the
    ///   calling thread once it has returned; no queued job starts after it.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — graphs with no edge, a chain and a scattered fan over
    ///   no item, one item and many, stamping each release, each job's start
    ///   and end and each commit, distinguish a release before an item that it
    ///   waits on is committed, a release out of order, a skipped or repeated
    ///   job, and a commit before its job or off the calling thread. A job that
    ///   returns before an earlier one distinguishes a commit in slice order,
    ///   and a held release distinguishes a release again while a job runs.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_held_release_waits_until_every_running_job_is_committed`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    #[inline]
    fn schedule<Item, Job, Out, Release, Run, Commit>(
        &self,
        items: &mut [Item],
        after: &Dependences,
        release: Release,
        run: Run,
        commit: Commit,
    ) where
        Job: Send,
        Out: Send,
        Release: FnMut(gandr_core_fork::ItemIndex, &mut Item) -> Releasing<Job, Out>,
        Run: Fn(Job) -> Out + Sync,
        Commit: FnMut(gandr_core_fork::ItemIndex, &mut Item, Out),
    {
        schedule_indexed(
            None,
            *self,
            items,
            after,
            release,
            |_index, job| run(job),
            commit,
        );
    }
}

/// The place of an item in the slice that a fork runs a job on.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ItemIndex(usize);

impl From<ItemIndex> for usize
{
    /// The place of `index` in its slice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ItemIndex) -> Self
    {
        index.0
    }
}

/// Run `job` on every item and its index, each task on one share of the
/// items: at most `workers` shares, each of one item or more. At one worker
/// the items run on the calling thread in slice order, from one state.
///
/// # Specification
/// - ensures: `job` runs once per item with the item's place in `items`. Each
///   share is one slice, at most one item longer than any other share. Its task
///   runs it in slice order, makes its state on its first item and keeps it for
///   the rest. No task takes a lock or touches a counter that another task
///   writes.
/// - panics: a job's panic, at the end of the scope.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Pooled`]'s `each`.
/// - witness: `pool::tests::a_pool_visits_each_item_once_from_a_state_per_busy_worker`
/// - witness: `pool::tests::one_item_runs_on_the_caller_and_many_on_the_workers`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "pool: `Fork::each` on the driver's pool, which its caller installs before it forks"
    )
)]
fn each_indexed<Item, State, Start, Job>(
    workers: Threads,
    items: &mut [Item],
    start: Start,
    job: Job,
) where
    Item: Send,
    Start: Fn() -> State + Sync,
    Job: Fn(&mut State, ItemIndex, &mut Item) + Sync,
{
    let count = items.len();
    let workers = NonZeroUsize::from(workers).get().min(count);
    let share = |first: usize, part: &mut [Item]| {
        let mut state = None;
        for (offset, item) in part.iter_mut().enumerate() {
            job(
                state.get_or_insert_with(&start),
                ItemIndex(first.saturating_add(offset)),
                item,
            );
        }
    };
    if workers <= 1 {
        share(0, items);
        return;
    }
    // Each share holds `whole` items, and the first `longer` shares hold one
    // more. The calling thread runs the last share.
    let whole = count.checked_div(workers).unwrap_or_default();
    let longer = count.checked_rem(workers).unwrap_or_default();
    rayon::scope(|scope| {
        let share = &share;
        let mut rest = items;
        let mut first = 0_usize;
        for task in 1 .. workers {
            let length = whole
                .saturating_add(usize::from(task <= longer))
                .min(rest.len());
            let (part, after) = core::mem::take(&mut rest).split_at_mut(length);
            rest = after;
            scope.spawn(move |_scope| share(first, part));
            first = first.saturating_add(length);
        }
        share(first, rest);
    });
}

/// Release each item on the calling thread in slice order, run each job that
/// a release gives with its item's place, on `pool` or on the pool that the
/// calling thread runs in, and commit each item on the calling thread as its
/// job returns. Each task beside the calling thread owns one lane. At one
/// worker, or one item, each item is released, run and committed on the
/// calling thread in slice order.
///
/// # Specification
/// - ensures: as [`Pooled`]'s `schedule`, with the item's place handed to each
///   job. A calling thread outside the pool has one lane for each pool thread
///   beside it, and one inside the pool one for each other pool thread; no
///   schedule has more lanes than items. A lane's task starts when the lane
///   takes a job that no task attends. Each party that waits polls up to
///   `fork`'s spin budget before it parks.
/// - panics: a panic of `release`, `run` or `commit`, resumed on the calling
///   thread once it has returned.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
/// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
/// - witness: `pool::tests::a_held_release_waits_until_every_running_job_is_committed`
/// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
/// - witness: `pool::tests::a_schedule_inside_a_scheduled_job_ends`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "pool: `Fork::schedule` on the driver's pool, which its caller names or installs before it forks"
    )
)]
fn schedule_indexed<Item, Job, Out, Release, Run, Commit>(
    pool: Option<&rayon::ThreadPool>,
    fork: Pooled,
    items: &mut [Item],
    after: &Dependences,
    mut release: Release,
    run: Run,
    mut commit: Commit,
) where
    Job: Send,
    Out: Send,
    Release: FnMut(gandr_core_fork::ItemIndex, &mut Item) -> Releasing<Job, Out>,
    Run: Fn(ItemIndex, Job) -> Out + Sync,
    Commit: FnMut(gandr_core_fork::ItemIndex, &mut Item, Out),
{
    let count = items.len();
    let threads = NonZeroUsize::from(fork.threads).get();
    if threads.min(count) <= 1 {
        for (index, item) in items.iter_mut().enumerate() {
            let position = gandr_core_fork::ItemIndex::from(index);
            let out = match release(position, item) {
                Releasing::Run(job) => run(ItemIndex(index), job),
                // No job runs at a release here, so a held release commits
                // the result that it holds.
                Releasing::Settled(out) | Releasing::Held(out) => out,
            };
            commit(position, item, out);
        }
        return;
    }
    // A calling thread inside the pool takes one of the pool's threads.
    let tasks = match pool {
        Some(_) => threads,
        None => threads.saturating_sub(1),
    }
    .min(count);
    // Both counts are at least two here, so `tasks` is at least one.
    let tasks = NonZeroUsize::new(tasks).map_or(Threads::ONE, Threads::from);
    let (schedule, ledger) = Scheduled::new(tasks, items, run, fork.spin);
    let waiting = Waiting::new(after, items);
    let calls = (&mut release, &mut commit);
    match pool {
        Some(pool) => {
            pool.in_place_scope(|scope| schedule.drive(scope, ledger, items, waiting, calls));
        },
        None => {
            rayon::in_place_scope(|scope| schedule.drive(scope, ledger, items, waiting, calls));
        },
    }
}

/// What a scheduled job hands back to the calling thread: its item's place
/// and its result, or its panic.
type Returned<Out> = Result<(ItemIndex, Out), Box<dyn Any + Send>>;

/// A job that may run: its item's place and the job that the release gave.
type Ready<Job> = (ItemIndex, Job);

/// Whether the calling thread ran a job of a lane.
///
/// # Specification
/// - provides: the answer of [`Scheduled::take`].
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Taken
{
    /// It ran one job of a lane whose task did not run it.
    Ran,
    /// No lane held a job that no task runs.
    Idle,
}

/// How many releases a chained schedule puts off for each release that it
/// tries beside a running job. A schedule runs as a chain after a release
/// holds while a job runs: the next release reads what that job commits, so
/// the calling thread runs the job itself, and a hand-off would only cost a
/// task's start. A try stages the item and gives the staging back when it
/// holds, so a chain spends one try in 64 releases on finding parallel work.
const CHAIN_PROBE: usize = 64;

/// One schedule's state that its tasks share.
///
/// # Specification
/// - provides: one lane for each task, the calling thread's sleeper, the run of
///   a job, the spin budget, and the end of the schedule.
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
struct Scheduled<Job, Out, Run>
{
    /// One lane for each task beside the calling thread.
    lanes: Vec<Lane<Ready<Job>, Returned<Out>>>,
    /// The calling thread, which parks while it waits for a result.
    caller: Sleeper,
    /// Runs a released job.
    run: Run,
    /// How many empty polls a party makes before a task leaves its lane or
    /// the calling thread parks.
    spin: Spin,
    /// Set once the schedule ends or the calling thread resumes a panic, so
    /// that no task starts another job.
    ended: AtomicBool,
}

/// What the calling thread alone holds of a schedule's lanes.
///
/// # Specification
/// - provides: the calling thread's end of each lane, the lanes that hold a job
///   not yet committed, the count of lanes with room, the released jobs that no
///   lane holds, and the lane that the next hand-off tries first.
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
struct Ledger<Job, Out>
{
    /// The calling thread's end of each lane.
    feeds: Vec<Feed<Ready<Job>, Returned<Out>>>,
    /// The lanes that hold a job not yet committed, in no order.
    busy: Vec<usize>,
    /// How many lanes hold fewer than [`DEPTH`] jobs.
    room: usize,
    /// The released jobs that no lane holds, in release order.
    kept: VecDeque<Ready<Job>>,
    /// The lane that the next hand-off tries first.
    turn: usize,
}

/// The end of a schedule: when the calling thread leaves the schedule, by its
/// return or by a panic, each task ends.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Ending<'schedule, Job, Out, Run>(&'schedule Scheduled<Job, Out, Run>);

impl<Job, Out, Run> Drop for Ending<'_, Job, Out, Run>
{
    /// End the schedule.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.0.end();
    }
}

/// What the calling thread alone holds of a schedule: each item's successors
/// and its count of the items that it waits on and that are not committed.
///
/// # Specification
/// - provides: the edges within the slice, sorted by their earlier item, and
///   where each item's edges start; a count for each item.
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
struct Waiting
{
    /// Every edge within the slice, sorted by its earlier item.
    edges: Vec<Dependence>,
    /// Where each item's edges start in `edges`, and one past the last.
    starts: Vec<usize>,
    /// Each item's count of the items that it waits on and that are not
    /// committed.
    counts: Vec<usize>,
}

impl Waiting
{
    /// The counts of `items` under `after`, each before any commit.
    ///
    /// # Specification
    /// - ensures: one count for each item: the edges within the slice that end
    ///   at it. Edges past the slice are dropped. The plan takes one pass over
    ///   the items and the edges.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    #[spec(ensures: |ret| ret.counts.len() == items.len()
        && ret.starts.len() == items.len().saturating_add(1))]
    fn new<Item>(
        after: &Dependences,
        items: &[Item],
    ) -> Self
    {
        let count = items.len();
        let edges: Vec<Dependence> = after
            .edges()
            .iter()
            .copied()
            .filter(|edge| edge.after < count)
            .collect();
        // The edges are sorted by their earlier item, so one sweep finds where
        // each item's edges start.
        let mut starts = Vec::with_capacity(count.saturating_add(1));
        let mut first = 0_usize;
        let mut counts = alloc::vec![0_usize; count];
        for position in 0 ..= count {
            while let Some(&Dependence { after: later, .. }) =
                edges.get(first).filter(|edge| edge.before < position)
            {
                if let Some(waits) = counts.get_mut(later) {
                    *waits = waits.saturating_add(1);
                }
                first = first.saturating_add(1);
            }
            starts.push(first);
        }
        Self {
            edges,
            starts,
            counts,
        }
    }

    /// Whether the item at `position` waits on no item that is not committed.
    /// An item past the slice waits on nothing that can come.
    ///
    /// # Specification
    /// trivial.
    fn free(
        &self,
        position: ItemIndex,
    ) -> Released
    {
        match self.counts.get(position.0).copied() {
            Some(0) => Released::Free,
            Some(_) => Released::Waiting,
            None => Released::Past,
        }
    }

    /// Count down every item that waits on the item at `position`.
    ///
    /// # Specification
    /// - ensures: each successor's count falls by one.
    /// - panics: none.
    /// - executable: none — a count of each successor, which a postcondition
    ///   over the whole vector would copy to compare.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    fn commit(
        &mut self,
        position: ItemIndex,
    )
    {
        let successors = self
            .starts
            .get(position.0)
            .zip(self.starts.get(position.0.saturating_add(1)))
            .and_then(|(&first, &last)| self.edges.get(first .. last))
            .unwrap_or_default();
        for &Dependence { after: later, .. } in successors {
            if let Some(waits) = self.counts.get_mut(later) {
                *waits = waits.saturating_sub(1);
            }
        }
    }
}

/// Whether the calling thread may release an item now.
///
/// # Specification
/// - provides: the answer of [`Waiting::free`].
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Released
{
    /// Every item that it waits on is committed.
    Free,
    /// An item that it waits on is not committed.
    Waiting,
    /// Every item is released.
    Past,
}

/// Whether a schedule runs.
///
/// # Specification
/// - provides: the answer of [`Scheduled::phase`].
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Phase
{
    /// Its tasks take its jobs.
    Running,
    /// Its calling thread left it, so no task starts another job.
    Ended,
}

impl<Job, Out, Run> Scheduled<Job, Out, Run>
{
    /// End the schedule, so that each task ends at its next poll and none
    /// starts another job.
    ///
    /// # Specification
    /// - ensures: the end is set.
    /// - panics: none.
    /// - executable: none — each task reads the end on its own thread, after
    ///   the call returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    fn end(&self)
    {
        self.ended.store(true, Ordering::Release);
    }

    /// Whether the schedule runs or has ended.
    ///
    /// # Specification
    /// trivial.
    fn phase(&self) -> Phase
    {
        if self.ended.load(Ordering::Acquire) {
            Phase::Ended
        }
        else {
            Phase::Running
        }
    }
}

impl<Job, Out, Run> Scheduled<Job, Out, Run>
where
    Job: Send,
    Out: Send,
    Run: Fn(ItemIndex, Job) -> Out + Sync,
{
    /// A schedule on one lane for each of `tasks` threads, whose jobs `run`
    /// runs, and the calling thread's ledger of it, with room for a job of
    /// each of `items`.
    ///
    /// # Specification
    /// - ensures: one lane and one feed for each task, each lane empty and its
    ///   claim free, and room kept for a job of every item, so no later
    ///   hand-off allocates. No task runs yet.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    #[spec(ensures: |ret| ret.0.lanes.len() == NonZeroUsize::from(tasks).get()
        && ret.1.feeds.len() == NonZeroUsize::from(tasks).get()
        && ret.1.room == NonZeroUsize::from(tasks).get()
        && ret.1.kept.capacity() >= items.len())]
    fn new<Item>(
        tasks: Threads,
        items: &[Item],
        run: Run,
        spin: Spin,
    ) -> (Self, Ledger<Job, Out>)
    {
        let lanes_count = NonZeroUsize::from(tasks).get();
        let (lanes, feeds) = core::iter::repeat_with(lane::open)
            .take(lanes_count)
            .unzip();
        (
            Self {
                lanes,
                caller: Sleeper::of(std::thread::current()),
                run,
                spin,
                ended: AtomicBool::new(false),
            },
            Ledger {
                feeds,
                busy: Vec::with_capacity(lanes_count),
                room: lanes_count,
                kept: VecDeque::with_capacity(items.len()),
                turn: 0,
            },
        )
    }

    /// Release each item of `items` in slice order and commit each item as
    /// its job returns, both on the calling thread. A lane's task starts when
    /// the calling thread hands the lane a job.
    ///
    /// # Specification
    /// - ensures: `release` ran on every item in slice order, each first time
    ///   once `waiting` counts no item that it waits on and fewer than
    ///   [`DEPTH`] + 1 released jobs for each lane were not committed. A
    ///   release that answered [`Releasing::Held`] while a released job was not
    ///   committed ran again once every released job was committed. `commit`
    ///   ran once on every item, with its job's result as the job returned, or
    ///   with the result of its release. Each commit counts down the items that
    ///   wait on the committed one. After a release holds while a job runs, the
    ///   schedule runs as a chain: the calling thread keeps each job that a
    ///   release gives and runs it, and it tries a release beside a running job
    ///   once in [`CHAIN_PROBE`] releases. A release that gives a job beside a
    ///   running job ends the chain. Out of a chain, after each release that
    ///   gives a job, and after each result, the calling thread hands kept jobs
    ///   to lanes with room. While it can neither release nor commit, it runs
    ///   its oldest kept job, or else a job of a lane whose task does not run,
    ///   or else it waits for a result. Once the call returns, each task ends.
    /// - panics: the first panic of `release`, of a job or of `commit`, after
    ///   it ends the schedule so that no task starts another job.
    /// - executable: none — each release and commit is a call of the caller's
    ///   closure, and the call returns nothing for a postcondition to compare.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_job_that_returns_first_commits_first`
    /// - witness: `pool::tests::a_held_release_waits_until_every_running_job_is_committed`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    /// - witness: `pool::tests::a_chained_schedule_runs_its_jobs_on_the_calling_thread`
    /// - witness: `pool::tests::a_schedule_releases_at_most_a_window_ahead_of_its_commits_7299`
    fn drive<'scope, Item, Release, Commit>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
        mut ledger: Ledger<Job, Out>,
        items: &mut [Item],
        mut waiting: Waiting,
        (release, commit): (&mut Release, &mut Commit),
    ) where
        Job: 'scope,
        Out: 'scope,
        Run: 'scope,
        Release: FnMut(gandr_core_fork::ItemIndex, &mut Item) -> Releasing<Job, Out>,
        Commit: FnMut(gandr_core_fork::ItemIndex, &mut Item, Out),
    {
        let _ending = Ending(self);
        let count = items.len();
        // The next item to release, the released jobs that are not committed,
        // the items committed, whether a release holds, whether the schedule
        // runs as a chain, and the releases that the chain put off since its
        // last try.
        let mut next = ItemIndex(0);
        let mut outstanding = 0_usize;
        let mut committed = 0_usize;
        let mut holding = false;
        let mut chained = false;
        let mut put_off = 0_usize;
        // Each released job holds what its run reads until its commit, a
        // check's view of the environment among them. So the releases run
        // ahead of the commits by at most a full lane and one more job for
        // each lane, and what they hold stays a bound of the width (#7299).
        let window = self.lanes.len().saturating_mul(DEPTH.saturating_add(1));
        let mut commit_one =
            |position: ItemIndex, item: &mut Item, out: Out, waiting: &mut Waiting| {
                let place = gandr_core_fork::ItemIndex::from(position.0);
                if let Err(panic) =
                    std::panic::catch_unwind(AssertUnwindSafe(|| commit(place, item, out)))
                {
                    self.stop(panic);
                }
                waiting.commit(position);
            };
        while committed < count {
            while !holding && outstanding < window && waiting.free(next) == Released::Free {
                // A chain releases beside a running job only once in
                // `CHAIN_PROBE` releases: each other try stages the item and
                // then gives the staging back.
                if chained && outstanding > 0 {
                    put_off = put_off.saturating_add(1);
                    if put_off < CHAIN_PROBE {
                        break;
                    }
                    put_off = 0;
                }
                let Some(item) = items.get_mut(next.0)
                else {
                    break;
                };
                let place = gandr_core_fork::ItemIndex::from(next.0);
                let released =
                    std::panic::catch_unwind(AssertUnwindSafe(|| release(place, &mut *item)))
                        .unwrap_or_else(|panic| self.stop(panic));
                match released {
                    Releasing::Run(job) => {
                        if outstanding > 0 {
                            chained = false;
                        }
                        ledger.kept.push_back((next, job));
                        outstanding = outstanding.saturating_add(1);
                        next = ItemIndex(next.0.saturating_add(1));
                        if !chained {
                            self.hand(scope, &mut ledger);
                        }
                    },
                    Releasing::Held(_) if outstanding > 0 => {
                        chained = true;
                        holding = true;
                    },
                    Releasing::Settled(out) | Releasing::Held(out) => {
                        commit_one(next, item, out, &mut waiting);
                        committed = committed.saturating_add(1);
                        next = ItemIndex(next.0.saturating_add(1));
                    },
                }
            }
            if committed >= count {
                break;
            }
            // Commit each result that has come back, lane by lane.
            let mut returned = 0_usize;
            let mut at = 0_usize;
            while let Some(&lane) = ledger.busy.get(at) {
                let mut held = 0_usize;
                if let Some(feed) = ledger.feeds.get_mut(lane) {
                    while let Ok(returning) = feed.results.pop() {
                        if feed.held == DEPTH {
                            ledger.room = ledger.room.saturating_add(1);
                        }
                        feed.held = feed.held.saturating_sub(1);
                        let (position, out) = returning.unwrap_or_else(|panic| self.stop(panic));
                        if let Some(item) = items.get_mut(position.0) {
                            commit_one(position, item, out, &mut waiting);
                        }
                        returned = returned.saturating_add(1);
                    }
                    held = feed.held;
                }
                if held == 0 {
                    ledger.busy.swap_remove(at);
                }
                else {
                    at = at.saturating_add(1);
                }
            }
            if returned > 0 {
                committed = committed.saturating_add(returned);
                outstanding = outstanding.saturating_sub(returned);
                if outstanding == 0 {
                    holding = false;
                }
                if !chained {
                    self.hand(scope, &mut ledger);
                }
                continue;
            }
            // Neither a release nor a commit is possible: run a job here, or
            // wait for one to return.
            if let Some((position, job)) = ledger.kept.pop_front() {
                let (position, out) = self
                    .run(position, job)
                    .unwrap_or_else(|panic| self.stop(panic));
                if let Some(item) = items.get_mut(position.0) {
                    commit_one(position, item, out, &mut waiting);
                }
                committed = committed.saturating_add(1);
                outstanding = outstanding.saturating_sub(1);
                if outstanding == 0 {
                    holding = false;
                }
            }
            else if self.take(scope, &ledger) == Taken::Idle {
                self.wait(&ledger);
            }
        }
    }

    /// Hand the jobs that the calling thread keeps to lanes with room: first
    /// one job to each lane that holds none, then more to each lane up to
    /// [`DEPTH`], each try from the lane after the last one tried.
    ///
    /// # Specification
    /// - ensures: the oldest kept jobs move to lanes in release order, and no
    ///   lane holds more than [`DEPTH`] jobs, so no push is refused. Each lane
    ///   handed a job while no task attends it gets a task, so a job runs while
    ///   the calling thread releases.
    /// - panics: none.
    /// - executable: none — a task may take a handed job before a postcondition
    ///   reads its lane.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_job_that_returns_first_commits_first`
    fn hand<'scope>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
        ledger: &mut Ledger<Job, Out>,
    ) where
        Job: 'scope,
        Out: 'scope,
        Run: 'scope,
    {
        let lanes = ledger.feeds.len();
        for depth in 1 ..= DEPTH {
            let mut tried = 0_usize;
            while tried < lanes
                && ledger.room > 0
                && (depth > 1 || ledger.busy.len() < lanes)
                && !ledger.kept.is_empty()
            {
                let lane = ledger.turn;
                ledger.turn = lane
                    .checked_add(1)
                    .filter(|&after| after < lanes)
                    .unwrap_or_default();
                tried = tried.saturating_add(1);
                let Some(feed) = ledger.feeds.get_mut(lane).filter(|feed| feed.held < depth)
                else {
                    continue;
                };
                let Some(ready) = ledger.kept.pop_front()
                else {
                    break;
                };
                if let Err(rtrb::PushError::Full(ready)) = feed.jobs.push(ready) {
                    ledger.kept.push_front(ready);
                    continue;
                }
                tried = 0;
                if feed.held == 0 {
                    ledger.busy.push(lane);
                }
                feed.held = feed.held.saturating_add(1);
                if feed.held == DEPTH {
                    ledger.room = ledger.room.saturating_sub(1);
                }
                if let Some(shared) = self.lanes.get(lane)
                    && shared.attendance() == Attendance::Unattended
                {
                    self.start(scope, shared);
                }
            }
        }
    }

    /// Start a task for `lane`, unless a task attends it already.
    ///
    /// # Specification
    /// - ensures: when no task attended the lane, the lane is attended and one
    ///   task for it is spawned on `scope`.
    /// - panics: none.
    /// - executable: none — the task may leave the lane before a postcondition
    ///   reads it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a schedule whose tasks leave their empty lanes and
    ///   start again when the calling thread hands them jobs ends with each job
    ///   committed once.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
    fn start<'scope>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
        lane: &'scope Lane<Ready<Job>, Returned<Out>>,
    ) where
        Job: 'scope,
        Out: 'scope,
        Run: 'scope,
    {
        if lane.attend() == Attendance::Unattended {
            scope.spawn(move |_scope| self.work(lane));
        }
    }

    /// Run one job of a lane whose task does not run it, on the calling
    /// thread, and hand its result back on the lane. When more than one lane
    /// holds such a job, first start a task for each of the others.
    ///
    /// # Specification
    /// - ensures: [`Taken::Ran`] exactly when the calling thread took a free
    ///   claim of a lane, ran its oldest job, and pushed the result onto the
    ///   lane's ring of results.
    /// - panics: none; a panic of the job is the result.
    /// - executable: none — the lane's task may take the claim back as soon as
    ///   the call returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a schedule inside a scheduled job, whose tasks no
    ///   pool thread starts, ends with each job run on the calling thread.
    /// - witness: `pool::tests::a_schedule_inside_a_scheduled_job_ends`
    /// - witness: `pool::tests::a_job_that_returns_first_commits_first`
    fn take<'scope>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
        ledger: &Ledger<Job, Out>,
    ) -> Taken
    where
        Job: 'scope,
        Out: 'scope,
        Run: 'scope,
    {
        let mut first = None;
        for &lane in &ledger.busy {
            let (Some(feed), Some(shared)) = (ledger.feeds.get(lane), self.lanes.get(lane))
            else {
                continue;
            };
            if shared.tending(feed) == Tending::Tended {
                continue;
            }
            match first {
                None => first = Some(shared),
                Some(_) => self.start(scope, shared),
            }
        }
        let Some(mut claim) = first.and_then(Lane::claim)
        else {
            return Taken::Idle;
        };
        let runner = claim.runner();
        let Ok((position, job)) = runner.jobs.pop()
        else {
            return Taken::Idle;
        };
        let returning = self.run(position, job);
        let refused = runner.results.push(returning).is_err();
        debug_assert!(
            !refused,
            "a lane's ring of results holds a slot for each job that the lane holds"
        );
        Taken::Ran
    }

    /// Wait until a result comes back, or until a lane holds a job that no
    /// task runs: poll up to the spin budget, then park.
    ///
    /// # Specification
    /// - ensures: returns once a busy lane's ring of results holds a result, or
    ///   a busy lane holds a job with its claim free. A task that pushes a
    ///   result wakes the calling thread if it parks.
    /// - panics: none.
    /// - executable: none — the condition is the tasks' writes, which may
    ///   change before a postcondition reads them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_held_release_waits_until_every_running_job_is_committed`
    fn wait(
        &self,
        ledger: &Ledger<Job, Out>,
    )
    {
        let ready = || {
            ledger.busy.iter().any(|&lane| {
                ledger.feeds.get(lane).is_some_and(|feed| {
                    !feed.results.is_empty()
                        || self
                            .lanes
                            .get(lane)
                            .is_some_and(|shared| shared.tending(feed) == Tending::Stranded)
                })
            })
        };
        let mut polls = 0_u32;
        while polls < self.spin.0 {
            if ready() {
                return;
            }
            polls = polls.saturating_add(1);
            core::hint::spin_loop();
        }
        self.caller.sleep(ready);
    }

    /// The task of `lane`: run the lane's jobs while it holds the lane's
    /// claim and hand each result back, and poll up to the spin budget when
    /// the lane is empty. Then give the claim back, leave the lane and end,
    /// so that the worker goes back to the pool.
    ///
    /// # Specification
    /// - ensures: each job that the task takes runs once, and its result goes
    ///   back on the lane, with a wake of the calling thread if it parks. The
    ///   task holds the claim only while it runs or polls, starts no job once
    ///   the end is set, and never parks. When it ends, either the lane is
    ///   unattended, or another task attends it. A job that the calling thread
    ///   hands after the last poll either shows to the task, which takes the
    ///   lane back, or the calling thread reads the lane unattended. A task
    ///   that ends wakes the calling thread after it gives its last claim back,
    ///   so a calling thread that read the claim held reads it again.
    /// - panics: none; a panic of a job is its result.
    /// - executable: none — the task runs after the spawn returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`, and a schedule whose jobs
    ///   fork again on the same pool.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_pool_schedules_on_its_own_threads_and_commits_on_the_caller`
    /// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
    fn work(
        &self,
        lane: &Lane<Ready<Job>, Returned<Out>>,
    )
    {
        loop {
            if let Some(mut claim) = lane.claim() {
                let mut polls = 0_u32;
                while self.phase() == Phase::Running {
                    let runner = claim.runner();
                    if let Ok((position, job)) = runner.jobs.pop() {
                        let returning = self.run(position, job);
                        let refused = runner.results.push(returning).is_err();
                        debug_assert!(
                            !refused,
                            "a lane's ring of results holds a slot for each job that the lane holds"
                        );
                        self.caller.wake();
                        polls = 0;
                    }
                    else if polls < self.spin.0 {
                        polls = polls.saturating_add(1);
                        core::hint::spin_loop();
                    }
                    else {
                        break;
                    }
                }
            }
            lane.leave();
            // A job that the calling thread handed after the last poll shows
            // here, or the calling thread reads the lane unattended and runs
            // the job or starts a task for it.
            let handed = self.phase() == Phase::Running
                && lane
                    .claim()
                    .is_some_and(|mut claim| !claim.runner().jobs.is_empty());
            if !handed || lane.attend() == Attendance::Attended {
                // The calling thread may have read the lane claimed and
                // parked: it reads the lane again, and runs a job that waits
                // there.
                self.caller.wake();
                return;
            }
        }
    }

    /// End the schedule, then resume `panic`.
    ///
    /// # Specification
    /// - ensures: never returns.
    /// - panics: always, with `panic`.
    /// - executable: none — the call never returns, so no postcondition runs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a job that panics while later jobs wait on it.
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    fn stop(
        &self,
        panic: Box<dyn Any + Send>,
    ) -> !
    {
        self.end();
        std::panic::resume_unwind(panic)
    }

    /// Run the job of the item at `position`.
    ///
    /// # Specification
    /// - ensures: the item's place and the job's result, once the job has
    ///   returned; or the panic of the job.
    /// - panics: none; a panic of the job is returned.
    /// - executable: none — the result is the caller's closure's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    fn run(
        &self,
        position: ItemIndex,
        job: Job,
    ) -> Returned<Out>
    {
        let out = std::panic::catch_unwind(AssertUnwindSafe(|| (self.run)(position, job)))?;
        Ok((position, out))
    }
}

/// Why the driver's pool could not start.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct PoolFault(Arc<rayon::ThreadPoolBuildError>);

impl fmt::Display for PoolFault
{
    /// Name the pool's error.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "the worker pool did not start: {}", self.0)
    }
}

impl core::error::Error for PoolFault
{
}

#[cfg(test)]
mod tests
{
    use core::hint;
    use core::num::NonZeroUsize;
    use core::panic::AssertUnwindSafe;
    use core::sync::atomic::AtomicBool;
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering;
    use core::time::Duration;
    use std::sync::Condvar;
    use std::sync::Mutex;
    use std::thread::ThreadId;
    use std::time::Instant;

    use gandr_core_fork::Dependence;
    use gandr_core_fork::Dependences;
    use gandr_core_fork::Fork as _;
    use gandr_core_fork::Releasing;
    use gandr_core_fork::Scoped;
    use gandr_core_fork::Spawn;
    use gandr_core_fork::Unwound;
    use quenchant_shape::shape::Maybe;

    use super::CHAIN_PROBE;
    use super::DEPTH;
    use super::Forked;
    use super::Pool;
    use super::Spin;
    use super::alone;
    use crate::width::Threads;
    use crate::width::Width;

    /// A job that ignores its spawner: a closure, run once.
    #[repr(transparent)]
    struct Job<Run>(Run);

    impl<'scope, Run, Output> Scoped<'scope> for Job<Run>
    where
        Run: FnOnce() -> Output,
    {
        type Output = Output;

        /// Run the closure.
        ///
        /// # Specification
        /// trivial.
        fn run<Spawner>(
            self,
            _spawner: &Spawner,
        ) -> Output
        where
            Spawner: Spawn<'scope>,
        {
            (self.0)()
        }
    }

    /// The sum of a spawn tree's leaves.
    #[derive(Debug, Eq, PartialEq)]
    #[repr(transparent)]
    struct Sum(u64);

    /// A leaf of a spawn tree: its own value.
    #[repr(transparent)]
    struct Leaf(u64);

    impl<'scope> Scoped<'scope> for Leaf
    {
        type Output = Sum;

        /// The leaf's value.
        ///
        /// # Specification
        /// trivial.
        fn run<Spawner>(
            self,
            _spawner: &Spawner,
        ) -> Sum
        where
            Spawner: Spawn<'scope>,
        {
            Sum(self.0)
        }
    }

    /// A node of a spawn tree: two subtrees, each spawned before either is
    /// waited for.
    struct Pair<Tree>(Tree, Tree);

    impl<'scope, Tree> Scoped<'scope> for Pair<Tree>
    where
        Tree: Scoped<'scope, Output = Sum> + Send + 'scope,
    {
        type Output = Sum;

        /// Spawn both subtrees, wait for the right one and then the left one,
        /// and add their sums.
        ///
        /// # Specification
        /// trivial.
        fn run<Spawner>(
            self,
            spawner: &Spawner,
        ) -> Sum
        where
            Spawner: Spawn<'scope>,
        {
            let Self(left, right) = self;
            let left = spawner.spawn(left);
            let Sum(right) = spawner.wait(spawner.spawn(right)).unwrap();
            let Sum(left) = spawner.wait(left).unwrap();
            Sum(left.checked_add(right).unwrap())
        }
    }

    /// The flags that a scope's jobs raise for one another.
    #[derive(Default)]
    struct Flags
    {
        /// The first long job has started.
        started: AtomicBool,
        /// The job spawned after the first long job has run.
        released: AtomicBool,
        /// The second long job has started.
        occupied: AtomicBool,
        /// The body has let the second long job end.
        freed: AtomicBool,
        /// How many of the two untaken jobs have run.
        turns: AtomicUsize,
        /// How many times the job whose handle was dropped ran.
        dropped: AtomicUsize,
    }

    /// What the waiting witness saw.
    #[derive(Debug)]
    struct Seen
    {
        /// The worker the body ran on.
        worker: ThreadId,
        /// The first long job saw its release.
        released: bool,
        /// The worker the release ran on.
        release_ran_on: ThreadId,
        /// The older untaken job's turn among the two, and its worker.
        older: (usize, ThreadId),
        /// The second long job saw its freeing.
        freed: bool,
    }

    /// The body of the waiting witness, on a pool of two threads.
    #[repr(transparent)]
    struct Waits<'flags>(&'flags Flags);

    impl<'scope, 'flags: 'scope> Scoped<'scope> for Waits<'flags>
    {
        type Output = Seen;

        /// Wait for a job that waits for a later spawn, for the older of two
        /// jobs that no worker took, and for a long job, and drop a handle
        /// unwaited. Answer what each wait saw.
        ///
        /// # Specification
        /// trivial.
        fn run<Spawner>(
            self,
            spawner: &Spawner,
        ) -> Seen
        where
            Spawner: Spawn<'scope>,
        {
            let flags = self.0;
            let raised = |flag: &AtomicBool| {
                let deadline = Instant::now().checked_add(Duration::from_secs(10)).unwrap();
                while !flag.load(Ordering::Acquire) {
                    if Instant::now() > deadline {
                        return false;
                    }
                    hint::spin_loop();
                }
                true
            };
            let worker = std::thread::current().id();
            let first = spawner.spawn(Job(move || {
                flags.started.store(true, Ordering::Release);
                raised(&flags.released)
            }));
            assert!(raised(&flags.started), "the other worker takes the job");
            let release = spawner.spawn(Job(move || {
                flags.released.store(true, Ordering::Release);
                std::thread::current().id()
            }));
            let released = spawner.wait(first).unwrap();
            let release_ran_on = spawner.wait(release).unwrap();
            let second = spawner.spawn(Job(move || {
                flags.occupied.store(true, Ordering::Release);
                raised(&flags.freed)
            }));
            assert!(raised(&flags.occupied), "the other worker takes the job");
            let untaken = || {
                Job(move || {
                    (
                        flags.turns.fetch_add(1, Ordering::Relaxed),
                        std::thread::current().id(),
                    )
                })
            };
            let (older, newer) = (spawner.spawn(untaken()), spawner.spawn(untaken()));
            let older = spawner.wait(older).unwrap();
            spawner.wait(newer).unwrap();
            drop(spawner.spawn(Job(move || {
                flags.dropped.fetch_add(1, Ordering::Relaxed);
            })));
            flags.freed.store(true, Ordering::Release);
            let freed = spawner.wait(second).unwrap();
            Seen {
                worker,
                released,
                release_ran_on,
                older,
                freed,
            }
        }
    }

    /// The body of the unwinding witness, on a pool of two threads.
    #[repr(transparent)]
    struct Unwinds<'flags>(&'flags Flags);

    impl<'scope, 'flags: 'scope> Scoped<'scope> for Unwinds<'flags>
    {
        type Output = ();

        /// Wait for a job that panics on the other worker, and record in
        /// `released` whether the wait answered [`Unwound`].
        ///
        /// # Specification
        /// trivial.
        fn run<Spawner>(
            self,
            spawner: &Spawner,
        ) where
            Spawner: Spawn<'scope>,
        {
            let flags = self.0;
            let panics = spawner.spawn(Job(move || {
                flags.started.store(true, Ordering::Release);
                panic!("the job panics on another worker");
            }));
            while !flags.started.load(Ordering::Acquire) {
                hint::spin_loop();
            }
            flags
                .released
                .store(spawner.wait(panics) == Err(Unwound), Ordering::Release);
        }
    }

    #[test]
    fn nested_spawns_sum_the_leaves_at_every_width()
    {
        let leaf = |first: u64, offset: u64| Leaf(first.checked_add(offset).unwrap());
        let pair = |first: u64| Pair(leaf(first, 0), leaf(first, 1));
        let quad = |first: u64| Pair(pair(first), pair(first.checked_add(2).unwrap()));
        let octet = |first: u64| Pair(quad(first), quad(first.checked_add(4).unwrap()));
        for threads in [1_usize, 2, 4] {
            let pool = Pool::new(Width::Threads(Threads::from(
                NonZeroUsize::new(threads).unwrap(),
            )));
            assert_eq!(
                pool.scope(Pair(octet(1), octet(9))),
                Sum(136),
                "the leaves 1 to 16 sum at {threads} threads"
            );
        }
    }

    #[test]
    fn a_wait_runs_its_job_here_or_helps_until_it_ends()
    {
        let flags = Flags::default();
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::MIN.saturating_add(1),
        )));
        let seen = pool.scope(Waits(&flags));
        assert!(seen.released, "the first long job sees its release");
        assert_eq!(
            seen.release_ran_on, seen.worker,
            "the release runs on the worker that waits and helps"
        );
        assert_eq!(
            seen.older,
            (0, seen.worker),
            "the older untaken job runs first, at its wait"
        );
        assert!(seen.freed, "the second long job sees its freeing");
        assert_eq!(
            flags.dropped.load(Ordering::Relaxed),
            0,
            "a job whose handle was dropped untaken never runs"
        );
    }

    #[test]
    fn a_job_that_panics_elsewhere_ends_its_wait()
    {
        let flags = Flags::default();
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::MIN.saturating_add(1),
        )));
        let unwound = std::panic::catch_unwind(AssertUnwindSafe(|| pool.scope(Unwinds(&flags))));
        assert!(
            flags.released.load(Ordering::Acquire),
            "the wait answers that the job unwound"
        );
        let payload = unwound.expect_err("the scope resumes the job's panic");
        assert_eq!(
            payload.downcast_ref::<&str>(),
            Some(&"the job panics on another worker"),
            "the panic is the job's own"
        );
    }

    #[test]
    fn a_serial_pool_starts_no_thread()
    {
        let many = [(); 64];
        let pool = Pool::new(Width::SERIAL);
        assert!(matches!(
            pool.helpers(&many),
            Maybe::Absent(alone::Absent::Serial)
        ));
        assert!(matches!(pool.forked(), Ok(Forked::Serial)));
        let wide = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::MIN.saturating_add(3),
        )));
        assert!(matches!(
            wide.helpers(&many[.. 1]),
            Maybe::Absent(alone::Absent::Serial)
        ));
        assert!(
            wide.started.get().is_none(),
            "a fork of one item starts no thread"
        );
        let helpers = |items: &[()]| match wide.helpers(items) {
            Maybe::Present((_, helpers)) => NonZeroUsize::from(helpers).get(),
            Maybe::Absent(_) => 0,
        };
        assert_eq!(helpers(&many[.. 2]), 1);
        assert_eq!(helpers(&many), 3);
    }

    #[test]
    fn a_pool_visits_each_item_once_from_a_state_per_busy_worker()
    {
        let workers = 4_usize;
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(workers).unwrap(),
        )));
        let Ok(Forked::Pooled(threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        for count in [0_usize, 1, 3, 64] {
            let made = AtomicUsize::new(0);
            let mut visits = vec![0_usize; count];
            threads.install(|| {
                fork.each(
                    &mut visits,
                    || {
                        made.fetch_add(1, Ordering::Relaxed);
                    },
                    |_state, visited| *visited = visited.checked_add(1).unwrap(),
                );
            });
            assert!(visits.iter().all(|&visited| visited == 1), "{count} items");
            let made = made.load(Ordering::Relaxed);
            assert_eq!(made == 0, count == 0, "{count} items");
            assert!(
                made <= count.min(workers),
                "{made} states for {count} items"
            );
        }
    }

    /// A stage of one item runs on the calling thread, and a stage of many on
    /// the pool's workers alone: called from outside any pool, no item of a
    /// wide stage runs on the caller.
    #[test]
    fn one_item_runs_on_the_caller_and_many_on_the_workers()
    {
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let Ok(Forked::Pooled(_threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        let caller = std::thread::current().id();
        for (count, on_caller) in [(1_usize, true), (64, false)] {
            let mut ran: Vec<Option<std::thread::ThreadId>> = vec![None; count];
            fork.each(
                &mut ran,
                || (),
                |_state, ran| {
                    *ran = Some(std::thread::current().id());
                },
            );
            assert!(
                ran.iter()
                    .all(|ran| ran.is_some_and(|thread| (thread == caller) == on_caller)),
                "{count} items run on the caller: {on_caller}"
            );
        }
    }

    /// The pool forked as a consumer forks it: many items run on the pool's
    /// own threads, one item runs on the caller and starts nothing, and a
    /// serial pool keeps every item on the caller. A join gives its halves'
    /// results in argument order at either width.
    #[test]
    fn a_pool_forks_on_its_own_threads()
    {
        let caller = std::thread::current().id();
        let wide = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let mut one = [None];
        wide.each(
            &mut one,
            || (),
            |_state, ran| *ran = Some(std::thread::current().id()),
        );
        assert_eq!(one, [Some(caller)], "one item runs on the caller");
        assert!(
            wide.started.get().is_none(),
            "a fork of one item starts no thread"
        );
        let inside = || matches!(wide.forked(), Ok(Forked::Pooled(threads, _)) if threads.current_thread_index().is_some());
        let mut many = [false; 64];
        wide.each(&mut many, || (), |_state, ran| *ran = inside());
        assert!(
            many.iter().all(|&ran| ran),
            "every item runs on the pool's own threads"
        );
        assert_eq!(
            wide.join(|| ('l', inside()), || ('r', inside())),
            (('l', true), ('r', true)),
            "both halves run on the pool, in argument order"
        );
        let serial = Pool::default();
        let mut ran = [None; 8];
        serial.each(
            &mut ran,
            || (),
            |_state, ran| *ran = Some(std::thread::current().id()),
        );
        assert!(
            ran.iter().all(|&ran| ran == Some(caller)),
            "a serial pool keeps every item on the caller"
        );
        let here = || std::thread::current().id() == caller;
        assert_eq!(
            serial.join(|| ('l', here()), || ('r', here())),
            (('l', true), ('r', true)),
            "a serial join runs both halves on the caller, in argument order"
        );
    }

    /// A join's right half waits for a signal that its left half gives. On a
    /// wide pool and on a serial one, the right half sees the signal.
    #[test]
    fn a_right_half_may_wait_for_the_left_one()
    {
        let wide = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        for pool in [wide, Pool::default()] {
            let (given, signalled) = (Mutex::new(false), Condvar::new());
            let ((), seen) = pool.join(
                || {
                    *given.lock().unwrap() = true;
                    signalled.notify_all();
                },
                || {
                    let (seen, waited) = signalled
                        .wait_timeout_while(
                            given.lock().unwrap(),
                            Duration::from_secs(60),
                            |given| !*given,
                        )
                        .unwrap();
                    *seen && !waited.timed_out()
                },
            );
            assert!(
                seen,
                "the right half sees the left half's signal at {:?}",
                pool.width()
            );
        }
    }

    /// One item of a schedule: the clock and the thread at each of its
    /// releases, and the clock, the thread and the job's stamps at each of
    /// its commits.
    #[derive(Debug, Default)]
    struct Stamped
    {
        /// The clock and the thread at each release.
        releases: Vec<(usize, ThreadId)>,
        /// The clock, the thread, and the clocks at the job's start and
        /// return, at each commit.
        commits: Vec<(usize, ThreadId, (usize, usize))>,
    }

    #[test]
    fn a_schedule_releases_in_order_and_commits_each_job_as_it_returns()
    {
        let width = Width::Threads(Threads::from(NonZeroUsize::new(4_usize).unwrap()));
        let pools = [
            ("parking", Pool::new(width)),
            ("spinning", Pool::new(width).spinning(Spin::from(10_000))),
        ];
        // The edges of a chain and of a scattered fan over `count` items. The
        // fan also holds one edge past the slice.
        let graphs = |count: usize| {
            let chain: Vec<Dependence> = (1 .. count)
                .map(|later| Dependence {
                    before: later.checked_sub(1).unwrap(),
                    after: later,
                })
                .collect();
            let fan: Vec<Dependence> = (1 .. count)
                .flat_map(|later| {
                    let scattered = later
                        .checked_mul(37)
                        .and_then(|scaled| scaled.checked_add(11))
                        .and_then(|shifted| shifted.checked_rem(later))
                        .unwrap();
                    [
                        Dependence {
                            before: later.checked_div(2).unwrap(),
                            after: later,
                        },
                        Dependence {
                            before: scattered,
                            after: later,
                        },
                    ]
                })
                .chain([Dependence {
                    before: count,
                    after: count.checked_add(3).unwrap(),
                }])
                .collect();
            [
                ("no edge", Dependences::default()),
                ("a chain", Dependences::new(chain).unwrap()),
                ("a scattered fan", Dependences::new(fan).unwrap()),
            ]
        };
        for (count, &(budget, ref pool)) in [0_usize, 1, 2, 7, 64]
            .into_iter()
            .flat_map(|count| pools.iter().map(move |pool| (count, pool)))
        {
            let Ok(Forked::Pooled(threads, fork)) = pool.forked()
            else {
                panic!("a pool of four threads starts");
            };
            for (graph, after) in graphs(count) {
                let clock = AtomicUsize::new(0);
                let tick = || clock.fetch_add(1, Ordering::SeqCst);
                let runs: Vec<AtomicUsize> = core::iter::repeat_with(|| AtomicUsize::new(0))
                    .take(count)
                    .collect();
                let mut items: Vec<Stamped> = core::iter::repeat_with(Stamped::default)
                    .take(count)
                    .collect();
                let caller = threads.install(|| {
                    fork.schedule(
                        &mut items,
                        &after,
                        |position, item| {
                            item.releases.push((tick(), std::thread::current().id()));
                            Releasing::<usize, (usize, usize)>::Run(usize::from(position))
                        },
                        |job| {
                            let started = tick();
                            runs[job].fetch_add(1, Ordering::SeqCst);
                            std::thread::yield_now();
                            (started, tick())
                        },
                        |_position, item, stamps| {
                            item.commits
                                .push((tick(), std::thread::current().id(), stamps));
                        },
                    );
                    std::thread::current().id()
                });
                let case = format!("{graph} over {count} items, {budget}");
                for (position, item) in items.iter().enumerate() {
                    assert_eq!(
                        runs[position].load(Ordering::SeqCst),
                        1,
                        "{case}: item {position}'s job runs once"
                    );
                    let [(released, by)] = item.releases[..]
                    else {
                        panic!("{case}: item {position} is released once");
                    };
                    let [(committed, on, (started, returned))] = item.commits[..]
                    else {
                        panic!("{case}: item {position} is committed once");
                    };
                    assert!(
                        released < started && returned < committed,
                        "{case}: item {position}'s job runs after its release and before its commit"
                    );
                    assert_eq!(
                        (by, on),
                        (caller, caller),
                        "{case}: item {position} is released and committed on the calling thread"
                    );
                }
                for pair in items.windows(2) {
                    let [ref first, ref second] = *pair
                    else {
                        panic!("{case}: a window of two holds two items");
                    };
                    assert!(
                        first.releases[0].0 < second.releases[0].0,
                        "{case}: releases in slice order"
                    );
                }
                for &Dependence {
                    before,
                    after: later,
                } in after.edges().iter().filter(|edge| edge.after < count)
                {
                    assert!(
                        items[later].releases[0].0 > items[before].commits[0].0,
                        "{case}: item {later} is released after item {before} is committed"
                    );
                }
            }
        }
    }

    /// A scheduled job that schedules again on the same pool: the tasks of
    /// the inner schedule wait behind the tasks that the outer schedule
    /// holds, so the inner calling thread runs their jobs, and both schedules
    /// end.
    #[test]
    fn a_schedule_inside_a_scheduled_job_ends()
    {
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let Ok(Forked::Pooled(_threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        let release = |position: gandr_core_fork::ItemIndex, _item: &mut usize| {
            Releasing::<usize, usize>::Run(usize::from(position))
        };
        let mut outer = [0_usize; 8];
        pool.schedule(
            &mut outer,
            &Dependences::default(),
            release,
            |job| {
                let mut inner = [0_usize; 16];
                fork.schedule(
                    &mut inner,
                    &Dependences::default(),
                    release,
                    |inner_job| inner_job,
                    |_position, item, out| *item = out,
                );
                inner.iter().sum::<usize>().checked_add(job).unwrap()
            },
            |_position, item, out| *item = out,
        );
        let inner = (0 .. 16_usize).sum::<usize>();
        let expected: [usize; 8] = core::array::from_fn(|job| inner.checked_add(job).unwrap());
        assert_eq!(
            outer, expected,
            "each outer job runs its inner schedule to its end"
        );
    }

    /// A scheduled job that forks again on the same pool: no task parks on its
    /// worker, so the share of the inner fork finds a worker, and every round
    /// ends.
    #[test]
    fn a_schedule_whose_jobs_fork_again_ends()
    {
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let expected: [usize; 16] = core::array::from_fn(|job| job.checked_add(8).unwrap());
        for _round in 0 .. 200_usize {
            let mut outer = [0_usize; 16];
            pool.schedule(
                &mut outer,
                &Dependences::default(),
                |position: gandr_core_fork::ItemIndex, _item: &mut usize| {
                    Releasing::<usize, usize>::Run(usize::from(position))
                },
                |job| {
                    let mut inner = [0_usize; 8];
                    pool.each(
                        &mut inner,
                        || (),
                        |_state: &mut (), item: &mut usize| *item = 1,
                    );
                    inner.iter().sum::<usize>().checked_add(job).unwrap()
                },
                |_position, item, out| *item = out,
            );
            assert_eq!(
                outer, expected,
                "each job's inner fork visits each of its items once"
            );
        }
    }

    #[test]
    fn a_job_that_returns_first_commits_first()
    {
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let Ok(Forked::Pooled(threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        // Item 1 is released once the job of item 0 runs on a task, so the
        // calling thread never runs that job. The job of item 0 then waits
        // until item 1 is committed, which a commit in slice order never
        // reaches: there each wait gives up after five seconds.
        let patience = Duration::from_secs(5);
        let wait = |flag: &AtomicBool| {
            let start = Instant::now();
            while !flag.load(Ordering::SeqCst) {
                if start.elapsed() > patience {
                    return false;
                }
                std::thread::yield_now();
            }
            true
        };
        let (started, first) = (AtomicBool::new(false), AtomicBool::new(false));
        let mut committed = Vec::new();
        threads.install(|| {
            fork.schedule(
                &mut [(); 2],
                &Dependences::default(),
                |position, &mut ()| {
                    if usize::from(position) == 1 {
                        assert!(wait(&started), "the job of item 0 starts on a task");
                    }
                    Releasing::<usize, bool>::Run(usize::from(position))
                },
                |job| {
                    if job == 0 {
                        started.store(true, Ordering::SeqCst);
                        wait(&first)
                    }
                    else {
                        true
                    }
                },
                |position, &mut (), saw| {
                    if usize::from(position) == 1 {
                        first.store(true, Ordering::SeqCst);
                    }
                    committed.push((usize::from(position), saw));
                },
            );
        });
        assert_eq!(
            committed,
            [(1, true), (0, true)],
            "item 1 commits at its job's return, while the job of item 0 still runs"
        );
    }

    #[test]
    fn a_held_release_waits_until_every_running_job_is_committed()
    {
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let Ok(Forked::Pooled(threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        let clock = AtomicUsize::new(0);
        let tick = || clock.fetch_add(1, Ordering::SeqCst);
        let mut items: Vec<Stamped> = core::iter::repeat_with(Stamped::default).take(6).collect();
        // Item 0 holds with no job running, so it commits what it holds. Item
        // 3 holds at its first release while the jobs of items 1 and 2 run.
        threads.install(|| {
            fork.schedule(
                &mut items,
                &Dependences::default(),
                |position, item| {
                    item.releases.push((tick(), std::thread::current().id()));
                    let held = (usize::MAX, usize::MAX);
                    match (usize::from(position), item.releases.len()) {
                        (0 | 3, 1) => Releasing::<(), (usize, usize)>::Held(held),
                        _ => Releasing::Run(()),
                    }
                },
                |()| {
                    let started = tick();
                    std::thread::yield_now();
                    (started, tick())
                },
                |_position, item, stamps| {
                    item.commits
                        .push((tick(), std::thread::current().id(), stamps));
                },
            );
        });
        let releases: Vec<usize> = items.iter().map(|item| item.releases.len()).collect();
        assert_eq!(
            releases,
            [1, 1, 1, 2, 1, 1],
            "item 3 is released again, and item 0, which held with no job running, is not"
        );
        assert_eq!(
            items[0].commits[0].2,
            (usize::MAX, usize::MAX),
            "item 0 commits what its release held"
        );
        let again = items[3].releases[1].0;
        for (position, item) in items.iter().enumerate().take(3).skip(1) {
            assert!(
                item.commits[0].0 < again,
                "item 3 is released again after item {position} is committed"
            );
        }
        assert!(
            items[3].commits[0].2 != (usize::MAX, usize::MAX) && items[3].commits[0].2.0 > again,
            "item 3 commits its job's result, after its release again"
        );
        assert!(
            items.iter().all(|item| item.commits.len() == 1),
            "every item is committed once"
        );
    }

    /// A schedule whose jobs run slower than its releases keeps at most a
    /// full lane and one more job for each lane released and not committed,
    /// so what the released jobs hold stays a bound of the width (#7299).
    #[test]
    fn a_schedule_releases_at_most_a_window_ahead_of_its_commits_7299()
    {
        let threads_count = 2_usize;
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(threads_count).unwrap(),
        )));
        let Ok(Forked::Pooled(threads, fork)) = pool.forked()
        else {
            panic!("a pool of two threads starts");
        };
        let outstanding = AtomicUsize::new(0);
        let most = AtomicUsize::new(0);
        let mut items = [(); 1_000];
        threads.install(|| {
            fork.schedule(
                &mut items,
                &Dependences::default(),
                |_position, &mut ()| {
                    let now = outstanding.fetch_add(1, Ordering::SeqCst).saturating_add(1);
                    most.fetch_max(now, Ordering::SeqCst);
                    Releasing::<(), ()>::Run(())
                },
                |()| std::thread::sleep(Duration::from_micros(50)),
                |_position, &mut (), ()| {
                    outstanding.fetch_sub(1, Ordering::SeqCst);
                },
            );
        });
        assert_eq!(
            outstanding.load(Ordering::SeqCst),
            0,
            "every released job is committed"
        );
        assert!(
            most.load(Ordering::SeqCst) <= threads_count.saturating_mul(DEPTH.saturating_add(1)),
            "at most a full lane and one more job for each lane wait for their commits, not {}",
            most.load(Ordering::SeqCst)
        );
    }

    #[test]
    fn a_chained_schedule_runs_its_jobs_on_the_calling_thread()
    {
        let caller = std::thread::current().id();
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let count = 256_usize;
        // Each release holds while a released job is not committed, as a
        // readmission whose next declaration reads the last one does.
        let pending = core::cell::Cell::new(0_usize);
        let releases = core::cell::Cell::new(0_usize);
        let mut ran: Vec<Option<ThreadId>> = alloc::vec![None; count];
        pool.schedule(
            &mut ran,
            &Dependences::default(),
            |_position, _ran| {
                releases.set(releases.get().saturating_add(1));
                if pending.get() > 0 {
                    return Releasing::<(), Option<ThreadId>>::Held(None);
                }
                pending.set(pending.get().saturating_add(1));
                Releasing::Run(())
            },
            |()| Some(std::thread::current().id()),
            |_position, ran, job| {
                pending.set(pending.get().saturating_sub(1));
                *ran = job;
            },
        );
        let elsewhere = ran.iter().filter(|&&job| job != Some(caller)).count();
        assert!(
            elsewhere <= 1,
            "only the job before the first hold leaves the calling thread, not {elsewhere}"
        );
        assert!(
            releases.get()
                <= count
                    .saturating_add(1)
                    .saturating_add(count.checked_div(CHAIN_PROBE).unwrap_or_default()),
            "a chain tries one release beside a running job in {CHAIN_PROBE}, not {} releases for {count} items",
            releases.get()
        );
    }

    #[test]
    fn a_scheduled_job_s_panic_resumes_on_the_calling_thread()
    {
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let Ok(Forked::Pooled(threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        let mut items: Vec<usize> = (0 .. 32).collect();
        let chain = Dependences::new((1_usize .. 32).map(|later| Dependence {
            before: later.checked_sub(1).unwrap(),
            after: later,
        }))
        .unwrap();
        let resumed = std::panic::catch_unwind(AssertUnwindSafe(|| {
            threads.install(|| {
                fork.schedule(
                    &mut items,
                    &chain,
                    |_position, item| Releasing::<usize, ()>::Run(*item),
                    |job| assert_ne!(job, 13, "job 13 panics"),
                    |_position, _item, ()| (),
                );
            });
        }));
        let payload = resumed.expect_err("the job's panic resumes at the schedule");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or_default();
        assert!(message.contains("job 13 panics"), "{message}");
    }

    #[test]
    fn a_pool_schedules_on_its_own_threads_and_commits_on_the_caller()
    {
        let caller = std::thread::current().id();
        let here = || Some(std::thread::current().id());
        let fan = |count: usize| {
            Dependences::new((1 .. count).map(|later| Dependence {
                before: later.checked_div(2).unwrap(),
                after: later,
            }))
            .unwrap()
        };
        let wide = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        let mut one = [(None, None, None)];
        wide.schedule(
            &mut one,
            &fan(1),
            |_position, ran| {
                ran.0 = here();
                Releasing::<(), Option<ThreadId>>::Run(())
            },
            |()| here(),
            |_position, ran, job| {
                ran.1 = job;
                ran.2 = here();
            },
        );
        assert_eq!(
            one,
            [(Some(caller), Some(caller), Some(caller))],
            "one item is released, runs and commits on the caller"
        );
        assert!(
            wide.started.get().is_none(),
            "a schedule of one item starts no thread"
        );
        let inside = || matches!(wide.forked(), Ok(Forked::Pooled(threads, _)) if threads.current_thread_index().is_some());
        let mut many = [(None, false, None); 64];
        wide.schedule(
            &mut many,
            &fan(64),
            |_position, ran| {
                ran.0 = here();
                Releasing::<(), bool>::Run(())
            },
            |()| inside() || here() == Some(caller),
            |_position, ran, pooled| {
                ran.1 = pooled;
                ran.2 = here();
            },
        );
        assert!(
            many.iter()
                .all(|&(released, pooled, committed)| released == Some(caller)
                    && pooled
                    && committed == Some(caller)),
            "every job runs on the pool's threads or on the caller, and every release and commit on the caller"
        );
        let serial = Pool::default();
        let mut ran = [(None, None, None); 8];
        serial.schedule(
            &mut ran,
            &fan(8),
            |_position, ran| {
                ran.0 = here();
                Releasing::<(), Option<ThreadId>>::Run(())
            },
            |()| here(),
            |_position, ran, job| {
                ran.1 = job;
                ran.2 = here();
            },
        );
        assert!(
            ran.iter()
                .all(|&ran| ran == (Some(caller), Some(caller), Some(caller))),
            "a serial pool releases, runs and commits every item on the caller"
        );
    }

    /// A part of a drain that counts each run of it.
    #[repr(transparent)]
    struct Counted<'runs>(&'runs AtomicUsize);

    impl gandr_kernel_core::fork::Job for Counted<'_>
    {
        /// Count one run of this part.
        ///
        /// # Specification
        /// trivial.
        fn run(&mut self)
        {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }

    #[test]
    fn the_pool_runs_each_part_of_a_drain_once_at_its_width()
    {
        use gandr_kernel_core::fork::ForkWidth;
        use gandr_kernel_core::fork::Job as Part;
        use gandr_kernel_core::fork::ObligationFork;

        let wide = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(4_usize).unwrap(),
        )));
        for (threads, pool) in [(4_usize, wide), (1_usize, Pool::default())] {
            assert_eq!(
                ObligationFork::workers(&pool),
                ForkWidth::from(NonZeroUsize::new(threads).unwrap()),
                "the fork's workers are the pool's threads"
            );
            let runs: [AtomicUsize; 16] = core::array::from_fn(|_| AtomicUsize::new(0));
            let mut parts: Vec<Counted<'_>> = runs.iter().map(Counted).collect();
            let mut jobs: Vec<&mut dyn Part> = parts
                .iter_mut()
                .map(|part| -> &mut dyn Part { part })
                .collect();
            ObligationFork::run_jobs(&pool, &mut jobs);
            assert!(
                runs.iter().all(|runs| runs.load(Ordering::Relaxed) == 1),
                "each part of the drain runs once on a pool of {threads}"
            );
        }
    }
}
