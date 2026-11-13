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
//! **A schedule counts readiness on the pool, with no rings.** The calling
//! thread folds each item of a [`Fork::schedule`] in slice order. Each fold
//! counts down the items that wait on the folded one, and queues each one that
//! reaches zero. At most one task for each pool thread takes queued jobs, and
//! a task ends when the queue is empty. While the calling thread waits for its
//! next item, it runs a queued job itself, and it blocks only when no job is
//! queued. The measurements of the dependence schedule found that the pool's
//! hand-off costs at most 1.4 % of a replay node while the pool is busy, so a
//! ring at this grain pays for nothing. The choice reverses on a measurement
//! where a ring beats the pool at this grain.
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

#[cfg(feature = "instrument")]
pub mod recording;
mod spawning;

use alloc::sync::Arc;
use core::any::Any;
use core::fmt;
use core::num::NonZeroUsize;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::OnceLock;
use std::sync::PoisonError;
use std::sync::mpsc;

use anodized::spec;
use crossbeam_queue::ArrayQueue;
use gandr_core_fork::Dependence;
use gandr_core_fork::Dependences;
use gandr_core_fork::Fork;
use gandr_core_fork::Scoped;
use gandr_core_fork::Serial;
use gandr_kernel_core::fork::ForkWidth;
use gandr_kernel_core::fork::Job;
use gandr_kernel_core::fork::ObligationFork;
use quenchant_shape::shape::Maybe;

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
    /// The threads, once a fork asked for them.
    started: OnceLock<Result<Started, PoolFault>>,
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
    /// A pool of `width` threads, none of them started yet.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(width: Width) -> Self
    {
        Self {
            width,
            started: OnceLock::new(),
        }
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
            }) => Ok(Forked::Pooled(pool, Pooled(threads))),
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
    /// Run `job` on every item on the pool's threads, each task taking items
    /// from a shared cursor.
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

    /// Run every job on the pool's threads once every item that it waits on is
    /// folded, and fold each item on the calling thread in slice order.
    ///
    /// # Specification
    /// - ensures: as [`Fork::schedule`]. One item or none, a pool of one thread
    ///   and a pool the host refused run the serial schedule on the calling
    ///   thread, and none of them starts a thread. Otherwise the jobs run on
    ///   the pool's own threads as [`Pooled`] runs them, and on the calling
    ///   thread while it waits; the calling thread folds every item.
    /// - panics: a panic of `start`, `job` or `fold`, on the calling thread.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one item, many items and a serial pool, each
    ///   recording the thread of every job and of every fold, distinguish a
    ///   schedule that starts the pool for one item, a job run on a thread that
    ///   is neither the pool's nor the caller's, and a fold off the calling
    ///   thread.
    /// - witness: `pool::tests::a_pool_schedules_on_its_own_threads_and_folds_on_the_caller`
    #[inline]
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
        Fold: FnMut(&mut Item),
    {
        if items.len() <= 1 {
            Serial.schedule(items, after, start, job, fold);
            return;
        }
        match self.forked() {
            Ok(Forked::Pooled(threads, Pooled(workers))) => schedule_indexed(
                Some(threads),
                workers,
                items,
                after,
                start,
                |state, _index, item| job(state, item),
                fold,
            ),
            Ok(Forked::Serial) | Err(_) => Serial.schedule(items, after, start, job, fold),
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

/// The pool as the checker's fork: each forked stage spawns one task per
/// worker, at most one per item, and each task takes items from one shared
/// cursor until none is left.
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
#[repr(transparent)]
pub struct Pooled(Threads);

impl Fork for Pooled
{
    /// Run `job` on every item from one task per worker, each taking items
    /// from a shared cursor.
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
        each_indexed(self.0, items, start, |state, _index, item| job(state, item));
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

    /// Run every job on the pool once every item that it waits on is folded,
    /// and fold each item on the calling thread in slice order.
    ///
    /// # Specification
    /// - ensures: as [`Fork::schedule`]. Each item holds a count of the items
    ///   that it waits on and that are not folded. Each fold counts down the
    ///   items that wait on the folded one, and queues each one that reaches
    ///   zero. At most one task for each pool thread takes queued jobs, and a
    ///   task ends when the queue is empty. After a fold that queues jobs, the
    ///   calling thread starts tasks while fewer run than jobs wait. The
    ///   calling thread folds its next item as soon as that item has returned.
    ///   It keeps the job of that item for itself when a fold has just queued
    ///   it, so a chain needs no task. While it waits, it runs a queued job
    ///   itself, and it blocks only when no job is queued. A schedule of one
    ///   item, or a pool of one worker, runs on the calling thread. Each thread
    ///   that runs a job keeps one state for all its jobs.
    /// - panics: a panic of `start`, `job` or `fold`, resumed on the calling
    ///   thread once it has returned; no queued job starts after it.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — graphs with no edge, a chain and a scattered fan over
    ///   no item, one item and many, stamping each job's start and end and each
    ///   fold, distinguish a job run before an item that it waits on is folded,
    ///   a skipped or repeated job, a fold out of order, before its job or off
    ///   the calling thread, and a state made per job.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    #[inline]
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
        Fold: FnMut(&mut Item),
    {
        schedule_indexed(
            None,
            self.0,
            items,
            after,
            start,
            |state, _index, item| job(state, item),
            fold,
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

/// Run `job` on every item and its index from one task per worker, at most
/// `workers` and one per item, each taking items from a shared cursor. At one
/// worker the items run on the calling thread in slice order, from one state.
///
/// # Specification
/// - ensures: `job` runs once per item with the item's place in `items`; each
///   task makes its state on its first item and keeps it for the rest.
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
    let workers = NonZeroUsize::from(workers).get().min(items.len());
    if workers <= 1 {
        let mut state = None;
        for (index, item) in items.iter_mut().enumerate() {
            job(state.get_or_insert_with(&start), ItemIndex(index), item);
        }
        return;
    }
    let cursor = Mutex::new(items.iter_mut().enumerate());
    rayon::scope(|scope| {
        for _ in 0 .. workers {
            scope.spawn(|_| {
                let mut state = None;
                loop {
                    // A poisoned cursor only means another task's job
                    // panicked; the panic resumes when the scope ends.
                    let next = match cursor.lock() {
                        Ok(mut items) => items.next(),
                        Err(poisoned) => poisoned.into_inner().next(),
                    };
                    let Some((index, item)) = next
                    else {
                        break;
                    };
                    job(state.get_or_insert_with(&start), ItemIndex(index), item);
                }
            });
        }
    });
}

/// Run `job` on every item and its index once the calling thread has folded
/// every item that it waits on, on `pool` or on the pool that the calling
/// thread runs in, with at most `workers` tasks beside the calling thread, and
/// `fold` on every item on the calling thread in slice order. At one worker,
/// or one item, the items run on the calling thread in slice order, from one
/// state.
///
/// # Specification
/// - ensures: as [`Pooled`]'s `schedule`, with the item's place in `items`
///   handed to each job.
/// - panics: a panic of `start`, `job` or `fold`, resumed on the calling thread
///   once it has returned.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
/// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
/// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "pool: `Fork::schedule` on the driver's pool, which its caller names or installs before it forks"
    )
)]
fn schedule_indexed<Item, State, Start, Job, Fold>(
    pool: Option<&rayon::ThreadPool>,
    workers: Threads,
    items: &mut [Item],
    after: &Dependences,
    start: Start,
    job: Job,
    mut fold: Fold,
) where
    Item: Send,
    State: Send,
    Start: Fn() -> State + Sync,
    Job: Fn(&mut State, ItemIndex, &mut Item) + Sync,
    Fold: FnMut(&mut Item),
{
    let count = items.len();
    if NonZeroUsize::from(workers).get().min(count) <= 1 {
        let mut state = None;
        for (index, item) in items.iter_mut().enumerate() {
            job(state.get_or_insert_with(&start), ItemIndex(index), item);
            fold(item);
        }
        return;
    }
    // Each job reports once, so a buffer of one slot for each item never
    // fills, and no report allocates.
    let (returned, arrivals) = mpsc::sync_channel(count);
    let (schedule, waiting) = Scheduled::new(pool, items, after, workers, start, job, returned);
    match pool {
        Some(pool) => {
            pool.in_place_scope(|scope| schedule.drive(scope, waiting, &arrivals, &mut fold));
        },
        None => {
            rayon::in_place_scope(|scope| schedule.drive(scope, waiting, &arrivals, &mut fold));
        },
    }
}

/// What a scheduled job hands back to the calling thread: its position and
/// its item, or its panic.
type Returned<'items, Item> = Result<(ItemIndex, &'items mut Item), Box<dyn Any + Send>>;

/// A job that may run: its item's position and the item.
type Ready<'items, Item> = (ItemIndex, &'items mut Item);

/// Whether a schedule counted in one more task.
///
/// # Specification
/// - provides: the answer of one try to count in a task.
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Place
{
    /// Fewer tasks ran than the pool has threads, so the count rose by one.
    Taken,
    /// As many tasks run as the pool has threads.
    Full,
}

/// One schedule's shared state, read by every task of its scope.
///
/// # Specification
/// - provides: the bounded queue of the items whose jobs may run, which the
///   calling thread alone pushes and every task pops with no lock; the count of
///   the tasks that pop it; one state slot for each pool thread, and one for a
///   thread outside the pool; the jobs' channel back to the calling thread.
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
struct Scheduled<'items, 'pool, Item, State, Start, Job>
{
    /// The pool that the scope spawns on, or the pool of the calling thread.
    pool: Option<&'pool rayon::ThreadPool>,
    /// The most tasks that run at once: one for each pool thread.
    threads: usize,
    /// The items whose jobs may run, in the order that they became ready, with
    /// room for every item.
    ready: ArrayQueue<Ready<'items, Item>>,
    /// How many tasks pop `ready` now: at most `threads`.
    running: AtomicUsize,
    /// Each pool thread's state, then the state of a thread outside the pool.
    /// A job takes its thread's state out and puts it back when it returns.
    states: Vec<Mutex<Option<State>>>,
    /// Makes a state for a thread whose slot is empty.
    start: Start,
    /// The job.
    job: Job,
    /// Where every job that a task runs reports.
    returned: mpsc::SyncSender<Returned<'items, Item>>,
    /// Set once the calling thread resumes a panic, so that no task starts
    /// another job.
    stopped: AtomicBool,
}

/// What the calling thread alone holds of a schedule: each item's successors,
/// its count of the items that it waits on and that are not folded, and the
/// items whose jobs still wait.
///
/// # Specification
/// - provides: the edges within the slice, sorted by their earlier item, and
///   where each item's edges start; a count and a held item for each item.
/// - panics: none.
/// - executable: none — a type-level block; [`Pooled`]'s `schedule` carries the
///   obligations.
struct Waiting<'items, Item>
{
    /// Every edge within the slice, sorted by its earlier item.
    edges: Vec<Dependence>,
    /// Where each item's edges start in `edges`, and one past the last.
    starts: Vec<usize>,
    /// Each item's count of the items that it waits on and that are not
    /// folded.
    counts: Vec<usize>,
    /// The items whose jobs still wait on an item that is not folded.
    held: Vec<Option<&'items mut Item>>,
}

impl<'items, Item> Waiting<'items, Item>
{
    /// Count down every item that waits on the item at `position`. The item
    /// right after it, when it waits on nothing more, is the calling thread's
    /// next job. Each other item that waits on nothing more goes on `ready`,
    /// in the order of its edges.
    ///
    /// # Specification
    /// - ensures: each successor's count falls by one; a successor that reaches
    ///   zero leaves the held items. The answer is the item right after
    ///   `position` when it left.
    /// - panics: none.
    /// - executable: none — the queue is shared with the tasks that pop it, so
    ///   no postcondition reads it at one instant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    fn release(
        &mut self,
        position: ItemIndex,
        ready: &ArrayQueue<Ready<'items, Item>>,
    ) -> Option<&'items mut Item>
    {
        let position = usize::from(position);
        let successors = self
            .starts
            .get(position)
            .zip(self.starts.get(position.saturating_add(1)))
            .and_then(|(&first, &last)| self.edges.get(first .. last))
            .unwrap_or_default();
        let mine = position.saturating_add(1);
        let mut kept = None;
        for &Dependence { after: later, .. } in successors {
            let freed = self.counts.get_mut(later).is_some_and(|waits| {
                *waits = waits.saturating_sub(1);
                *waits == 0
            });
            if let Some(item) = self
                .held
                .get_mut(later)
                .filter(|_| freed)
                .and_then(Option::take)
            {
                if later == mine {
                    kept = Some(item);
                }
                else {
                    // `ready` holds room for every item, and an item leaves
                    // the held items once, so no push is refused.
                    let refused = ready.push((ItemIndex(later), item)).is_err();
                    debug_assert!(!refused, "a schedule's queue holds room for every item");
                }
            }
        }
        kept
    }
}

impl<'items, 'pool, Item, State, Start, Job> Scheduled<'items, 'pool, Item, State, Start, Job>
where
    Item: Send,
    State: Send,
    Start: Fn() -> State + Sync,
    Job: Fn(&mut State, ItemIndex, &mut Item) + Sync,
{
    /// A schedule of `items` under `after` with at most `workers` tasks, and
    /// what the calling thread holds of it.
    ///
    /// # Specification
    /// - ensures: an item is queued, in slice order, exactly when no edge
    ///   within the slice ends at it; the rest are held; edges past the slice
    ///   are dropped. The plan takes one pass over the items and the edges. The
    ///   queue holds room for every item, so no later push allocates. No task
    ///   runs yet.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    #[spec(ensures: |ret| ret.1.held.len() == ret.1.counts.len())]
    fn new(
        pool: Option<&'pool rayon::ThreadPool>,
        items: &'items mut [Item],
        after: &Dependences,
        workers: Threads,
        start: Start,
        job: Job,
        returned: mpsc::SyncSender<Returned<'items, Item>>,
    ) -> (Self, Waiting<'items, Item>)
    {
        let threads = NonZeroUsize::from(workers).get();
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
        let mut held = Vec::with_capacity(count);
        let ready = ArrayQueue::new(count.max(1));
        for ((position, item), &waits) in items.iter_mut().enumerate().zip(&counts) {
            if waits == 0 {
                // `ready` holds room for every item, so no push is refused.
                let refused = ready.push((ItemIndex(position), item)).is_err();
                debug_assert!(!refused, "a schedule's queue holds room for every item");
                held.push(None);
            }
            else {
                held.push(Some(item));
            }
        }
        let schedule = Self {
            pool,
            threads,
            ready,
            running: AtomicUsize::new(0),
            states: core::iter::repeat_with(|| Mutex::new(None))
                .take(threads.saturating_add(1))
                .collect(),
            start,
            job,
            returned,
            stopped: AtomicBool::new(false),
        };
        let waiting = Waiting {
            edges,
            starts,
            counts,
            held,
        };
        (schedule, waiting)
    }

    /// Start the tasks for the queued jobs, then fold every item on the
    /// calling thread in slice order, each once its job has returned, and
    /// release the items that wait on it.
    ///
    /// # Specification
    /// - ensures: `fold` ran once on every item, in slice order. Each fold
    ///   counts down the items that wait on the folded one, and queues each one
    ///   that waits on nothing more. The calling thread keeps for itself the
    ///   job of the item that it folds next, when that fold frees it, and
    ///   queues it for no task. After a fold that queues a job, the calling
    ///   thread starts tasks while fewer run than jobs wait and than the pool
    ///   has threads. While the next item's job has not returned, the calling
    ///   thread runs a queued job, or blocks until a job reports when none is
    ///   queued.
    /// - panics: the first panic of a job or of `fold`, after it sets the stop
    ///   so that no queued job starts.
    /// - executable: none — each fold is a call of the caller's closure, and
    ///   the call returns nothing for a postcondition to compare.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    fn drive<'scope, Fold>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
        mut waiting: Waiting<'items, Item>,
        arrivals: &mpsc::Receiver<Returned<'items, Item>>,
        fold: &mut Fold,
    ) where
        'items: 'scope,
        Fold: FnMut(&mut Item),
    {
        self.start_tasks(scope);
        let count = waiting.held.len();
        let mut arrived: Vec<Option<&mut Item>> =
            core::iter::repeat_with(|| None).take(count).collect();
        let mut own = None;
        for next in 0 .. count {
            let item = loop {
                if let Some(item) = arrived.get_mut(next).and_then(Option::take) {
                    break item;
                }
                let returning = if let Some(item) = own.take() {
                    self.run(ItemIndex(next), item)
                }
                else if let Ok(returning) = arrivals.try_recv() {
                    returning
                }
                else if let Some((position, item)) = self.take() {
                    self.run(position, item)
                }
                else {
                    // The calling thread alone queues jobs, so an empty queue
                    // stays empty here. The next item's job runs on a task,
                    // and it reports.
                    match arrivals.recv() {
                        Ok(returning) => returning,
                        // The schedule holds the sender until the scope ends,
                        // so the channel never closes here.
                        Err(mpsc::RecvError) => return,
                    }
                };
                match returning {
                    Ok((position, item)) => {
                        if let Some(slot) = arrived.get_mut(usize::from(position)) {
                            *slot = Some(item);
                        }
                    },
                    Err(panic) => self.stop(panic),
                }
            };
            if let Err(panic) = std::panic::catch_unwind(AssertUnwindSafe(|| fold(item))) {
                self.stop(panic);
            }
            own = waiting.release(ItemIndex(next), &self.ready);
            if !self.ready.is_empty() {
                self.start_tasks(scope);
            }
        }
    }

    /// Stop every task from starting a queued job, then resume `panic`.
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
        self.stopped.store(true, Ordering::Release);
        std::panic::resume_unwind(panic)
    }

    /// Take the next queued job, unless the stop is set.
    ///
    /// # Specification
    /// - ensures: the job taken, if any.
    /// - panics: none.
    /// - executable: none — the queue is shared with the tasks that run beside
    ///   this call, so no postcondition reads it at one instant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    fn take(&self) -> Option<Ready<'items, Item>>
    {
        if self.stopped.load(Ordering::Acquire) {
            return None;
        }
        self.ready.pop()
    }

    /// Start tasks while fewer run than jobs wait and than the pool has
    /// threads.
    ///
    /// # Specification
    /// - ensures: the count of tasks stays at most `threads`; each task counted
    ///   in is spawned.
    /// - panics: none.
    /// - executable: none — the spawned tasks run after the call returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    /// - witness: `pool::tests::a_pool_schedules_on_its_own_threads_and_folds_on_the_caller`
    fn start_tasks<'scope>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
    ) where
        'items: 'scope,
    {
        while self.running.load(Ordering::SeqCst) < self.ready.len()
            && self.count_in() == Place::Taken
        {
            self.spawn(scope);
        }
    }

    /// Count in one more task when fewer tasks run than the pool has threads.
    ///
    /// # Specification
    /// - ensures: [`Place::Taken`] exactly when the count rose by one, to at
    ///   most `threads`.
    /// - panics: none.
    /// - executable: none — the count is shared with the tasks that run beside
    ///   this call, so no postcondition reads it at one instant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    fn count_in(&self) -> Place
    {
        match self
            .running
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |running| {
                (running < self.threads).then(|| running.saturating_add(1))
            }) {
            Ok(_) => Place::Taken,
            Err(_) => Place::Full,
        }
    }

    /// Spawn one counted-in task, which takes queued jobs and reports each to
    /// the calling thread until the queue is empty.
    ///
    /// # Specification
    /// - ensures: one task spawned on `scope`. A task that finds the queue
    ///   empty, or the stop set, counts itself out and ends. It first looks at
    ///   the queue once more. A job that the calling thread queued while the
    ///   count still held this task started no task, so the task counts itself
    ///   in again and takes that job.
    /// - panics: none.
    /// - executable: none — the spawned task runs after the call returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    /// - witness: `pool::tests::a_pool_schedules_on_its_own_threads_and_folds_on_the_caller`
    fn spawn<'scope>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
    ) where
        'items: 'scope,
    {
        scope.spawn(move |_scope| {
            loop {
                while let Some((position, item)) = self.take() {
                    // The calling thread holds the receiver until the scope
                    // ends, and the buffer holds a slot for each job, so the
                    // report never waits and is never refused.
                    self.returned
                        .send(self.run(position, item))
                        .unwrap_or_default();
                }
                self.running.fetch_sub(1, Ordering::SeqCst);
                if self.stopped.load(Ordering::Acquire)
                    || self.ready.is_empty()
                    || self.count_in() == Place::Full
                {
                    return;
                }
            }
        });
    }

    /// Run the job of the item at `position` on this thread's state.
    ///
    /// # Specification
    /// - ensures: the item and its position, once its job has returned; or the
    ///   panic of `start` or of the job. The job takes its thread's state out
    ///   of the slot, or makes one when the slot is empty, and puts it back
    ///   when it returns. So a job that its thread runs while another job of
    ///   that thread waits inside a nested fork gets a state of its own, and no
    ///   state goes to two jobs at once.
    /// - panics: none; a panic of `start` or of the job is returned, and the
    ///   state that it held is dropped.
    /// - executable: none — the state's ownership is a property of the
    ///   schedule, which a postcondition over the returned item cannot observe.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pooled`]'s `schedule`.
    /// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
    /// - witness: `pool::tests::a_scheduled_job_s_panic_resumes_on_the_calling_thread`
    fn run(
        &self,
        position: ItemIndex,
        item: &'items mut Item,
    ) -> Returned<'items, Item>
    {
        let thread = self.pool.map_or_else(
            rayon::current_thread_index,
            rayon::ThreadPool::current_thread_index,
        );
        let slot = thread
            .and_then(|thread| self.states.get(thread))
            .or_else(|| self.states.last());
        let mut state = slot.and_then(|slot| lock(slot).take());
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            (self.job)(state.get_or_insert_with(&self.start), position, &mut *item);
        }))?;
        if let (Some(slot), Some(state)) = (slot, state) {
            let mut kept = lock(slot);
            if kept.is_none() {
                *kept = Some(state);
            }
        }
        Ok((position, item))
    }
}

/// The value that `mutex` guards, whether or not a job panicked while it held
/// the guard: every guarded value here is whole between two statements.
///
/// # Specification
/// trivial.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
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
    use gandr_core_fork::Scoped;
    use gandr_core_fork::Spawn;
    use gandr_core_fork::Unwound;
    use quenchant_shape::shape::Maybe;

    use super::Forked;
    use super::Pool;
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

    /// One item of a schedule: when its job started and returned, how often
    /// it ran, and when and where it was folded.
    #[derive(Debug, Default)]
    struct Stamped
    {
        /// The clock when the job started.
        started: usize,
        /// The clock when the job returned.
        returned: usize,
        /// How often the job ran.
        runs: usize,
        /// The clock and the thread at each fold.
        folds: Vec<(usize, ThreadId)>,
    }

    #[test]
    fn a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order()
    {
        let workers = 4_usize;
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::new(workers).unwrap(),
        )));
        let Ok(Forked::Pooled(threads, fork)) = pool.forked()
        else {
            panic!("a pool of four threads starts");
        };
        for count in [0_usize, 1, 2, 7, 64] {
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
            for (graph, edges) in [
                ("no edge", Vec::new()),
                ("a chain", chain),
                ("a scattered fan", fan),
            ] {
                let after = Dependences::new(edges).unwrap();
                let clock = AtomicUsize::new(0);
                let made = AtomicUsize::new(0);
                let tick = || clock.fetch_add(1, Ordering::SeqCst);
                let mut items: Vec<Stamped> = core::iter::repeat_with(Stamped::default)
                    .take(count)
                    .collect();
                let caller = threads.install(|| {
                    fork.schedule(
                        &mut items,
                        &after,
                        || {
                            made.fetch_add(1, Ordering::Relaxed);
                        },
                        |_state, item| {
                            item.started = tick();
                            item.runs = item.runs.checked_add(1).unwrap();
                            std::thread::yield_now();
                            item.returned = tick();
                        },
                        |item| item.folds.push((tick(), std::thread::current().id())),
                    );
                    std::thread::current().id()
                });
                let case = format!("{graph} over {count} items");
                for (position, item) in items.iter().enumerate() {
                    assert_eq!(item.runs, 1, "{case}: item {position}'s job runs once");
                    let [(folded, thread)] = item.folds[..]
                    else {
                        panic!("{case}: item {position} folds once");
                    };
                    assert!(
                        folded > item.returned,
                        "{case}: item {position} folds after its job"
                    );
                    assert_eq!(
                        thread, caller,
                        "{case}: item {position} folds on the calling thread"
                    );
                }
                for pair in items.windows(2) {
                    let [ref first, ref second] = *pair
                    else {
                        panic!("{case}: a window of two holds two items");
                    };
                    assert!(
                        first.folds[0].0 < second.folds[0].0,
                        "{case}: folds in slice order"
                    );
                }
                for &Dependence {
                    before,
                    after: later,
                } in after.edges().iter().filter(|edge| edge.after < count)
                {
                    assert!(
                        items[later].started > items[before].folds[0].0,
                        "{case}: item {later}'s job starts after item {before} is folded"
                    );
                }
                let made = made.load(Ordering::Relaxed);
                assert_eq!(made == 0, count == 0, "{case}");
                assert!(
                    made <= workers,
                    "{case}: {made} states on {workers} workers"
                );
            }
        }
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
                    || (),
                    |_state, item| assert_ne!(*item, 13, "job 13 panics"),
                    |_item| (),
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
    fn a_pool_schedules_on_its_own_threads_and_folds_on_the_caller()
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
        let mut one = [(None, None)];
        wide.schedule(
            &mut one,
            &fan(1),
            || (),
            |_state, ran| ran.0 = here(),
            |ran| ran.1 = here(),
        );
        assert_eq!(
            one,
            [(Some(caller), Some(caller))],
            "one item runs and folds on the caller"
        );
        assert!(
            wide.started.get().is_none(),
            "a schedule of one item starts no thread"
        );
        let inside = || matches!(wide.forked(), Ok(Forked::Pooled(threads, _)) if threads.current_thread_index().is_some());
        let mut many = [(false, None); 64];
        wide.schedule(
            &mut many,
            &fan(64),
            || (),
            |_state, ran| ran.0 = inside() || here() == Some(caller),
            |ran| ran.1 = here(),
        );
        assert!(
            many.iter()
                .all(|&(ran, folded)| ran && folded == Some(caller)),
            "every job runs on the pool's threads or on the caller, and every fold on the caller"
        );
        let serial = Pool::default();
        let mut ran = [(None, None); 8];
        serial.schedule(
            &mut ran,
            &fan(8),
            || (),
            |_state, ran| ran.0 = here(),
            |ran| ran.1 = here(),
        );
        assert!(
            ran.iter().all(|&ran| ran == (Some(caller), Some(caller))),
            "a serial pool runs every job and every fold on the caller"
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
