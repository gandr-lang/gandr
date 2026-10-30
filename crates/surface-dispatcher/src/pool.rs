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

mod spawning;

use alloc::sync::Arc;
use core::fmt;
use core::num::NonZeroUsize;
use std::sync::Mutex;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_fork::Fork;
use gandr_core_fork::Scoped;
use gandr_core_fork::Serial;
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
/// - witness: `walk::tests::a_tree_is_walked_in_order`
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
    /// - witness: `walk::tests::a_tree_is_walked_in_order`
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
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "pool: `Fork::each` on the driver's pool, which its caller installs before it forks"
        )
    )]
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
        let workers = NonZeroUsize::from(self.0).get().min(items.len());
        if workers <= 1 {
            Serial.each(items, start, job);
            return;
        }
        let cursor = Mutex::new(items.iter_mut());
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
                        let Some(item) = next
                        else {
                            break;
                        };
                        job(state.get_or_insert_with(&start), item);
                    }
                });
            }
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
}
