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
//! The `no_std` crates name no thread. `gandr-core-checker`'s
//! [`Fork`] is their seam: [`Pooled`] runs a staged check's stages on this
//! pool, and the walk and the formatting spawn their jobs on it directly,
//! because each hands its steps over on the calling thread.
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

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::sync::Arc;
use core::any::Any;
use core::fmt;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::panic::AssertUnwindSafe;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::OnceLock;
use std::sync::PoisonError;
use std::sync::mpsc;

use anodized::spec;
use gandr_core_checker::fork::Dependences;
use gandr_core_checker::fork::Fork;
use gandr_core_checker::fork::Serial;
use quenchant_shape::shape::Maybe;

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

/// Where a staged check's jobs run.
#[derive(Debug)]
pub enum Forked<'pool>
{
    /// The calling thread alone.
    Serial,
    /// The driver's pool, and the fork over it.
    Pooled(&'pool rayon::ThreadPool, Pooled),
}

/// The pool as the checker's fork. Each forked stage spawns one task per
/// worker, at most one per item, and each task takes items from one shared
/// cursor until none is left. A schedule spawns one task per job whose
/// predecessors have all returned, and the calling thread folds each item as
/// it returns.
///
/// # Specification
/// - provides: a [`Fork`] whose every task makes its worker state once, on its
///   first item, so a stage clones no more snapshots than it has workers with
///   work; halves join through `rayon::join`; a schedule's state is one per
///   pool thread that runs a job.
/// - panics: none of its own; a job's panic resumes at the fork.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L2 — programs checked at three workers and at the host's width
///   print the serial run, digest and verdict.
/// - witness: `stage::tests::every_width_stages_the_serial_run`
/// - witness: `pool::tests::a_schedule_runs_each_job_after_its_predecessors_and_folds_in_order`
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

    /// Run both halves through `rayon::join`.
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
        rayon::join(left, right)
    }

    /// Run every job on the pool once its predecessors have returned, and
    /// fold each item on the calling thread in slice order.
    ///
    /// # Specification
    /// - ensures: as [`Fork::schedule`]. Each item holds a count of the
    ///   predecessors whose jobs have not returned; a returning job counts its
    ///   successors down and queues each that reaches zero, with one task
    ///   spawned per queued job. The calling thread folds its next item as
    ///   soon as that item has returned, runs a queued job itself while it
    ///   waits, and blocks only when no job is queued. A schedule of one item,
    ///   or a pool of one worker, runs on the calling thread.
    /// - panics: a panic of `start` or `job`, resumed on the calling thread
    ///   once it has returned; a panic of `fold`.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — graphs with no edge, a chain and a scattered fan over
    ///   no item, one item and many, stamping each job's start and end and
    ///   each fold, distinguish a job run before a predecessor returned, a
    ///   skipped or repeated job, a fold out of order, before its job or off
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
        mut fold: Fold,
    ) where
        Item: Send,
        State: Send,
        Start: Fn() -> State + Sync,
        Job: Fn(&mut State, &mut Item) + Sync,
        Fold: FnMut(&mut Item),
    {
        let threads = NonZeroUsize::from(self.0).get();
        if threads.min(items.len()) <= 1 {
            Serial.schedule(items, after, start, job, fold);
            return;
        }
        let count = items.len();
        let (returned, arrivals) = mpsc::channel();
        let (schedule, ready) = Scheduled::new(items, after, threads, start, job, returned);
        rayon::in_place_scope(|scope| {
            for _ in 0 .. ready {
                schedule.spawn(scope);
            }
            let mut arrived: Vec<Option<&mut Item>> = core::iter::repeat_with(|| None).take(count).collect();
            for next in 0 .. count {
                let item = loop {
                    if let Some(item) = arrived.get_mut(next).and_then(Option::take) {
                        break item;
                    }
                    let returning = match arrivals.try_recv() {
                        Ok(returning) => returning,
                        Err(_) => {
                            // The guard drops here: the job may queue its
                            // successors.
                            let queued = lock(&schedule.ready).pop_front();
                            match queued {
                                Some((position, item)) => schedule.run(position, item, scope),
                                None => match arrivals.recv() {
                                    Ok(returning) => returning,
                                    Err(mpsc::RecvError) => return,
                                },
                            }
                        },
                    };
                    match returning {
                        Ok((position, item)) => {
                            if let Some(slot) = arrived.get_mut(position) {
                                *slot = Some(item);
                            }
                        },
                        Err(panic) => {
                            schedule.stopped.store(true, Ordering::Release);
                            std::panic::resume_unwind(panic);
                        },
                    }
                };
                fold(item);
            }
        });
    }
}

/// What a scheduled job hands back to the calling thread: its position and
/// item, or its panic.
type Returned<'items, Item> = Result<(usize, &'items mut Item), Box<dyn Any + Send>>;

/// One schedule's shared state, read by every task of its scope.
///
/// # Specification
/// - provides: each item's readiness count and its successors; the items still
///   waiting and those queued to run; one state per pool thread, and one for a
///   thread outside it; the jobs' channel back to the calling thread.
/// - panics: none.
/// - executable: none — [`Pooled::schedule`] carries the obligations.
struct Scheduled<'items, Item, State, Start, Job>
{
    /// Each item's count of predecessors whose jobs have not returned.
    waiting: Vec<AtomicUsize>,
    /// Every edge within the slice, sorted by its earlier item.
    edges: Vec<(usize, usize)>,
    /// Where each item's edges start in `edges`, and one past the last.
    starts: Vec<usize>,
    /// The items whose jobs still wait on a predecessor.
    held: Mutex<Vec<Option<&'items mut Item>>>,
    /// The items whose jobs may run, in the order they became ready.
    ready: Mutex<VecDeque<(usize, &'items mut Item)>>,
    /// Each pool thread's state, then the state of a thread outside the pool.
    states: Vec<Mutex<Option<State>>>,
    /// Makes a thread's state on its first job.
    start: Start,
    /// The job.
    job: Job,
    /// Where every returning job reports.
    returned: mpsc::Sender<Returned<'items, Item>>,
    /// Set once the calling thread resumes a panic, so no task starts another
    /// job.
    stopped: AtomicBool,
}

impl<'items, Item, State, Start, Job> Scheduled<'items, Item, State, Start, Job>
where
    Item: Send,
    State: Send,
    Start: Fn() -> State + Sync,
    Job: Fn(&mut State, &mut Item) + Sync,
{
    /// A schedule of `items` under `after` on `threads` pool threads, and how
    /// many items are ready at once.
    ///
    /// # Specification
    /// - ensures: an item is queued, in slice order, exactly when no edge
    ///   within the slice ends at it; the rest are held; edges past the slice
    ///   are dropped.
    /// - panics: none.
    #[spec(ensures: |ret| ret.1 <= count_of(&ret.0))]
    fn new(
        items: &'items mut [Item],
        after: &Dependences,
        threads: usize,
        start: Start,
        job: Job,
        returned: mpsc::Sender<Returned<'items, Item>>,
    ) -> (Self, usize)
    {
        let count = items.len();
        let edges: Vec<(usize, usize)> = after
            .edges()
            .iter()
            .copied()
            .filter(|&(_, later)| later < count)
            .collect();
        let starts = (0 ..= count)
            .map(|position| edges.partition_point(|&(earlier, _)| earlier < position))
            .collect();
        let mut waiting = alloc::vec![0_usize; count];
        for &(_, later) in &edges {
            if let Some(waits) = waiting.get_mut(later) {
                *waits = waits.saturating_add(1);
            }
        }
        let mut held = Vec::with_capacity(count);
        let mut ready = VecDeque::new();
        for ((position, item), &waits) in items.iter_mut().enumerate().zip(&waiting) {
            if waits == 0 {
                ready.push_back((position, item));
                held.push(None);
            }
            else {
                held.push(Some(item));
            }
        }
        let queued = ready.len();
        let schedule = Self {
            waiting: waiting.into_iter().map(AtomicUsize::new).collect(),
            edges,
            starts,
            held: Mutex::new(held),
            ready: Mutex::new(ready),
            states: core::iter::repeat_with(|| Mutex::new(None))
                .take(threads.saturating_add(1))
                .collect(),
            start,
            job,
            returned,
            stopped: AtomicBool::new(false),
        };
        (schedule, queued)
    }

    /// Spawn one task that runs one queued job, if one is still queued when it
    /// starts, and reports it to the calling thread.
    ///
    /// # Specification
    /// - ensures: one task spawned on `scope`.
    /// - panics: none.
    fn spawn<'scope>(
        &'scope self,
        scope: &rayon::Scope<'scope>,
    ) where
        'items: 'scope,
    {
        scope.spawn(move |scope| {
            if self.stopped.load(Ordering::Acquire) {
                return;
            }
            let queued = lock(&self.ready).pop_front();
            if let Some((position, item)) = queued {
                // The calling thread outlives every task of its scope, so a
                // report is refused only after it has resumed a panic.
                self.returned
                    .send(self.run(position, item, scope))
                    .unwrap_or_default();
            }
        });
    }

    /// Run the job of the item at `position` on this thread's state, then
    /// release the jobs that wait on it.
    ///
    /// # Specification
    /// - ensures: the item and its position, once its job has returned and its
    ///   successors are counted down; or the panic of `start` or the job.
    /// - panics: none; a panic of `start` or the job is returned.
    fn run<'scope>(
        &'scope self,
        position: usize,
        item: &'items mut Item,
        scope: &rayon::Scope<'scope>,
    ) -> Returned<'items, Item>
    where
        'items: 'scope,
    {
        let slot = rayon::current_thread_index()
            .and_then(|thread| self.states.get(thread))
            .or_else(|| self.states.last());
        let ran = slot.map_or(Ok(()), |slot| {
            let mut state = lock(slot);
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                (self.job)(state.get_or_insert_with(&self.start), &mut *item);
            }))
        });
        ran?;
        self.release(position, scope);
        Ok((position, item))
    }

    /// Count down every job that waits on the item at `position`, and queue
    /// each that waits on nothing more, with a task to run it.
    ///
    /// # Specification
    /// - ensures: each successor's count falls by one; a successor reaching
    ///   zero leaves the held items for the queue.
    /// - panics: none.
    fn release<'scope>(
        &'scope self,
        position: usize,
        scope: &rayon::Scope<'scope>,
    ) where
        'items: 'scope,
    {
        let successors = self
            .starts
            .get(position)
            .zip(self.starts.get(position.saturating_add(1)))
            .and_then(|(&first, &last)| self.edges.get(first .. last))
            .unwrap_or_default();
        for &(_, later) in successors {
            let freed = self
                .waiting
                .get(later)
                .is_some_and(|waits| waits.fetch_sub(1, Ordering::AcqRel) == 1);
            if !freed {
                continue;
            }
            let item = lock(&self.held).get_mut(later).and_then(Option::take);
            if let Some(item) = item {
                lock(&self.ready).push_back((later, item));
                self.spawn(scope);
            }
        }
    }
}

/// How many items a schedule holds, queued or held.
///
/// # Specification
/// trivial.
fn count_of<Item, State, Start, Job>(schedule: &Scheduled<'_, Item, State, Start, Job>) -> usize
{
    schedule.waiting.len()
}

/// The value `mutex` guards, whether or not a job panicked while holding it:
/// every guarded value here is whole between two statements.
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
    use core::num::NonZeroUsize;
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering;

    use gandr_core_checker::fork::Dependences;
    use gandr_core_checker::fork::Fork as _;
    use quenchant_shape::shape::Maybe;

    use super::Forked;
    use super::Pool;
    use super::alone;
    use crate::width::Threads;
    use crate::width::Width;

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
        folds: Vec<(usize, std::thread::ThreadId)>,
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
            let chain: Vec<(usize, usize)> = (1 .. count).map(|later| (later - 1, later)).collect();
            let fan: Vec<(usize, usize)> = (1 .. count)
                .flat_map(|later| [(later / 2, later), ((later * 37 + 11) % later, later)])
                .chain([(count, count + 3)])
                .collect();
            for (graph, edges) in [("no edge", Vec::new()), ("a chain", chain), ("a scattered fan", fan)] {
                let after = Dependences::new(edges).unwrap();
                let clock = AtomicUsize::new(0);
                let made = AtomicUsize::new(0);
                let tick = || clock.fetch_add(1, Ordering::SeqCst);
                let mut items: Vec<Stamped> = (0 .. count).map(|_| Stamped::default()).collect();
                let caller = threads.install(|| {
                    fork.schedule(
                        &mut items,
                        &after,
                        || {
                            made.fetch_add(1, Ordering::Relaxed);
                        },
                        |_state, item| {
                            item.started = tick();
                            item.runs += 1;
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
                    assert!(folded > item.returned, "{case}: item {position} folds after its job");
                    assert_eq!(thread, caller, "{case}: item {position} folds on the calling thread");
                }
                for pair in items.windows(2) {
                    assert!(pair[0].folds[0].0 < pair[1].folds[0].0, "{case}: folds in slice order");
                }
                for &(before, later) in after.edges().iter().filter(|&&(_, later)| later < count) {
                    assert!(
                        items[later].started > items[before].returned,
                        "{case}: item {later}'s job starts after item {before}'s returned"
                    );
                }
                let made = made.load(Ordering::Relaxed);
                assert_eq!(made == 0, count == 0, "{case}");
                assert!(made <= workers, "{case}: {made} states on {workers} workers");
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
        let chain = Dependences::new((1 .. 32).map(|later| (later - 1, later))).unwrap();
        let resumed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
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
}
