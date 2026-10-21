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

use alloc::sync::Arc;
use core::fmt;
use core::num::NonZeroUsize;
use std::sync::Mutex;
use std::sync::OnceLock;

use anodized::spec;
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
///   work; halves join through `rayon::join`.
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
}
