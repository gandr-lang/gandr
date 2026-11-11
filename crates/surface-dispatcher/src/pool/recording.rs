//! The pool as a fork that records each job it runs into the activity ring.
//!
//! [`Pool::recording`] answers an [`ActivityFork`]: a [`Fork`] over the pool's
//! threads that writes a start mark and an end mark around each job. The marks
//! go into the ring of the thread that runs the job. A thread of the pool
//! writes the ring at its index in the pool, and every other thread writes the
//! last ring, the ring of the calling thread. The clock is [`clock`], the
//! process's monotonic clock, which the hub's fold reads too.
//!
//! A fork site that records nothing forks through the pool itself, so the
//! choice costs one branch for each fork and none for each job. A build
//! without the `instrument` feature carries none of this module.
//!
//! # What it does not cover
//!
//! A scope is one task on the thread that runs its body. Its spawned jobs are
//! not recorded apart, because a mark that rides into a spawned job must
//! outlive the scope, and the scope's lifetime is the caller's choice. No fork
//! site of the session or of the walk opens a scope.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-activity — each job of the pool marked on the ring of its
//!   thread, and the hub's fold the one consumer.

use core::num::NonZeroU16;
use core::num::NonZeroUsize;
use std::sync::OnceLock;
use std::time::Instant;

use gandr_core_fork::Fork;
use gandr_core_fork::Scoped;
use gandr_core_fork::Spawn;
use gandr_core_fork::activity::Activity;
use gandr_core_fork::activity::Core;
use gandr_core_fork::activity::Cores;
use gandr_core_fork::activity::Declared;
use gandr_core_fork::activity::Edge;
use gandr_core_fork::activity::Mark;
use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Slots;
use gandr_core_fork::activity::Task;
use gandr_core_fork::activity::World;

use super::Forked;
use super::Helped;
use super::ItemIndex;
use super::Pool;
use super::Pooled;
use super::each_indexed;
use crate::width::Threads;

/// The process's monotonic clock: the nanoseconds since its first reading.
///
/// Every mark of an [`ActivityFork`] reads this clock, and the hub's fold ticks
/// on it, so a mark and a tick compare.
///
/// # Specification
/// - ensures: a reading no earlier than any reading before it on any thread.
/// - panics: none.
/// - executable: none — the clock is the host's.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded fork's marks read in the order of their jobs.
/// - witness: `pool::recording::tests::a_recorded_fork_marks_each_item_with_its_declaration`
#[inline]
#[must_use]
pub fn clock() -> Nanos
{
    static EPOCH: OnceLock<Instant> = OnceLock::new();
    let elapsed = EPOCH.get_or_init(Instant::now).elapsed().as_nanos();
    Nanos::from(u64::try_from(elapsed).unwrap_or(u64::MAX))
}

/// `work`, run as one task of the kind `task`, in `world`, on `declared`:
/// between a start mark and an end mark on the ring of the calling thread.
///
/// A job that the pool runs whole, such as an editor's judgement or its
/// admission, is one task of its thread. The fork sites inside the job mark
/// their own jobs through [`Pool::recording`].
///
/// # Specification
/// - requires: `activity` is the pool's, as [`Pool::activity`] makes it.
/// - ensures: the answer of `work`, run once. A thread of the pool writes its
///   own ring, and every other thread writes the last ring.
/// - panics: only by propagating a panic of `work`, which leaves the end mark
///   unwritten.
/// - executable: none — the marks are atomics, which a postcondition does not
///   read.
///
/// # Adequacy
/// - hypothesis: L3 — a task outside the pool reaches the fold as one start and
///   one end on the last ring, with its kind, world and declaration.
/// - witness: `pool::recording::tests::a_marked_task_is_one_start_and_one_end_on_its_thread_s_ring`
#[inline]
pub fn marked<Out>(
    activity: &Activity,
    (task, world): (Task, World),
    declared: Declared,
    work: impl FnOnce() -> Out,
) -> Out
{
    Marks {
        activity,
        task,
        world,
    }
    .around(declared, work)
}

impl Pool
{
    /// The rings for this pool: one for each of its threads, and one more for
    /// every thread outside it, each of `slots` marks.
    ///
    /// # Specification
    /// - ensures: an activity of the pool's threads and one ring more.
    /// - panics: none.
    /// - executable: none — the rings are atomics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded fork's marks reach the rings of the
    ///   threads that ran its jobs.
    /// - witness: `pool::recording::tests::a_recorded_fork_marks_each_item_with_its_declaration`
    #[inline]
    #[must_use]
    pub fn activity(
        &self,
        slots: Slots,
    ) -> Activity
    {
        let threads = core::num::NonZeroUsize::from(self.width.threads()).get();
        let rings = u16::try_from(threads.saturating_add(1)).unwrap_or(u16::MAX);
        Activity::new(
            Cores::from(NonZeroU16::new(rings).unwrap_or(NonZeroU16::MIN)),
            slots,
        )
    }

    /// The pool as a fork that records each job of the kind `task`, in
    /// `world`, into `activity`. `declared` names the declaration of each
    /// item of an `each` by its place; a half of a `join` and a scope name
    /// none.
    ///
    /// # Specification
    /// - requires: `activity` is this pool's, as [`Pool::activity`] makes it.
    /// - ensures: a fork that runs each job as the pool runs it, between a
    ///   start mark and an end mark on the ring of the thread that runs it.
    /// - panics: none.
    /// - executable: none — the marks are atomics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded fork over many items marks each item once,
    ///   start before end, with its declaration.
    /// - witness: `pool::recording::tests::a_recorded_fork_marks_each_item_with_its_declaration`
    #[inline]
    #[must_use]
    pub const fn recording<'fork, Declares>(
        &'fork self,
        activity: &'fork Activity,
        (task, world): (Task, World),
        declared: Declares,
    ) -> ActivityFork<'fork, Declares>
    where
        Declares: Fn(ItemIndex) -> Declared + Sync,
    {
        ActivityFork {
            pool: self,
            marks: Marks {
                activity,
                task,
                world,
            },
            declared,
        }
    }
}

/// What a recording writes beside each job: the activity, the kind of the
/// jobs and their world.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Marks<'fork>
{
    /// The rings the marks go into.
    activity: &'fork Activity,
    /// The kind of every job of the fork.
    task: Task,
    /// The world the jobs run in.
    world: World,
}

impl Marks<'_>
{
    /// Run `work` between a start mark and an end mark on the ring of the
    /// calling thread, both naming `declared`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn around<Out>(
        self,
        declared: Declared,
        work: impl FnOnce() -> Out,
    ) -> Out
    {
        let rings = NonZeroUsize::from(NonZeroU16::from(self.activity.cores())).get();
        let outside = rings.saturating_sub(1);
        let index = rayon::current_thread_index()
            .filter(|&index| index < outside)
            .unwrap_or(outside);
        let core = Core::from(u16::try_from(index).unwrap_or(u16::MAX));
        let worker = self.activity.worker(core);
        let mark = |edge| Mark {
            task: self.task,
            edge,
            declaration: declared,
            world: self.world,
            clock: clock(),
        };
        if let Ok(ref worker) = worker {
            worker.record(mark(Edge::Start));
        }
        let out = work();
        if let Ok(ref worker) = worker {
            worker.record(mark(Edge::End));
        }
        out
    }
}

/// The pool as a fork that records each job: [`Pool::recording`].
///
/// # Specification
/// - provides: a [`Fork`] that runs as the pool runs, and marks each item of an
///   `each`, each half of a `join` and each scope's body.
/// - panics: none of its own; a job's panic is the job's.
/// - executable: none — the schedule is the pool's.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Pool::recording`].
/// - witness: `pool::recording::tests::a_recorded_fork_marks_each_item_with_its_declaration`
/// - witness: `pool::recording::tests::a_recorded_join_marks_each_half`
#[derive(Debug)]
pub struct ActivityFork<'fork, Declares>
{
    /// The pool the jobs run on.
    pool: &'fork Pool,
    /// What each mark writes beside its job.
    marks: Marks<'fork>,
    /// The declaration of each item of an `each`, by its place.
    declared: Declares,
}

impl<Declares> Helped for ActivityFork<'_, Declares>
where
    Declares: Sync,
{
    /// The pool that the recording runs its jobs on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn pool(&self) -> &Pool
    {
        self.pool
    }

    /// Run `work` as one job that names no declaration, marked on the ring of
    /// the calling thread.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn job<Out>(
        &self,
        work: impl FnOnce() -> Out,
    ) -> Out
    {
        self.marks.around(Declared::NONE, work)
    }
}

impl<Declares> Fork for ActivityFork<'_, Declares>
where
    Declares: Fn(ItemIndex) -> Declared + Sync,
{
    /// Run `job` on every item as the pool runs it, each between a start mark
    /// and an end mark that name the item's declaration.
    ///
    /// # Specification
    /// - ensures: `job` runs once per item, as [`Pool`]'s `each` runs it; each
    ///   run is marked once on the ring of its thread.
    /// - panics: a job's panic, at the end of the fork.
    /// - executable: none — the schedule is the pool's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Pool::recording`].
    /// - witness: `pool::recording::tests::a_recorded_fork_marks_each_item_with_its_declaration`
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
        let (marks, declared) = (self.marks, &self.declared);
        let marked = |state: &mut State, index: ItemIndex, item: &mut Item| {
            marks.around(declared(index), || job(state, item));
        };
        let forked = if items.len() <= 1 {
            Ok(Forked::Serial)
        }
        else {
            self.pool.forked()
        };
        match forked {
            Ok(Forked::Pooled(threads, Pooled(workers))) => {
                let (start, marked) = (&start, &marked);
                threads.install(move || each_indexed(workers, items, start, marked));
            },
            Ok(Forked::Serial) | Err(_) => each_indexed(Threads::ONE, items, start, marked),
        }
    }

    /// Run both halves as the pool runs them, each between a start mark and
    /// an end mark that name no declaration.
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
        let marks = self.marks;
        self.pool.join(
            move || marks.around(Declared::NONE, left),
            move || marks.around(Declared::NONE, right),
        )
    }

    /// Run `body` in the pool's scope, as one job between a start mark and an
    /// end mark on the thread that runs it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn scope<'scope, Body>(
        &self,
        body: Body,
    ) -> Body::Output
    where
        Body: Scoped<'scope> + Send,
        Body::Output: Send,
    {
        self.pool.scope(Marked {
            body,
            marks: self.marks,
        })
    }
}

/// A scope's body, run between a start mark and an end mark.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Marked<'fork, Body>
{
    /// The body.
    body: Body,
    /// What each mark writes beside the body.
    marks: Marks<'fork>,
}

impl<'scope, Body> Scoped<'scope> for Marked<'_, Body>
where
    Body: Scoped<'scope>,
{
    type Output = Body::Output;

    /// Run the body under `spawner`, marked.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run<Spawner>(
        self,
        spawner: &Spawner,
    ) -> Self::Output
    where
        Spawner: Spawn<'scope>,
    {
        let Self { body, marks } = self;
        marks.around(Declared::NONE, || body.run(spawner))
    }
}

#[cfg(test)]
mod tests;
