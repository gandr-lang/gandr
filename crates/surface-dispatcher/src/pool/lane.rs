//! The lanes of the pool's dependence schedule: for each task beside the
//! calling thread, one ring of jobs to the task and one ring of results back.
//!
//! **One producer and one consumer for each ring.** The calling thread alone
//! pushes a lane's jobs and pops its results. The party that holds the lane's
//! claim alone pops its jobs and pushes its results. So a hand-off is one write
//! into a slot and one release store of the ring's index: no hand-off takes a
//! lock. The rings are `rtrb`'s wait-free rings of one producer and one
//! consumer.
//!
//! **A claim, never a wait.** A lane's task holds the lane's claim while it
//! runs the lane's jobs. The calling thread takes the claim of a lane that no
//! task holds, and runs a job of that lane itself. Each party tries a claim
//! once and does other work when the other party holds it, so no party waits
//! for a claim.
//!
//! **A task spins, then leaves.** A task that finds its ring empty polls up to
//! its spin budget. Then it gives the claim back, clears the lane's attendance
//! and ends. Its worker goes back to the pool, and the pool parks the worker.
//! The calling thread starts a task again for a lane that it hands a job while
//! no task attends the lane. A sequentially consistent fence on each side
//! orders the write of the job before the read of the attendance, and the
//! clear of the attendance before the read of the ring. So at least one of the
//! two parties sees the write of the other, and no job waits for a task that
//! does not come.
//!
//! A task never parks inside a job of the pool. A parked task holds its
//! worker. A fork inside another job can then wait for that worker forever:
//! the fork's share runs on no thread, the job that waits on it never returns,
//! and the schedule never ends.
//!
//! **The calling thread spins, then parks.** It polls up to the spin budget,
//! then sets its flag and parks. A task that hands a result back unparks it
//! only when it reads the flag set, under the same two fences. The calling
//! thread holds no worker that a fork of its jobs waits on, so its park stops
//! no other party.
//!
//! # References
//!
//! - `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — anchor: the plan of the
//!   single writer gives each worker one ring in and one ring out, and a
//!   consumer that spins, then parks, against a flag that its producer reads.
//! - `vault:01a12791-4fa7-7d23-852e-a50c09a02144` — dependency: §
//!   admission-strategies-findings, the hand-off spike: rings with batch
//!   publication against each parking transport.

use core::cell::UnsafeCell;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;
use core::sync::atomic::fence;
use std::thread::Thread;

/// The most jobs that a lane holds: the job that its task runs and seven
/// behind it. The jobs behind it keep the task busy while the calling thread
/// wakes and commits, and that can take longer than a short job. A shallower
/// lane drains, so its task leaves and starts again for each job. A deeper
/// lane keeps more jobs behind a long one, where no other party can take them.
pub const DEPTH: usize = 8;

/// Whether the calling thread of a schedule parks.
///
/// # Specification
/// - provides: the answer of [`Sleeper::rest`].
/// - panics: none.
/// - executable: none — a type-level block; [`super::Pooled`]'s `schedule`
///   carries the obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rest
{
    /// The calling thread runs or polls.
    Awake,
    /// The calling thread parks, or is about to park, until a wake.
    Parked,
}

/// Whether a task attends a lane: it runs the lane's jobs, or the pool holds
/// it and starts it later.
///
/// # Specification
/// - provides: the answers of [`Lane::attendance`] and [`Lane::attend`].
/// - panics: none.
/// - executable: none — a type-level block; [`super::Pooled`]'s `schedule`
///   carries the obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Attendance
{
    /// A task attends the lane.
    Attended,
    /// No task attends the lane.
    Unattended,
}

/// Whether a party runs the jobs that wait in a lane.
///
/// # Specification
/// - provides: the answer of [`Lane::tending`].
/// - panics: none.
/// - executable: none — a type-level block; [`super::Pooled`]'s `schedule`
///   carries the obligations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Tending
{
    /// No job waits in the lane's ring, or a party holds the lane's claim.
    Tended,
    /// A job waits in the lane's ring, and no party holds the lane's claim.
    Stranded,
}

/// The calling thread of a schedule, which parks while it waits for a
/// result: its thread, and whether it parks now.
///
/// # Specification
/// - provides: the flag that the calling thread sets before it parks, and the
///   wake that clears the flag and unparks the thread.
/// - panics: none.
/// - executable: none — a type-level block; [`super::Pooled`]'s `schedule`
///   carries the obligations.
pub struct Sleeper
{
    /// The thread that parks, which a wake unparks.
    thread: Thread,
    /// Set while the thread parks, or from just before it parks.
    sleeping: AtomicBool,
}

impl Sleeper
{
    /// A sleeper whose thread is `thread`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn of(thread: Thread) -> Self
    {
        Self {
            thread,
            sleeping: AtomicBool::new(false),
        }
    }

    /// Park the calling thread until a wake, unless `ready` answers `true`
    /// once the flag is set.
    ///
    /// # Specification
    /// - requires: the calling thread is the sleeper's thread.
    /// - ensures: returns once `ready` answers `true` after the flag is set, or
    ///   once a wake clears the flag. A party that writes work and then reads
    ///   the flag through [`Sleeper::wake`] either sees the flag set and wakes
    ///   this one, or `ready` sees the work.
    /// - panics: a panic of `ready`.
    /// - executable: none — the answer is a later party's wake, which no
    ///   postcondition of this call reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a schedule at each spin budget, whose calling thread
    ///   parks while it waits, ends with each job committed.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
    #[inline]
    pub fn sleep<Ready>(
        &self,
        ready: Ready,
    ) where
        Ready: FnOnce() -> bool,
    {
        self.sleeping.store(true, Ordering::Release);
        fence(Ordering::SeqCst);
        if ready() {
            self.sleeping.store(false, Ordering::Relaxed);
            return;
        }
        // A park may return with no unpark, so the flag, which only a wake
        // clears, ends the wait.
        while self.sleeping.load(Ordering::Acquire) {
            std::thread::park();
        }
    }

    /// Whether the thread parks now, read after each write of the calling
    /// party.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn rest(&self) -> Rest
    {
        fence(Ordering::SeqCst);
        if self.sleeping.load(Ordering::Relaxed) {
            Rest::Parked
        }
        else {
            Rest::Awake
        }
    }

    /// Wake the thread if it parks, after each write of the calling party.
    ///
    /// # Specification
    /// - ensures: when the flag reads set after the fence, exactly one wake
    ///   clears it and unparks the thread.
    /// - panics: none.
    /// - executable: none — the parked thread reads the cleared flag, which no
    ///   postcondition of this call reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Sleeper::sleep`].
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
    #[inline]
    pub fn wake(&self)
    {
        if self.rest() == Rest::Parked && self.sleeping.swap(false, Ordering::AcqRel) {
            self.thread.unpark();
        }
    }
}

/// The ends of a lane that the holder of its claim uses: the ring that it
/// takes jobs from, and the ring that it hands results back on. They sit on
/// cache lines of their own, apart from the lines that the calling thread
/// reads.
///
/// # Specification
/// trivial.
#[repr(align(128))]
pub struct Runner<Job, Out>
{
    /// The jobs that the calling thread hands to the lane.
    pub jobs: rtrb::Consumer<Job>,
    /// The results that go back to the calling thread.
    pub results: rtrb::Producer<Out>,
}

/// The ends of a lane that the calling thread holds, and the count of the
/// lane's jobs that are not committed.
///
/// # Specification
/// - provides: the producer of the lane's jobs and the consumer of its results.
///   The calling thread hands a lane a job only while the lane holds fewer jobs
///   than its rings have slots, so no push into either ring is refused.
/// - panics: none.
/// - executable: none — a type-level block; [`super::Pooled`]'s `schedule`
///   carries the obligations.
pub struct Feed<Job, Out>
{
    /// The jobs for the lane.
    pub jobs: rtrb::Producer<Job>,
    /// The results of the lane's jobs.
    pub results: rtrb::Consumer<Out>,
    /// The jobs handed to the lane and not committed: those in the ring of
    /// jobs, the one that runs, and those in the ring of results.
    pub held: usize,
}

/// What the parties of a lane share: the claim and the attendance of a task,
/// and the ends that the holder of the claim uses.
///
/// # Specification
/// - provides: at most one holder of the claim at a time, and the runner's ends
///   only to that holder.
/// - panics: none.
/// - executable: none — a type-level block; [`super::Pooled`]'s `schedule`
///   carries the obligations.
pub struct Lane<Job, Out>
{
    /// The claim and the attendance, which both parties read.
    control: Control,
    /// The ends that the holder of the claim uses.
    runner: UnsafeCell<Runner<Job, Out>>,
}

/// The claim of a lane and its attendance, on cache lines of their own, so
/// that a write to them never moves a line of the runner's ends.
///
/// # Specification
/// trivial.
#[repr(align(128))]
struct Control
{
    /// Set while a party holds the claim.
    claimed: AtomicBool,
    /// Set while a task attends the lane.
    attended: AtomicBool,
}

/// Only the holder of a lane's claim reaches the runner's ends.
///
/// # Safety
/// - unsafe invariants: the claim's acquire on its take and its release on its
///   return order the uses of successive holders, so the runner's ends move
///   between threads as a `Send` value moves.
// SAFETY: only the holder of the claim reaches the runner. The claim's
// acquire on its take and its release on its return order the uses of
// successive holders, so the runner's ends move between threads as a `Send`
// value moves.
unsafe impl<Job, Out> Sync for Lane<Job, Out>
where
    Job: Send,
    Out: Send,
{
}

/// A lane whose rings each hold [`DEPTH`] values, attended by the task that
/// the schedule starts for it, and the calling thread's ends of it.
///
/// # Specification
/// - ensures: the rings are empty, the claim is free, the lane is attended, and
///   the feed holds no job.
/// - panics: none.
/// - executable: none — the rings' state is `rtrb`'s, which no postcondition
///   reads apart from the count of held jobs.
///
/// # Adequacy
/// - hypothesis: L3 — as [`super::Pooled`]'s `schedule`.
/// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
#[inline]
#[must_use]
pub fn open<Job, Out>() -> (Lane<Job, Out>, Feed<Job, Out>)
{
    let (handed, taken) = rtrb::RingBuffer::new(DEPTH);
    let (returned, committed) = rtrb::RingBuffer::new(DEPTH);
    (
        Lane {
            control: Control {
                claimed: AtomicBool::new(false),
                attended: AtomicBool::new(true),
            },
            runner: UnsafeCell::new(Runner {
                jobs: taken,
                results: returned,
            }),
        },
        Feed {
            jobs: handed,
            results: committed,
            held: 0,
        },
    )
}

impl<Job, Out> Lane<Job, Out>
{
    /// Take the lane's claim, unless another party holds it.
    ///
    /// # Specification
    /// - ensures: a claim exactly when no party held it; the claim returns when
    ///   the answer drops.
    /// - panics: none.
    /// - executable: none — another party may take the claim as soon as this
    ///   one returns it, so no postcondition reads the flag.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a schedule whose calling thread runs the jobs of a
    ///   lane whose task never starts, and one whose tasks run each job.
    /// - witness: `pool::tests::a_schedule_inside_a_scheduled_job_ends`
    /// - witness: `pool::tests::a_job_that_returns_first_commits_first`
    /// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
    #[inline]
    #[must_use]
    pub fn claim(&self) -> Option<Claim<'_, Job, Out>>
    {
        // The claim is built only on a won exchange: a claim built and then
        // dropped on a lost one would return the claim that another party
        // holds.
        match self.control.claimed.compare_exchange(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed,
        ) {
            Ok(_) => Some(Claim(self)),
            Err(_) => None,
        }
    }

    /// Whether a job waits in the lane's ring with no party to run it now,
    /// read from the calling thread's `feed` of the lane.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tending(
        &self,
        feed: &Feed<Job, Out>,
    ) -> Tending
    {
        if feed.jobs.slots() < feed.jobs.buffer().capacity()
            && !self.control.claimed.load(Ordering::Relaxed)
        {
            Tending::Stranded
        }
        else {
            Tending::Tended
        }
    }

    /// Whether a task attends the lane now, read after each write of the
    /// calling party.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn attendance(&self) -> Attendance
    {
        fence(Ordering::SeqCst);
        if self.control.attended.load(Ordering::Relaxed) {
            Attendance::Attended
        }
        else {
            Attendance::Unattended
        }
    }

    /// Attend the lane, unless a task attends it already, and answer the
    /// attendance that the call found.
    ///
    /// # Specification
    /// - ensures: [`Attendance::Unattended`] exactly when the call set the
    ///   attendance, so the calling party now attends the lane; of two parties
    ///   that attend an unattended lane at once, one alone sets it.
    /// - panics: none.
    /// - executable: none — the task that attends may leave as soon as the call
    ///   returns, so no postcondition reads the flag.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a schedule whose tasks leave their empty lanes and
    ///   start again when the calling thread hands them jobs ends with each job
    ///   committed once.
    /// - witness: `pool::tests::a_schedule_releases_in_order_and_commits_each_job_as_it_returns`
    /// - witness: `pool::tests::a_schedule_whose_jobs_fork_again_ends`
    #[inline]
    #[must_use]
    pub fn attend(&self) -> Attendance
    {
        match self.control.attended.compare_exchange(
            false,
            true,
            Ordering::AcqRel,
            Ordering::Relaxed,
        ) {
            Ok(_) => Attendance::Unattended,
            Err(_) => Attendance::Attended,
        }
    }

    /// Clear the lane's attendance, before each later read of the task that
    /// leaves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn leave(&self)
    {
        self.control.attended.store(false, Ordering::Release);
        fence(Ordering::SeqCst);
    }
}

/// A held claim of a lane, which returns when it drops.
///
/// # Specification
/// trivial.
#[repr(transparent)]
pub struct Claim<'lane, Job, Out>(&'lane Lane<Job, Out>);

impl<Job, Out> Claim<'_, Job, Out>
{
    /// The lane's ends for the holder of its claim.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn runner(&mut self) -> &mut Runner<Job, Out>
    {
        // SAFETY: this claim took the flag from free to set, and only its
        // drop sets it free again, so no other party reaches the runner while
        // the borrow lives.
        unsafe { &mut *self.0.runner.get() }
    }
}

impl<Job, Out> Drop for Claim<'_, Job, Out>
{
    /// Return the claim.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        self.0.control.claimed.store(false, Ordering::Release);
    }
}
